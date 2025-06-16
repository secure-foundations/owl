"""
WireGuard Handshake Benchmark Runner

This script runs cargo benchmarks for WireGuard handshake implementations
comparing performance between Rust and Owl implementations in different configurations.

The benchmarks test four different initiator/responder combinations:
- rs -> rs: Rust initiator to Rust responder (baseline)
- owl -> rs: Owl initiator to Rust responder  
- rs -> owl: Rust initiator to Owl responder
- owl -> owl: Owl initiator to Owl responder

Results are displayed in a matrix format showing handshakes/sec and relative performance percentages.
"""

import json
import subprocess
import sys
import os
import csv
import time
import threading
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from prettytable import PrettyTable


# Configuration constants
BASELINE = "rs -> rs"
BASELINE_PAT = "bench_h_1_rs_handshake"
BASELINE_INIT_PAT = "bench_h_1_rs_handshake_init"
OWL_TO_RUST = "owl -> rs"
OWL_TO_RUST_PAT = "bench_h_2_owl_init_rs_resp_handshake"
OWL_TO_RUST_INIT_PAT = "bench_h_2_owl_init_rs_resp_handshake_init"
RUST_TO_OWL = "rs -> owl"
RUST_TO_OWL_PAT = "bench_h_3_rs_init_owl_resp_handshake"
RUST_TO_OWL_INIT_PAT = "bench_h_3_rs_init_owl_resp_handshake_init"
OWL_TO_OWL = "owl -> owl"
OWL_TO_OWL_PAT = "bench_h_4_owl_handshake"
OWL_TO_OWL_INIT_PAT = "bench_h_4_owl_handshake_init"

# Cargo bench command configuration
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = "bench_h"
BENCH_ARGS = "--format=json -Z unstable-options"
HIDE_STDERR = "2> /dev/null"
UNVERIF_CRYPTO_ARGS = "--features=nonverif-crypto"

# Benchmark directory
BENCHMARK_DIR = "full_protocol_case_studies/implementations/wireguard/wireguard-rs"

# Benchmark patterns for processing
BENCHMARK_PATTERNS = [
    (BASELINE, BASELINE_PAT, BASELINE_INIT_PAT),
    (OWL_TO_RUST, OWL_TO_RUST_PAT, OWL_TO_RUST_INIT_PAT),
    (RUST_TO_OWL, RUST_TO_OWL_PAT, RUST_TO_OWL_INIT_PAT),
    (OWL_TO_OWL, OWL_TO_OWL_PAT, OWL_TO_OWL_INIT_PAT),
]


def validate_benchmark_directory():
    """
    Check if the benchmark directory exists and contains a valid Rust project.
    
    Exits the program with an error message if validation fails.
    """
    benchmark_path = Path(BENCHMARK_DIR)
    
    if not benchmark_path.exists():
        print(f"Error: Benchmark directory not found: {benchmark_path}")
        print("Please ensure you're running this script from the correct location.")
        sys.exit(1)
    
    if not (benchmark_path / "Cargo.toml").exists():
        print(f"Error: No Cargo.toml found in {benchmark_path}")
        print("This doesn't appear to be a valid Rust project directory.")
        sys.exit(1)
    
    print(f"Using benchmark directory: {benchmark_path.resolve()}")


def build_cargo_command(base_args: str) -> str:
    """
    Build the complete cargo bench command string.
    
    Args:
        base_args: Additional arguments for cargo bench command
        
    Returns:
        Complete command string ready for execution
    """
    return " ".join([
        BASE_COMMAND,
        base_args,
        "--",
        BENCH_PATTERN,
        BENCH_ARGS,
        HIDE_STDERR
    ])


def run_cargo_bench(command: str) -> Optional[List[Dict]]:
    """
    Execute cargo bench command and parse JSON output.
    
    Args:
        command: The complete shell command to execute
        
    Returns:
        List of parsed JSON objects, or None if execution failed
    """
    try:
        print(f"Running: {command}")
        
        # Set up animation
        animation_active = True
        
        def animate():
            bar_length = 20
            i = 0
            while animation_active:
                filled = i % (bar_length + 1)
                bar = '█' * filled + '░' * (bar_length - filled)
                sys.stdout.write(f'\r[{bar}] Running...')
                sys.stdout.flush()
                time.sleep(0.1)
                i += 1
        
        # Start animation in a separate thread
        animation_thread = threading.Thread(target=animate)
        animation_thread.daemon = True
        animation_thread.start()
        
        # Run the cargo bench command
        output = subprocess.check_output(
            command, 
            shell=True, 
            text=True,
            cwd=BENCHMARK_DIR
        )
        
        # Stop animation and clear the line
        animation_active = False
        time.sleep(0.2)  # Give animation thread time to stop
        sys.stdout.write('\r' + ' ' * 50 + '\r')  # Clear the animation line
        sys.stdout.flush()
        
        # Parse each line as JSON (cargo bench outputs one JSON object per line)
        parsed_output = []
        for line in output.strip().split('\n'):
            if line.strip():  # Skip empty lines
                try:
                    parsed_output.append(json.loads(line))
                except json.JSONDecodeError as e:
                    print(f"Warning: Failed to parse JSON line: {line[:100]}...")
                    continue
        
        return parsed_output
        
    except subprocess.CalledProcessError as e:
        # Stop animation on error
        animation_active = False
        time.sleep(0.2)
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        
        print(f"Error executing cargo bench: {e}")
        print(f"Return code: {e.returncode}")
        return None
    except Exception as e:
        # Stop animation on error
        animation_active = False
        time.sleep(0.2)
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        
        print(f"Unexpected error: {e}")
        return None


def process_benchmark_output(obj_list: List[Dict]) -> Dict[str, Dict]:
    """
    Process raw cargo bench output into structured benchmark results.
    
    WireGuard benchmarks include both handshake and init measurements.
    We calculate the actual handshake time by subtracting init time.
    
    Args:
        obj_list: List of JSON objects from cargo bench
        
    Returns:
        Dictionary mapping benchmark names to their results
    """
    # Filter for actual benchmark results
    bench_results = [obj for obj in obj_list if obj.get('type') == 'bench']
    
    if not bench_results:
        print("Warning: No benchmark results found in output")
        return {}
    
    structured_results = {}
    
    for display_name, handshake_pattern, init_pattern in BENCHMARK_PATTERNS:
        # Find matching benchmark results for both handshake and init
        matching_results = [
            result for result in bench_results 
            if handshake_pattern in result.get('name', '')
        ]
        
        if len(matching_results) != 2:
            print(f"Warning: Expected 2 results for pattern '{handshake_pattern}', found {len(matching_results)}")
            continue
        
        # Identify which is init and which is handshake
        init_result = None
        handshake_result = None
        
        for result in matching_results:
            if init_pattern in result.get('name', ''):
                init_result = result
            else:
                handshake_result = result
        
        if not init_result or not handshake_result:
            print(f"Warning: Could not find both init and handshake results for '{display_name}'")
            continue
        
        structured_results[display_name] = {
            'handshake_median': handshake_result.get('median', 0),
            'handshake_deviation': handshake_result.get('deviation', 0),
            'init_median': init_result.get('median', 0),
            'init_deviation': init_result.get('deviation', 0),
        }
    
    return structured_results


def calculate_metrics(data: Dict[str, Dict]) -> Dict[str, Dict]:
    """
    Calculate additional metrics like handshakes/sec and relative performance.
    
    Args:
        data: Raw benchmark data with handshake and init measurements
        
    Returns:
        Enhanced data with calculated metrics
    """
    enhanced_data = {}
    
    for name, values in data.items():
        handshake_median = values['handshake_median']
        handshake_deviation = values['handshake_deviation']
        init_median = values['init_median']
        init_deviation = values['init_deviation']
        
        # Calculate net handshake time (handshake - init setup)
        net_handshake_ns = handshake_median - init_median
        net_handshake_deviation = handshake_deviation + init_deviation
        
        # Calculate handshakes per second (convert from ns to handshakes/sec)
        handshakes_per_sec = 1e9 / net_handshake_ns if net_handshake_ns > 0 else 0
        
        # Calculate deviation for handshakes/sec using error propagation
        if net_handshake_ns > 0 and net_handshake_deviation > 0:
            # Using approximation: if f(x) = 1/x, then σ_f ≈ σ_x / x²
            handshakes_per_sec_dev = (net_handshake_deviation * 1e9) / (net_handshake_ns ** 2)
        else:
            handshakes_per_sec_dev = 0
        
        enhanced_data[name] = {
            'handshake_median': handshake_median,
            'handshake_deviation': handshake_deviation,
            'init_median': init_median,
            'init_deviation': init_deviation,
            'net_handshake_ns': net_handshake_ns,
            'net_handshake_deviation': net_handshake_deviation,
            'handshakes_per_sec': handshakes_per_sec,
            'handshakes_per_sec_dev': handshakes_per_sec_dev,
        }
    
    # Calculate relative performance compared to baseline
    baseline_data = enhanced_data.get(BASELINE)
    if baseline_data and baseline_data['handshakes_per_sec'] > 0:
        baseline_hps = baseline_data['handshakes_per_sec']
        
        for name, values in enhanced_data.items():
            if name == BASELINE:
                values['performance_pct'] = 0.0  # Baseline has no change
            else:
                # Calculate percentage change: (current - baseline) / baseline * 100
                current_hps = values['handshakes_per_sec']
                if current_hps > 0:
                    values['performance_pct'] = ((current_hps - baseline_hps) / baseline_hps) * 100
                else:
                    values['performance_pct'] = -100.0  # Complete performance loss
    
    return enhanced_data


def get_implementation_name(impl_type: str, is_verified: bool) -> str:
    """
    Get the display name for an implementation based on type and crypto verification.
    
    Args:
        impl_type: Either "rust" or "owl"
        is_verified: True for verified crypto, False for unverified crypto
        
    Returns:
        Formatted implementation name
    """
    if impl_type == "rust":
        return "wireguard-rs"
    elif impl_type == "owl":
        return "OwlC_V" if is_verified else "OwlC_B"
    else:
        return impl_type  # fallback


def format_matrix_cell(name: str, enhanced_data: Dict[str, Dict]) -> str:
    """
    Format a single cell in the performance matrix.
    
    Args:
        name: Benchmark configuration name
        enhanced_data: Calculated benchmark metrics
        
    Returns:
        Formatted string for matrix cell
    """
    if name not in enhanced_data:
        return "N/A"
    
    values = enhanced_data[name]
    handshakes_per_sec = values['handshakes_per_sec']
    performance_pct = values['performance_pct']
    
    if name == BASELINE:
        return f"{handshakes_per_sec:,.0f} (---)"
    else:
        return f"{handshakes_per_sec:,.0f} ({performance_pct:+.1f}%)"


def display_matrix_results(data: Dict[str, Dict], is_verified: bool = True):
    """
    Display benchmark results in a 2x2 matrix format.
    Each column represents the same initiator, each row represents the same responder.
    
    Args:
        data: Raw benchmark data
        is_verified: True for verified crypto, False for unverified crypto
    """
    if not data:
        print("No benchmark data to display")
        return
    
    enhanced_data = calculate_metrics(data)
    
    # Get implementation names based on crypto type
    rust_name = get_implementation_name("rust", is_verified)
    owl_name = get_implementation_name("owl", is_verified)
    
    # Create the matrix table with clearer headers
    table = PrettyTable()
    table.field_names = ["", f"Initiator: {rust_name}", f"Initiator: {owl_name}"]
    
    # Add data rows with responder labels
    table.add_row([
        f"Responder: {rust_name}",
        format_matrix_cell(BASELINE, enhanced_data),      # rs -> rs
        format_matrix_cell(OWL_TO_RUST, enhanced_data)    # owl -> rs
    ])
    
    table.add_row([
        f"Responder: {owl_name}",
        format_matrix_cell(RUST_TO_OWL, enhanced_data),   # rs -> owl
        format_matrix_cell(OWL_TO_OWL, enhanced_data)     # owl -> owl
    ])
    
    # Customize alignment
    table.align = "c"
    table.align[""] = "l"  # Left align the responder labels
    
    print("Performance Matrix (handshakes/sec with relative performance %)")
    print(table)


def save_raw_data_to_csv(verif_results: Dict, unverif_results: Dict, filename: str):
    """
    Save raw benchmark data to CSV file.
    
    Args:
        verif_results: Benchmark results with verified crypto
        unverif_results: Benchmark results with unverified crypto
        filename: Output CSV filename
    """
    try:
        with open(filename, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            
            # Write header
            writer.writerow([
                'crypto_type', 'configuration', 'initiator', 'responder', 
                'handshake_median_ns', 'handshake_deviation_ns', 'init_median_ns', 'init_deviation_ns',
                'net_handshake_ns', 'net_handshake_deviation_ns', 'handshakes_per_sec', 'performance_change_pct'
            ])
            
            # Helper function to write data for one benchmark suite
            def write_suite_data(results: Dict, crypto_type: str):
                if not results:
                    return
                    
                enhanced_data = calculate_metrics(results)
                
                for config_name, values in enhanced_data.items():
                    # Parse initiator and responder from config name
                    if config_name == BASELINE:
                        initiator, responder = "rust", "rust"
                    elif config_name == OWL_TO_RUST:
                        initiator, responder = "owl", "rust"
                    elif config_name == RUST_TO_OWL:
                        initiator, responder = "rust", "owl"
                    elif config_name == OWL_TO_OWL:
                        initiator, responder = "owl", "owl"
                    else:
                        initiator, responder = "unknown", "unknown"
                    
                    performance_pct = values['performance_pct'] if values['performance_pct'] != 0.0 else 0.0
                    
                    writer.writerow([
                        crypto_type,
                        config_name,
                        initiator,
                        responder,
                        values['handshake_median'],
                        values['handshake_deviation'],
                        values['init_median'],
                        values['init_deviation'],
                        values['net_handshake_ns'],
                        values['net_handshake_deviation'],
                        values['handshakes_per_sec'],
                        performance_pct
                    ])
            
            # Write verified crypto data
            write_suite_data(verif_results, 'verified')
            
            # Write unverified crypto data
            write_suite_data(unverif_results, 'unverified')
            
        print(f"Raw data saved to {filename}")
        
    except Exception as e:
        print(f"Error saving CSV data: {e}")


def save_formatted_tables_to_txt(verif_results: Dict, unverif_results: Dict, filename: str):
    """
    Save formatted benchmark tables to text file.
    
    Args:
        verif_results: Benchmark results with verified crypto
        unverif_results: Benchmark results with unverified crypto
        filename: Output text filename
    """
    try:
        with open(filename, 'w') as txtfile:
            # Capture the matrix output for verified crypto
            txtfile.write("WireGuard Handshake Benchmark Results\n")
            txtfile.write("=" * 60 + "\n\n")
            
            txtfile.write("Benchmarks with verified crypto:\n")
            txtfile.write("-" * 40 + "\n")
            
            if verif_results:
                # Capture matrix table
                enhanced_data = calculate_metrics(verif_results)
                rust_name = get_implementation_name("rust", True)
                owl_name = get_implementation_name("owl", True)
                
                table = PrettyTable()
                table.field_names = ["", f"Initiator: {rust_name}", f"Initiator: {owl_name}"]
                
                table.add_row([
                    f"Responder: {rust_name}",
                    format_matrix_cell(BASELINE, enhanced_data),
                    format_matrix_cell(OWL_TO_RUST, enhanced_data)
                ])
                table.add_row([
                    f"Responder: {owl_name}",
                    format_matrix_cell(RUST_TO_OWL, enhanced_data),
                    format_matrix_cell(OWL_TO_OWL, enhanced_data)
                ])
                
                table.align = "c"
                table.align[""] = "l"
                
                txtfile.write("Performance Matrix (handshakes/sec with relative performance %)\n")
                txtfile.write(str(table) + "\n")
            else:
                txtfile.write("Failed to run verified crypto benchmarks\n")
            
            txtfile.write("\n" + "=" * 60 + "\n\n")
            
            txtfile.write("Benchmarks with unverified crypto:\n")
            txtfile.write("-" * 40 + "\n")
            
            if unverif_results:
                # Capture matrix table
                enhanced_data = calculate_metrics(unverif_results)
                rust_name = get_implementation_name("rust", False)
                owl_name = get_implementation_name("owl", False)
                
                table = PrettyTable()
                table.field_names = ["", f"Initiator: {rust_name}", f"Initiator: {owl_name}"]
                
                table.add_row([
                    f"Responder: {rust_name}",
                    format_matrix_cell(BASELINE, enhanced_data),
                    format_matrix_cell(OWL_TO_RUST, enhanced_data)
                ])
                table.add_row([
                    f"Responder: {owl_name}",
                    format_matrix_cell(RUST_TO_OWL, enhanced_data),
                    format_matrix_cell(OWL_TO_OWL, enhanced_data)
                ])
                
                table.align = "c"
                table.align[""] = "l"
                
                txtfile.write("Performance Matrix (handshakes/sec with relative performance %)\n")
                txtfile.write(str(table) + "\n")
            else:
                txtfile.write("Failed to run unverified crypto benchmarks\n")
            
            txtfile.write("\n" + "=" * 60 + "\n")
            txtfile.write("Benchmark suite completed\n")
        
        print(f"Formatted tables saved to {filename}")
        
    except Exception as e:
        print(f"Error saving text file: {e}")


def run_benchmark_suite(base_args: str = "") -> Optional[Dict[str, Dict]]:
    """
    Run complete benchmark suite and return processed results.
    
    Args:
        base_args: Additional arguments for cargo bench command
        
    Returns:
        Dictionary of benchmark results, or None if execution failed
    """
    command = build_cargo_command(base_args)
    raw_output = run_cargo_bench(command)
    
    if raw_output is None:
        return None
    
    return process_benchmark_output(raw_output)


def main():
    """Main execution function."""
    validate_benchmark_directory()
    
    print("=" * 60)
    print("WireGuard Handshake Benchmark Suite")
    print("=" * 60)
    
    # Run benchmarks with verified crypto first
    print("\nBenchmarks with verified crypto:")
    print("-" * 40)
    verif_results = run_benchmark_suite("")
    
    if verif_results:
        display_matrix_results(verif_results, is_verified=True)
    else:
        print("Failed to run verified crypto benchmarks")
        verif_results = {}
    
    print("\n" + "=" * 60)
    
    # Run benchmarks with unverified crypto second
    print("\nBenchmarks with unverified crypto:")
    print("-" * 40)
    unverif_results = run_benchmark_suite(UNVERIF_CRYPTO_ARGS)
    
    if unverif_results:
        display_matrix_results(unverif_results, is_verified=False)
    else:
        print("Failed to run unverified crypto benchmarks")
        unverif_results = {}
    
    print("\n" + "=" * 60)
    print("Benchmark suite completed")
    
    # Save results to files
    print("\nSaving results...")
    save_raw_data_to_csv(verif_results, unverif_results, "experiment3.csv")
    save_formatted_tables_to_txt(verif_results, unverif_results, "experiment3.txt")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nBenchmark interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"\nUnexpected error: {e}")
        sys.exit(1)