"""
HPKE Benchmark Runner

This script runs cargo benchmarks for HPKE (Hybrid Public Key Encryption) implementations
comparing performance between Rust and Owl implementations in different configurations.

The benchmarks test four different sender/receiver combinations:
- rs -> rs: Rust sender to Rust receiver (baseline)
- owl -> rs: Owl sender to Rust receiver  
- rs -> owl: Rust sender to Owl receiver
- owl -> owl: Owl sender to Owl receiver

Results are displayed in a matrix format showing runs/sec and relative slowdown percentages.
"""

import json
import subprocess
import threading
import time
import sys
import os
import csv
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from prettytable import PrettyTable


# Configuration constants
BASELINE = "rs -> rs"
BASELINE_PAT = "bench_rust_rust"
OWL_TO_RUST = "owl -> rs"
OWL_TO_RUST_PAT = "bench_owl_rust"
RUST_TO_OWL = "rs -> owl"
RUST_TO_OWL_PAT = "bench_rust_owl"
OWL_TO_OWL = "owl -> owl"
OWL_TO_OWL_PAT = "bench_owl_owl"

# Cargo bench command configuration
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = ""
BENCH_ARGS = "--format=json -Z unstable-options"
HIDE_STDERR = "2> /dev/null"
UNVERIF_CRYPTO_ARGS = "--features=nonverif-crypto"

# Benchmark directory
BENCHMARK_DIR = "full_protocol_case_studies/implementations/hpke/test_bench_hpke"

# Benchmark patterns for processing
BENCHMARK_PATTERNS = [
    (BASELINE, BASELINE_PAT),
    (OWL_TO_RUST, OWL_TO_RUST_PAT),
    (RUST_TO_OWL, RUST_TO_OWL_PAT),
    (OWL_TO_OWL, OWL_TO_OWL_PAT),
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
    Execute cargo bench command and parse JSON output with progress indicator.
    
    Args:
        command: The complete shell command to execute
        
    Returns:
        List of parsed JSON objects, or None if execution failed
    """
    # Animation state
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
    
    try:
        # print(f"Running: {command}")
        
        # Start animation in separate thread
        animation_thread = threading.Thread(target=animate)
        animation_thread.daemon = True
        animation_thread.start()
        
        output = subprocess.check_output(
            command, 
            shell=True, 
            text=True,
            cwd=BENCHMARK_DIR
        )
        
        # Stop animation and clear line
        animation_active = False
        sys.stdout.write('\r' + ' ' * 30 + '\r')  # Clear the animation line
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
        animation_active = False
        sys.stdout.write('\r' + ' ' * 30 + '\r')
        sys.stdout.flush()
        print(f"Error executing cargo bench: {e}")
        print(f"Return code: {e.returncode}")
        return None
    except Exception as e:
        animation_active = False
        sys.stdout.write('\r' + ' ' * 30 + '\r')
        sys.stdout.flush()
        print(f"Unexpected error: {e}")
        return None


def process_benchmark_output(obj_list: List[Dict]) -> Dict[str, Dict]:
    """
    Process raw cargo bench output into structured benchmark results.
    
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
    
    for display_name, pattern in BENCHMARK_PATTERNS:
        # Find matching benchmark result
        matching_results = [
            result for result in bench_results 
            if pattern in result.get('name', '')
        ]
        
        if len(matching_results) == 0:
            print(f"Warning: No results found for pattern '{pattern}'")
            continue
        elif len(matching_results) > 1:
            print(f"Warning: Multiple results found for pattern '{pattern}', using first")
        
        result = matching_results[0]
        structured_results[display_name] = {
            'median': result.get('median', 0),
            'deviation': result.get('deviation', 0),
        }
    
    return structured_results


def calculate_metrics(data: Dict[str, Dict]) -> Dict[str, Dict]:
    """
    Calculate additional metrics like runs/sec and relative slowdowns.
    
    Args:
        data: Raw benchmark data with median and deviation
        
    Returns:
        Enhanced data with calculated metrics
    """
    enhanced_data = {}
    
    for name, values in data.items():
        median_ns = values['median']
        deviation_ns = values['deviation']
        
        # Calculate runs per second (convert from ns/iter to runs/sec)
        runs_per_sec = 1e9 / median_ns if median_ns > 0 else 0
        
        # Calculate deviation for runs/sec using error propagation
        if median_ns > 0 and deviation_ns > 0:
            # Using approximation: if f(x) = 1/x, then σ_f ≈ σ_x / x²
            runs_per_sec_dev = (deviation_ns * 1e9) / (median_ns ** 2)
        else:
            runs_per_sec_dev = 0
        
        enhanced_data[name] = {
            'median_ns': median_ns,
            'deviation_ns': deviation_ns,
            'runs_per_sec': runs_per_sec,
            'runs_per_sec_dev': runs_per_sec_dev,
        }
    
    # Calculate relative slowdowns compared to baseline
    baseline_data = enhanced_data.get(BASELINE)
    if baseline_data and baseline_data['runs_per_sec'] > 0:
        baseline_rps = baseline_data['runs_per_sec']
        
        for name, values in enhanced_data.items():
            if name == BASELINE:
                values['slowdown_pct'] = 0.0  # Baseline has no slowdown
            else:
                # Calculate percentage change: (current - baseline) / baseline * 100
                current_rps = values['runs_per_sec']
                if current_rps > 0:
                    values['slowdown_pct'] = ((current_rps - baseline_rps) / baseline_rps) * 100
                else:
                    values['slowdown_pct'] = -100.0  # Complete slowdown
    
    return enhanced_data


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
    runs_per_sec = values['runs_per_sec']
    slowdown_pct = values['slowdown_pct']
    
    if name == BASELINE:
        return f"{runs_per_sec:,.0f} (---)"
    else:
        return f"{runs_per_sec:,.0f} ({slowdown_pct:+.1f}%)"


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
        return "rust-hpke"
    elif impl_type == "owl":
        return "OwlC_V" if is_verified else "OwlC_B"
    else:
        return impl_type  # fallback


def display_matrix_results(data: Dict[str, Dict], is_verified: bool = True):
    """
    Display benchmark results in a 2x2 matrix format.
    Each column represents the same sender, each row represents the same receiver.
    
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
    table.field_names = ["", f"Sender: {rust_name}", f"Sender: {owl_name}"]
    
    # Add data rows with receiver labels
    table.add_row([
        f"Receiver: {rust_name}",
        format_matrix_cell(BASELINE, enhanced_data),      # rs -> rs
        format_matrix_cell(OWL_TO_RUST, enhanced_data)    # owl -> rs
    ])
    
    table.add_row([
        f"Receiver: {owl_name}",
        format_matrix_cell(RUST_TO_OWL, enhanced_data),   # rs -> owl
        format_matrix_cell(OWL_TO_OWL, enhanced_data)     # owl -> owl
    ])
    
    # Customize alignment
    table.align = "c"
    table.align[""] = "l"  # Left align the receiver labels
    
    print("Performance Matrix (runs/sec with relative performance %)")
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
                'crypto_type', 'configuration', 'sender', 'receiver', 
                'median_ns', 'deviation_ns', 'runs_per_sec', 'performance_change_pct'
            ])
            
            # Helper function to write data for one benchmark suite
            def write_suite_data(results: Dict, crypto_type: str):
                if not results:
                    return
                    
                enhanced_data = calculate_metrics(results)
                
                for config_name, values in enhanced_data.items():
                    # Parse sender and receiver from config name
                    if config_name == BASELINE:
                        sender, receiver = "rust", "rust"
                    elif config_name == OWL_TO_RUST:
                        sender, receiver = "owl", "rust"
                    elif config_name == RUST_TO_OWL:
                        sender, receiver = "rust", "owl"
                    elif config_name == OWL_TO_OWL:
                        sender, receiver = "owl", "owl"
                    else:
                        sender, receiver = "unknown", "unknown"
                    
                    performance_pct = values['slowdown_pct'] if values['slowdown_pct'] != 0.0 else 0.0
                    
                    writer.writerow([
                        crypto_type,
                        config_name,
                        sender,
                        receiver,
                        values['median_ns'],
                        values['deviation_ns'],
                        values['runs_per_sec'],
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
            txtfile.write("HPKE Benchmark Results\n")
            txtfile.write("=" * 60 + "\n\n")
            
            txtfile.write("Benchmarks with verified crypto:\n")
            txtfile.write("-" * 40 + "\n")
            
            if verif_results:
                # Capture matrix table
                enhanced_data = calculate_metrics(verif_results)
                rust_name = get_implementation_name("rust", True)
                owl_name = get_implementation_name("owl", True)
                
                table = PrettyTable()
                table.field_names = ["", f"Sender: {rust_name}", f"Sender: {owl_name}"]
                
                table.add_row([
                    f"Receiver: {rust_name}",
                    format_matrix_cell(BASELINE, enhanced_data),
                    format_matrix_cell(OWL_TO_RUST, enhanced_data)
                ])
                table.add_row([
                    f"Receiver: {owl_name}",
                    format_matrix_cell(RUST_TO_OWL, enhanced_data),
                    format_matrix_cell(OWL_TO_OWL, enhanced_data)
                ])
                
                table.align = "c"
                table.align[""] = "l"
                
                txtfile.write("Performance Matrix (runs/sec with relative performance %)\n")
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
                table.field_names = ["", f"Sender: {rust_name}", f"Sender: {owl_name}"]
                
                table.add_row([
                    f"Receiver: {rust_name}",
                    format_matrix_cell(BASELINE, enhanced_data),
                    format_matrix_cell(OWL_TO_RUST, enhanced_data)
                ])
                table.add_row([
                    f"Receiver: {owl_name}",
                    format_matrix_cell(RUST_TO_OWL, enhanced_data),
                    format_matrix_cell(OWL_TO_OWL, enhanced_data)
                ])
                
                table.align = "c"
                table.align[""] = "l"
                
                txtfile.write("Performance Matrix (runs/sec with relative performance %)\n")
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
    print("HPKE Benchmark Suite")
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
    save_raw_data_to_csv(verif_results, unverif_results, "experiment2.csv")
    save_formatted_tables_to_txt(verif_results, unverif_results, "experiment2.txt")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nBenchmark interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"\nUnexpected error: {e}")
        sys.exit(1)