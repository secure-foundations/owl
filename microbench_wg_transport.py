#!/usr/bin/env python3
"""
WireGuard Transport Layer Benchmark Runner

This script runs cargo benchmarks for WireGuard transport layer implementations
across different packet sizes, comparing performance between baseline Rust
implementation and Owl implementations with verified/unverified crypto.

The benchmarks test packet processing performance across packet sizes from 0 to 1440 bytes.
Results are displayed as a line graph showing performance trends.
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
import matplotlib.pyplot as plt
import numpy as np


# Configuration constants
BASELINE = "setup"
BASELINE_PAT = "bench_send_recv_baseline"
NO_OWL = "baseline"
NO_OWL_PAT = "bench_send_recv_no_owl"
OWL = "owl"
OWL_PAT = "bench_send_recv_owl"

# Cargo bench command configuration
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = "bench_send_recv"
BENCH_ARGS = "--format=json -Z unstable-options"
HIDE_STDERR = "2> /dev/null"
UNVERIF_CRYPTO_ARGS = "--features=nonverif-crypto"

# Benchmark directory and test file
BENCHMARK_DIR = "full_protocol_case_studies/implementations/wireguard/wireguard-rs"
TEST_FILE_PATH = "./src/wireguard/router/tests/tests.rs"

# Packet sizes to test
PACKET_SIZES = [0, 1] + list(range(50, 1440, 50)) + [1440]


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
    
    # Check if test file exists
    test_file = benchmark_path / TEST_FILE_PATH.lstrip('./')
    if not test_file.exists():
        print(f"Error: Test file not found: {test_file}")
        print("Cannot modify packet size configuration.")
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
    Execute cargo bench command and parse JSON output with animation.
    
    Args:
        command: The complete shell command to execute
        
    Returns:
        List of parsed JSON objects, or None if execution failed
    """
    try:
        # Set up animation
        animation_active = True
        
        def animate():
            bar_length = 20
            i = 0
            while animation_active:
                filled = i % (bar_length + 1)
                bar = '█' * filled + '░' * (bar_length - filled)
                sys.stdout.write(f'\r[{bar}] Running benchmark...')
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
        
        # Parse each line as JSON
        parsed_output = []
        for line in output.strip().split('\n'):
            if line.strip():
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
    benchmark_patterns = [(BASELINE, BASELINE_PAT), (NO_OWL, NO_OWL_PAT), (OWL, OWL_PAT)]
    
    for name, pattern in benchmark_patterns:
        matching_results = [
            result for result in bench_results 
            if pattern in result.get('name', '')
        ]
        
        if len(matching_results) != 1:
            print(f"Warning: Expected 1 result for pattern '{pattern}', found {len(matching_results)}")
            continue
        
        result = matching_results[0]
        structured_results[name] = {
            'median': result.get('median', 0),
            'deviation': result.get('deviation', 0)
        }
    
    return structured_results


def calculate_throughput_gbps(packet_size_bytes: int, processing_time_ns: float) -> float:
    """
    Calculate effective throughput in Gbps from packet size and processing time.
    
    Note: Each benchmark iteration processes 1000 packets, so we multiply by 1000
    to get the correct throughput calculation.
    
    Args:
        packet_size_bytes: Size of each packet in bytes
        processing_time_ns: Processing time per iteration (1000 packets) in nanoseconds
        
    Returns:
        Throughput in Gbps (Gigabits per second)
    """
    if processing_time_ns <= 0 or packet_size_bytes <= 0:
        return 0.0
    
    # Each iteration processes 1000 packets
    packets_per_iteration = 1000
    
    # Calculate total bits processed per iteration
    total_bits_per_iteration = packet_size_bytes * 8 * packets_per_iteration
    
    # Convert processing time from ns to seconds
    processing_time_s = processing_time_ns / 1e9
    
    # Calculate throughput: bits per second, then convert to Gbps
    throughput_bps = total_bits_per_iteration / processing_time_s
    throughput_gbps = throughput_bps / 1e9
    
    return throughput_gbps
def calculate_net_performance(data: Dict[str, Dict]) -> Tuple[Optional[float], Optional[float]]:
    """
    Calculate net performance by subtracting setup overhead.
    
    Args:
        data: Raw benchmark data
        
    Returns:
        Tuple of (no_owl_net, owl_net) performance in ns per iteration (1000 packets), or (None, None) if data missing
    """
    if BASELINE not in data or NO_OWL not in data or OWL not in data:
        return (None, None)
    
    baseline_median = data[BASELINE]['median']
    no_owl_net = data[NO_OWL]['median'] - baseline_median
    owl_net = data[OWL]['median'] - baseline_median
    
    return (no_owl_net, owl_net)


def run_single_benchmark(base_args: str) -> Tuple[Optional[float], Optional[float]]:
    """
    Run a single benchmark suite and return net performance results.
    
    Args:
        base_args: Additional arguments for cargo bench command
        
    Returns:
        Tuple of (no_owl_net, owl_net) performance in ns per iteration (1000 packets)
    """
    command = build_cargo_command(base_args)
    parsed_output = run_cargo_bench(command)
    
    if parsed_output is None:
        print("Failed to get parsed output")
        return (None, None)
    
    data = process_benchmark_output(parsed_output)
    return calculate_net_performance(data)


def get_file_contents(filepath: str) -> str:
    """
    Read and return the contents of a file.
    
    Args:
        filepath: Path to the file to read
        
    Returns:
        File contents as string
    """
    with open(filepath, "r") as file:
        return file.read()


def modify_packet_size(packet_size: int, filepath: str) -> bool:
    """
    Modify the test file to use a specific packet size by replacing existing constant.
    
    Args:
        packet_size: Size of packets to configure
        filepath: Path to the test file
        
    Returns:
        True if modification was successful, False otherwise
    """
    try:
        # Read the current file contents
        with open(filepath, "r") as file:
            lines = file.readlines()
        
        # Look for the BYTES_PER_PACKET constant line and replace it
        modified = False
        for i, line in enumerate(lines):
            stripped_line = line.strip()
            # Look for lines that contain the BYTES_PER_PACKET constant
            if (stripped_line.startswith('const BYTES_PER_PACKET') and 
                'usize' in stripped_line and 
                '=' in stripped_line and 
                stripped_line.endswith(';')):
                
                # Replace the entire line with our new constant
                lines[i] = f'const BYTES_PER_PACKET: usize = {packet_size};\n'
                modified = True
                break
        
        if not modified:
            print(f"Warning: Could not find BYTES_PER_PACKET constant in {filepath}")
            return False
        
        # Write the modified contents back to the file
        with open(filepath, "w") as file:
            file.writelines(lines)
        
        return True
        
    except Exception as e:
        print(f"Error modifying packet size in {filepath}: {e}")
        return False


def restore_file_contents(filepath: str, original_contents: str):
    """
    Restore the original contents of a file.
    
    Args:
        filepath: Path to the file to restore
        original_contents: Original contents to write back
    """
    with open(filepath, "w") as file:
        file.write(original_contents)


def run_packet_size_benchmarks() -> Dict[int, Dict[str, Optional[float]]]:
    """
    Run benchmarks across all packet sizes.
    
    Returns:
        Dictionary mapping packet sizes to benchmark results
    """
    test_file_path = Path(BENCHMARK_DIR) / TEST_FILE_PATH.lstrip('./')
    
    # Save original file contents for restoration at the end
    try:
        original_contents = get_file_contents(test_file_path)
    except Exception as e:
        print(f"Error reading original file contents: {e}")
        return {}
    
    results = {}
    total_tests = len(PACKET_SIZES)
    
    print(f"Running benchmarks for {total_tests} packet sizes: {PACKET_SIZES}")
    print("=" * 60)
    
    try:
        for i, packet_size in enumerate(PACKET_SIZES, 1):
            print(f"\n[{i}/{total_tests}] Testing packet size = {packet_size} bytes")
            print("-" * 40)
            
            # Modify the test file with current packet size
            if not modify_packet_size(packet_size, test_file_path):
                print(f"Skipping packet size {packet_size} due to modification error")
                results[packet_size] = {
                    'unverif_no_owl': None,
                    'unverif_owl': None,
                    'verif_no_owl': None,
                    'verif_owl': None
                }
                continue
            
            try:
                # Run benchmarks with unverified crypto
                print("Running unverified crypto benchmarks...")
                unverif_no_owl, unverif_owl = run_single_benchmark(UNVERIF_CRYPTO_ARGS)
                
                # Run benchmarks with verified crypto  
                print("Running verified crypto benchmarks...")
                verif_no_owl, verif_owl = run_single_benchmark("")
                
                results[packet_size] = {
                    'unverif_no_owl': unverif_no_owl,
                    'unverif_owl': unverif_owl,
                    'verif_no_owl': verif_no_owl,
                    'verif_owl': verif_owl
                }
                                
            except Exception as e:
                print(f"Error running benchmarks for packet size {packet_size}: {e}")
                results[packet_size] = {
                    'unverif_no_owl': None,
                    'unverif_owl': None,
                    'verif_no_owl': None,
                    'verif_owl': None
                }
    
    except Exception as e:
        print(f"Critical error during benchmark execution: {e}")
    
    finally:
        # Always restore original file contents, regardless of what happened
        try:
            restore_file_contents(test_file_path, original_contents)
            print(f"\nOriginal file contents restored to {test_file_path}")
        except Exception as e:
            print(f"Error restoring original file contents: {e}")
            print("WARNING: Original file may not have been properly restored!")
    
    return results


def create_performance_graph(results: Dict[int, Dict[str, Optional[float]]]):
    """
    Create and save a line graph of throughput performance results.
    
    Args:
        results: Dictionary mapping packet sizes to benchmark results (ns/1000 packets)
    """
    # Prepare data for plotting
    packet_sizes = []
    wg_rs_b_throughput = []    # unverif_no_owl - yellow X
    owlc_b_throughput = []     # unverif_owl - blue triangle  
    owlc_v_throughput = []     # verif_owl - red square
    
    for packet_size in sorted(results.keys()):
        data = results[packet_size]
        
        # Only include data points where we have all three values
        if (data['unverif_no_owl'] is not None and 
            data['unverif_owl'] is not None and 
            data['verif_owl'] is not None and
            packet_size > 0):  # Skip 0-byte packets for throughput calculation
            
            # Calculate throughput in Gbps for each implementation
            wg_rs_b_gbps = calculate_throughput_gbps(packet_size, data['unverif_no_owl'])
            owlc_b_gbps = calculate_throughput_gbps(packet_size, data['unverif_owl'])
            owlc_v_gbps = calculate_throughput_gbps(packet_size, data['verif_owl'])
            
            packet_sizes.append(packet_size)
            wg_rs_b_throughput.append(wg_rs_b_gbps)
            owlc_b_throughput.append(owlc_b_gbps)
            owlc_v_throughput.append(owlc_v_gbps)
    
    if not packet_sizes:
        print("Error: No valid data points for graphing")
        return
    
    # Create the plot
    plt.figure(figsize=(12, 8))
    
    # Plot the three data series
    plt.plot(packet_sizes, wg_rs_b_throughput, 'y-', marker='x', markersize=8, linewidth=2, 
             label='wg-rs_B', markeredgewidth=2)
    plt.plot(packet_sizes, owlc_b_throughput, 'b-', marker='^', markersize=8, linewidth=2, 
             label='OwlC_B', markerfacecolor='blue', markeredgecolor='blue')
    plt.plot(packet_sizes, owlc_v_throughput, 'r-', marker='s', markersize=8, linewidth=2, 
             label='OwlC_V', markerfacecolor='red', markeredgecolor='red')
    
    # Customize the plot
    plt.xlabel('Packet payload (bytes)', fontsize=12)
    plt.ylabel('Throughput (Gbps)', fontsize=12)
    plt.title('WireGuard Transport Layer Throughput vs Packet Size', fontsize=14, fontweight='bold')
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=11)
    
    # Set reasonable axis limits
    plt.xlim(min(packet_sizes) - 10, max(packet_sizes) + 10)
    plt.ylim(0, max(max(wg_rs_b_throughput), max(owlc_b_throughput), max(owlc_v_throughput)) * 1.1)
    
    # Format y-axis to show reasonable precision for Gbps values
    plt.ticklabel_format(style='plain', axis='y')
    
    # Save the plot
    plt.tight_layout()
    plt.savefig('microbench_wg_transport.png', dpi=300, bbox_inches='tight')
    plt.savefig('microbench_wg_transport.pdf', bbox_inches='tight')
    
    print(f"\nThroughput graphs saved as:")
    print(f"  - microbench_wg_transport.png")
    print(f"  - microbench_wg_transport.pdf")
    
    # Show the plot
    plt.show()


def save_results_to_csv(results: Dict[int, Dict[str, Optional[float]]]):
    """
    Save benchmark results to CSV file with both ns/iteration and Gbps metrics.
    
    Args:
        results: Dictionary mapping packet sizes to benchmark results
    """
    filename = "microbench_wg_transport.csv"
    
    try:
        with open(filename, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            
            # Write header with both timing and throughput metrics
            writer.writerow([
                'packet_size_bytes', 
                'wg_rs_B_ns_per_1000_packets', 'OwlC_B_ns_per_1000_packets', 'wg_rs_V_ns_per_1000_packets', 'OwlC_V_ns_per_1000_packets',
                'wg_rs_B_gbps', 'OwlC_B_gbps', 'wg_rs_V_gbps', 'OwlC_V_gbps'
            ])
            
            # Write data rows
            for packet_size in sorted(results.keys()):
                data = results[packet_size]
                
                # Calculate throughput values
                wg_rs_b_gbps = calculate_throughput_gbps(packet_size, data['unverif_no_owl']) if data['unverif_no_owl'] is not None else None
                owlc_b_gbps = calculate_throughput_gbps(packet_size, data['unverif_owl']) if data['unverif_owl'] is not None else None
                wg_rs_v_gbps = calculate_throughput_gbps(packet_size, data['verif_no_owl']) if data['verif_no_owl'] is not None else None
                owlc_v_gbps = calculate_throughput_gbps(packet_size, data['verif_owl']) if data['verif_owl'] is not None else None
                
                writer.writerow([
                    packet_size,
                    data['unverif_no_owl'] if data['unverif_no_owl'] is not None else '',
                    data['unverif_owl'] if data['unverif_owl'] is not None else '',
                    data['verif_no_owl'] if data['verif_no_owl'] is not None else '',
                    data['verif_owl'] if data['verif_owl'] is not None else '',
                    f"{wg_rs_b_gbps:.4f}" if wg_rs_b_gbps is not None else '',
                    f"{owlc_b_gbps:.4f}" if owlc_b_gbps is not None else '',
                    f"{wg_rs_v_gbps:.4f}" if wg_rs_v_gbps is not None else '',
                    f"{owlc_v_gbps:.4f}" if owlc_v_gbps is not None else ''
                ])
        
        print(f"Raw data saved to {filename}")
        
    except Exception as e:
        print(f"Error saving CSV data: {e}")


def print_summary_table(results: Dict[int, Dict[str, Optional[float]]]):
    """
    Print a summary table of results with both timing and throughput metrics.
    
    Args:
        results: Dictionary mapping packet sizes to benchmark results
    """
    table = PrettyTable()
    table.field_names = [
        "Packet Size (bytes)", 
        "wg-rs_B (Gbps)", 
        "OwlC_B (Gbps)", 
        "wg-rs_V (Gbps)", 
        "OwlC_V (Gbps)"
    ]
    
    for packet_size in sorted(results.keys()):
        data = results[packet_size]
        
        def format_throughput(ns_per_packet):
            if ns_per_packet is not None and packet_size > 0:
                gbps = calculate_throughput_gbps(packet_size, ns_per_packet)
                return f"{gbps:.2f}"
            return "N/A"
        
        table.add_row([
            packet_size,
            format_throughput(data['unverif_no_owl']),
            format_throughput(data['unverif_owl']),
            format_throughput(data['verif_no_owl']),
            format_throughput(data['verif_owl'])
        ])
    
    print("\nThroughput Summary Table:")
    print(table)


def main():
    """Main execution function."""
    validate_benchmark_directory()
    
    print("=" * 60)
    print("WireGuard Transport Layer Benchmark Suite")
    print("=" * 60)
    
    # Run all packet size benchmarks
    results = run_packet_size_benchmarks()
    
    print("\n" + "=" * 60)
    print("Benchmark suite completed")
    
    # Generate outputs
    print("\nGenerating results...")
    save_results_to_csv(results)
    print_summary_table(results)
    create_performance_graph(results)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nBenchmark interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"\nUnexpected error: {e}")
        sys.exit(1)