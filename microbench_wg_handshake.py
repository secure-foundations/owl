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

# Configurations to test
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

def build_cargo_command(base_args: str) -> str:
    return " ".join([
        BASE_COMMAND,
        base_args,
        "--",
        BENCH_PATTERN,
        BENCH_ARGS,
        HIDE_STDERR
    ])


def run_cargo_bench(command: str) -> Optional[List[Dict]]:
    try:
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
        
        animation_thread = threading.Thread(target=animate)
        animation_thread.daemon = True
        animation_thread.start()
        
        output = subprocess.check_output(
            command, 
            shell=True, 
            text=True,
            cwd=BENCHMARK_DIR
        )
        
        animation_active = False
        time.sleep(0.2)
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        
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
        animation_active = False
        time.sleep(0.2)
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        
        print(f"Error executing cargo bench: {e}")
        print(f"Return code: {e.returncode}")
        return None
    except Exception as e:
        animation_active = False
        time.sleep(0.2)
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        
        print(f"Unexpected error: {e}")
        return None


def process_benchmark_output(cargo_bench_output: List[Dict]) -> Dict[str, Dict]:
    bench_results = [obj for obj in cargo_bench_output if obj.get('type') == 'bench']
    
    if not bench_results:
        print("Warning: No benchmark results found in output")
        return {}
    
    structured_results = {}
    
    for display_name, handshake_pattern, init_pattern in BENCHMARK_PATTERNS:
        matching_results = [
            result for result in bench_results 
            if handshake_pattern in result.get('name', '')
        ]
        
        if len(matching_results) != 2:
            print(f"Warning: Expected 2 results for pattern '{handshake_pattern}', found {len(matching_results)}")
            continue
        
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
            'init_median': init_result.get('median', 0),
        }
    
    return structured_results


def calculate_metrics(data: Dict[str, Dict]) -> Dict[str, Dict]:
    enhanced_data = {}
    
    for name, values in data.items():
        handshake_median = values['handshake_median']
        init_median = values['init_median']
        
        net_handshake_ns = handshake_median - init_median
        handshakes_per_sec = 1e9 / net_handshake_ns if net_handshake_ns > 0 else 0
               
        enhanced_data[name] = {
            'handshake_median': handshake_median,
            'init_median': init_median,
            'net_handshake_ns': net_handshake_ns,
            'handshakes_per_sec': handshakes_per_sec,
        }
    
    # Calculate relative performance compared to baseline
    baseline_data = enhanced_data.get(BASELINE)
    if baseline_data and baseline_data['handshakes_per_sec'] > 0:
        baseline_hps = baseline_data['handshakes_per_sec']
        
        for name, values in enhanced_data.items():
            if name == BASELINE:
                values['performance_pct'] = 0.0
            else:
                current_hps = values['handshakes_per_sec']
                if current_hps > 0:
                    values['performance_pct'] = ((current_hps - baseline_hps) / baseline_hps) * 100
                else:
                    values['performance_pct'] = -100.0
    
    return enhanced_data


def get_implementation_name(impl_type: str, is_verified: bool) -> str:
    if impl_type == "rust":
        return "wireguard-rs"
    elif impl_type == "owl":
        return "OwlC_V" if is_verified else "OwlC_B"
    else:
        return impl_type


def format_matrix_cell(name: str, enhanced_data: Dict[str, Dict]) -> str:
    if name not in enhanced_data:
        return "N/A"
    
    values = enhanced_data[name]
    handshakes_per_sec = values['handshakes_per_sec']
    performance_pct = values['performance_pct']
    
    if name == BASELINE:
        return f"{handshakes_per_sec:,.0f} (---)"
    else:
        return f"{handshakes_per_sec:,.0f} ({performance_pct:+.1f}%)"


def mk_table(data: Dict[str, Dict], is_verified: bool) -> PrettyTable:   
    enhanced_data = calculate_metrics(data)
    rust_name = get_implementation_name("rust", is_verified)
    owl_name = get_implementation_name("owl", is_verified)

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
    
    return table

def display_matrix_results(data: Dict[str, Dict], is_verified: bool):
    if not data:
        print("No benchmark data to display")
        return
    
    table = mk_table(data, is_verified)

    print("Performance Matrix (handshakes/sec with relative performance %)")
    print(table)


def save_raw_data_to_csv(verif_results: Dict, unverif_results: Dict, filename: str):
    try:
        with open(filename, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            
            writer.writerow([
                'crypto_type', 'configuration', 'initiator', 'responder', 
                'handshake_median_ns', 'init_median_ns',
                'net_handshake_ns', 'handshakes_per_sec', 'performance_change_pct'
            ])
            
            def write_suite_data(results: Dict, crypto_type: str):
                if not results:
                    return
                    
                enhanced_data = calculate_metrics(results)
                
                for config_name, values in enhanced_data.items():
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
                        values['init_median'],
                        values['net_handshake_ns'],
                        values['handshakes_per_sec'],
                        performance_pct
                    ])
            
            write_suite_data(verif_results, 'verified')
            write_suite_data(unverif_results, 'unverified')
            
        print(f"Raw data saved to {filename}")
        
    except Exception as e:
        print(f"Error saving CSV data: {e}")


def save_formatted_tables_to_txt(verif_results: Dict, unverif_results: Dict, filename: str):
    try:
        with open(filename, 'w') as txtfile:
            txtfile.write("WireGuard Handshake Micro-benchmark Results\n")
            txtfile.write("=" * 60 + "\n\n")
            
            txtfile.write("Benchmarks with verified crypto:\n")
            txtfile.write("-" * 40 + "\n")
            
            if verif_results:
                table = mk_table(verif_results, True)
                txtfile.write("Performance Matrix (handshakes/sec with relative performance %)\n")
                txtfile.write(str(table) + "\n")
            else:
                txtfile.write("Failed to run verified crypto benchmarks\n")
            
            txtfile.write("\n" + "=" * 60 + "\n\n")
            
            txtfile.write("Benchmarks with unverified crypto:\n")
            txtfile.write("-" * 40 + "\n")
            
            if unverif_results:
                table = mk_table(unverif_results, False)
                txtfile.write("Performance Matrix (handshakes/sec with relative performance %)\n")
                txtfile.write(str(table) + "\n")
            else:
                txtfile.write("Failed to run unverified crypto benchmarks\n")
            
            txtfile.write("\n" + "=" * 60 + "\n")
            txtfile.write("Micro-benchmark suite completed\n")
        
        print(f"Formatted tables saved to {filename}")
        
    except Exception as e:
        print(f"Error saving text file: {e}")


def run_benchmark_suite(base_args: str = "") -> Optional[Dict[str, Dict]]:
    command = build_cargo_command(base_args)
    raw_output = run_cargo_bench(command)
    
    if raw_output is None:
        return None
    
    return process_benchmark_output(raw_output)


def main():
    print("=" * 60)
    print("WireGuard Handshake Micro-benchmark Suite")
    print("=" * 60)
    
    print("\nBenchmarks with verified crypto:")
    print("-" * 40)
    verif_results = run_benchmark_suite("")
    
    if verif_results:
        display_matrix_results(verif_results, is_verified=True)
    else:
        print("Failed to run verified crypto benchmarks")
        verif_results = {}
    
    print("\n" + "=" * 60)
    
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
    
    print("\nSaving results...")
    save_raw_data_to_csv(verif_results, unverif_results, "microbench_wg_handshake.csv")
    save_formatted_tables_to_txt(verif_results, unverif_results, "microbench_wg_handshake.txt")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nBenchmark interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"\nUnexpected error: {e}")
        sys.exit(1)