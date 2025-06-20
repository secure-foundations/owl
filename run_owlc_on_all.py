"""
Script to run commands and collect statistics for files in the examples directory.
Measures execution times and lines of code for Owl and Verus commands.
"""

import os
import subprocess
import time
import json
import csv
import threading
import sys
from pathlib import Path
from typing import Dict, List, Optional
import re
from prettytable import PrettyTable


# Owl protocols to test
ORDERED_FILES = [
    ("Basic-Hash", "owl_toy_protocols/basic_hash-indexed.owl", False),
    ("Hash-Lock", "owl_toy_protocols/hash-lock.owl", False),
    ("LAK", "owl_toy_protocols/lak-indexed.owl", False),
    ("MW", "owl_toy_protocols/mw-indexed.owl", False),
    ("Feldhofer", "owl_toy_protocols/feldhofer-indexed.owl", False),
    ("Private Auth", "owl_toy_protocols/private_authentication_hybrid.owl", False),
    ("Needham-Schroeder (sym)", "owl_toy_protocols/ns-sym-indexed.owl", False),
    ("Needham-Schroeder (pub)", "owl_toy_protocols/nsl.owl", False),
    ("Otway-Rees", "owl_toy_protocols/otwayrees-indexed.owl", False),
    ("Yahalom (sym)", "owl_toy_protocols/yahalom-indexed.owl", False),
    ("Denning-Sacco (pub)", "owl_toy_protocols/denning-sacco.owl", False),
    ("Core Kerberos", "owl_toy_protocols/kerberos.owl", False),
    ("Diffie-Hellman Key Exchange", "owl_toy_protocols/dhke.owl", False),
    ("SSH Forwarding Agent", "owl_toy_protocols/ssh.owl", False),
    ("WireGuard", "full_protocol_case_studies/owl_models/wg/wg_full.owl", True),
    ("HPKE", "full_protocol_case_studies/owl_models/hpke/hpke_full.owl", True),
]


def run_command_with_time(command: List[str], cwd: Optional[str] = None) -> tuple[float, str, str]:
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
    
    start_time = time.time()
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            cwd=cwd
        )
        end_time = time.time()
        execution_time = end_time - start_time
        
        animation_active = False
        sys.stdout.write('\r' + ' ' * 50 + '\r') 
        sys.stdout.flush()
        
        return execution_time, result.stdout, result.stderr
        
    except subprocess.TimeoutExpired:
        animation_active = False
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        return -1, "", "Command timed out"
    except Exception as e:
        animation_active = False
        sys.stdout.write('\r' + ' ' * 50 + '\r')
        sys.stdout.flush()
        return -1, "", str(e)


def get_verus_loc(file_path: str) -> int:
    try:
        result = subprocess.run(
            ["tokei", "--output", "json", file_path],
            capture_output=True,
            text=True,
            timeout=30
        )
        if result.returncode == 0:
            data = json.loads(result.stdout)
            for lang_data in data.values():
                if isinstance(lang_data, dict) and 'code' in lang_data:
                    return lang_data['code']
            return 0
    except (subprocess.TimeoutExpired, json.JSONDecodeError, FileNotFoundError):
        print(f"Warning: tokei line count failed for {file_path}.")
        return 0
    

def get_owl_loc(file_path: str) -> int:
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            count = 0
            for line in f:
                line = line.lstrip()
                if line == '':
                    continue
                if line.lstrip()[0] != '/' and line.lstrip()[0] != '*' :
                    count += 1
            return count
    except Exception:
        print(f"Warning: owl line count failed for {file_path}.")
        return 0

def get_case_study_loc(file_path: str) -> int:
    directory = os.path.dirname(file_path)
    count = 0
    try:
        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.owl'):
                    file_path = os.path.join(root, file)
                    count += get_owl_loc(file_path)
        return count
    except Exception as e:
        print(f"Warning: Error counting Owl case study LoC in {directory}: {e}")
        return 0

def get_verus_time_from_json(json_output: str) -> float:
    try:
        data = json.loads(json_output)

        if isinstance(data, dict) and 'times-ms' in data:
            times_ms = data['times-ms']
            if isinstance(times_ms, dict) and 'total' in times_ms:
                total_verify_ms = float(times_ms['total'])
                return total_verify_ms / 1000.0
        else:
            return -1
    except (json.JSONDecodeError, ValueError, KeyError):
        with open("log.txt", 'w') as f:
            f.write(json_output)
        return -1


def collect_file_statistics(display_name: str, file_path: str, is_full_case_study: bool) -> Dict[str, any]:
    """
    Collect statistics for a single file.
    """
    print(f"Processing {display_name} ({file_path})...")
    
    stats = {
        'file': display_name,
        'owl_loc': 0,
        'owl_time': -1,
        'verus_loc': 0,
        'verus_time': -1
    }
    
    print(f"  Running Owl command for {display_name}")
    owl_time, owl_stdout, owl_stderr = run_command_with_time(
        ["cabal", "run", "owl", "--", "-e", file_path]
    )
    stats['owl_time'] = owl_time
    if is_full_case_study:
        stats['owl_loc'] = get_case_study_loc(file_path)
    else: 
        stats['owl_loc'] = get_owl_loc(file_path)
    
    if owl_time == -1:
        print(f"  Warning: Owl command failed for {display_name}: {owl_stderr}")
        # Don't run Verus if Owl fails
        return stats
    else:
        print(f"  Owl completed in {owl_time:.2f}s, {stats['owl_loc']} LoC")
    
    print(f"  Running Verus commands")

    extraction_dir = "./extraction"
    if not os.path.exists(extraction_dir):
        print(f"  Warning: Extraction directory not found at {extraction_dir}")
        stats['verus_time'] = -1
        stats['verus_loc'] = 0
    else:
        print(f"    Running verusfmt...")
        fmt_time, fmt_stdout, fmt_stderr = run_command_with_time(
            ["verusfmt", "src/lib.rs"],
            cwd=extraction_dir
        )
        
        if fmt_time == -1:
            print(f"    Warning: verusfmt failed: {fmt_stderr}")
        else:
            print(f"    verusfmt completed in {fmt_time:.2f}s")

        max_attempts = 2
        attempt = 1

        while attempt <= max_attempts:
            print(f"    Running cargo verus verify...")
            verus_time, verus_stdout, verus_stderr = run_command_with_time(
                ["cargo", "verus", "verify", "--", "--no-lifetime", "--output-json", "--time"],
                cwd=extraction_dir
            )
        
            if verus_time == -1:
                print(f"    Warning: cargo verus verify failed: {verus_stderr}")
                stats['verus_time'] = -1
            else:
                json_time = get_verus_time_from_json(verus_stdout)
                if json_time != -1:
                    stats['verus_time'] = json_time
                    print(f"    Extracted verus time from JSON output: {json_time:.2f}s")
                    break
                else:
                    print(f"    Warning: could not extract verus time from JSON")            
            print(f"    Retrying...")
            attempt += 1 
                    
        verus_lib_path = os.path.join(extraction_dir, "src/lib.rs")
        if os.path.exists(verus_lib_path):
            stats['verus_loc'] = get_verus_loc(verus_lib_path)
            print(f"    Verus LoC: {stats['verus_loc']}")
        else:
            print(f"    Warning: Verus lib.rs not found at {verus_lib_path}")
            stats['verus_loc'] = 0
    
    return stats


def save_csv(data: List[Dict], filename: str):
    """Save data to CSV file."""
    if not data:
        return
    
    fieldnames = ['file', 'owl_loc', 'verus_loc', 'owl_time', 'verus_time']
    
    with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(data)
    
    print(f"CSV data saved to {filename}")


def format_table(data: List[Dict]) -> str:
    """Format data as a nicely aligned table using PrettyTable."""
    if not data:
        return "No data to display"
    
    table = PrettyTable()
    table.field_names = ["Case Study", "Owl_LOC", "VERUS_LOC", "Owl_TIME", "VERUS_TIME"]
    
    for row in data:
        owl_time_str = f"{row['owl_time']:.2f}s" if row['owl_time'] != -1 else "ERROR"
        verus_time_str = f"{row['verus_time']:.2f}s" if row['verus_time'] != -1 else "ERROR"
        
        table.add_row([
            row['file'],
            row['owl_loc'],
            row['verus_loc'],
            owl_time_str,
            verus_time_str
        ])
    
    table.align = "l"
    table.align["Owl_LOC"] = "r"
    table.align["VERUS_LOC"] = "r"
    table.align["Owl_TIME"] = "r"
    table.align["VERUS_TIME"] = "r"
    
    return str(table)

def clean_smtcache_files(directory: str):
    removed_count = 0
    try:
        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.smtcache'):
                    file_path = os.path.join(root, file)
                    try:
                        os.remove(file_path)
                        removed_count += 1
                    except Exception as e:
                        print(f"Warning: Failed to remove {file_path}: {e}")
        
        if removed_count > 0:
            print(f"Removed {removed_count} .smtcache files from {directory}")
        else:
            print(f"No .smtcache files found in {directory}")
    except Exception as e:
        print(f"Warning: Error cleaning .smtcache files from {directory}: {e}")

def main():
    print("(Re)building OwlC...")
    build_time, build_stdout, build_stderr = run_command_with_time(["cabal", "build", "owl"])
    if build_time == -1:
        print(f"Error: Failed to build OwlC: {build_stderr}")
        return 1
    else:
        print(f"OwlC build completed in {build_time:.2f}s")

    directories_to_clean = ["owl_toy_protocols", "full_protocol_case_studies"]
    for directory in directories_to_clean:
        if os.path.exists(directory):
            print(f"Cleaning .smtcache files from {directory}...")
            clean_smtcache_files(directory)
    print("=" * 50)   

    all_stats = []
    for display_name, file_path, is_full_case_study in ORDERED_FILES:
        if not os.path.exists(file_path):
            print(f"Warning: File not found: {file_path} (for {display_name})")
            print("-" * 30)
            continue
            
        try:
            stats = collect_file_statistics(display_name, file_path, is_full_case_study)
            all_stats.append(stats)
        except Exception as e:
            print(f"Error processing {display_name} ({file_path}): {e}")
        print("-" * 30)
    
    if not all_stats:
        print("No statistics collected")
        return 1

    save_csv(all_stats, "run_owlc_on_all.csv")
    
    table = format_table(all_stats)
    print("\nFormatted Results:")
    print("=" * 50)
    print(table)
    
    with open("run_owlc_on_all.txt", "w", encoding="utf-8") as f:
        f.write("OwlC Results\n")
        f.write("=" * 50 + "\n\n")
        f.write(table)
    
    print("\nFormatted table saved to run_owlc_on_all.txt")
    
    return 0


if __name__ == "__main__":
    exit(main())
