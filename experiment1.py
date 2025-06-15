#!/usr/bin/env python3
"""
Script to run commands and collect statistics for files in the examples directory.
Measures execution times and lines of code for OWL and Verus commands.
"""

import os
import subprocess
import time
import json
import csv
from pathlib import Path
from typing import Dict, List, Optional
import re
from prettytable import PrettyTable


def run_command_with_time(command: List[str], cwd: Optional[str] = None, timeout: int = 1200) -> tuple[float, str, str]:
    """
    Run a command and measure its execution time.
    Returns (execution_time, stdout, stderr)
    """
    start_time = time.time()
    try:
        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            cwd=cwd,
            timeout=timeout,
        )
        end_time = time.time()
        execution_time = end_time - start_time
        return execution_time, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return -1, "", "Command timed out"
    except Exception as e:
        return -1, "", str(e)


def get_verus_loc(file_path: str) -> int:
    """
    Get lines of code using tokei.
    Falls back to simple line counting if tokei is not available.
    """
    try:
        result = subprocess.run(
            ["tokei", "--output", "json", file_path],
            capture_output=True,
            text=True,
            timeout=30
        )
        if result.returncode == 0:
            data = json.loads(result.stdout)
            # Navigate the tokei JSON structure to get total lines of code
            for lang_data in data.values():
                if isinstance(lang_data, dict) and 'code' in lang_data:
                    return lang_data['code']
            return 0
    except (subprocess.TimeoutExpired, json.JSONDecodeError, FileNotFoundError):
        print(f"Warning: tokei line count failed for {file_path}.")
        return 0
    

def get_owl_loc(file_path: str) -> int:
    """
    Get lines of code for OWL files by counting non-empty non-comment lines.
    """
    # Fallback: count non-empty lines
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
    """
    Extract timing information from Verus JSON output.
    """
    try:
        data = json.loads(json_output)

        # Look up timing information in the JSON structure
        if isinstance(data, dict) and 'times-ms' in data:
            times_ms = data['times-ms']
            if isinstance(times_ms, dict) and 'total' in times_ms:
                # Convert from milliseconds to seconds
                total_verify_ms = float(times_ms['total'])
                return total_verify_ms / 1000.0
                    
        # If no timing found in JSON, return -1 to indicate unavailable
        return -1
    except (json.JSONDecodeError, ValueError, KeyError):
        return -1


def collect_file_statistics(file_path: str, is_full_case_study: bool) -> Dict[str, any]:
    """
    Collect statistics for a single file.
    """
    file_name = os.path.basename(file_path)
    print(f"Processing {file_path}...")
    
    stats = {
        'file': file_name,
        'owl_loc': 0,
        'owl_time': -1,
        'verus_loc': 0,
        'verus_time': -1
    }
    
    # Get OWL statistics
    print(f"  Running OWL command for {file_name}")
    owl_time, owl_stdout, owl_stderr = run_command_with_time(
        ["cabal", "run", "owl", "--", "-e", file_path]
    )
    stats['owl_time'] = owl_time
    if is_full_case_study:
        stats['owl_loc'] = get_case_study_loc(file_path)
    else: 
        stats['owl_loc'] = get_owl_loc(file_path)
    
    if owl_time == -1:
        print(f"  Warning: OWL command failed for {file_name}: {owl_stderr}")
        # Don't run Verus if Owl fails
        return stats
    else:
        print(f"  OWL completed in {owl_time:.2f}s, {stats['owl_loc']} LoC")
    
    # Get Verus statistics
    print(f"  Running Verus commands")

    # Change to extraction directory
    extraction_dir = "./extraction"
    if not os.path.exists(extraction_dir):
        print(f"  Warning: Extraction directory not found at {extraction_dir}")
        stats['verus_time'] = -1
        stats['verus_loc'] = 0
    else:
        # Run verusfmt first
        print(f"    Running verusfmt...")
        fmt_time, fmt_stdout, fmt_stderr = run_command_with_time(
            ["verusfmt", "src/lib.rs"],
            cwd=extraction_dir
        )
        
        if fmt_time == -1:
            print(f"    Warning: verusfmt failed: {fmt_stderr}")
        else:
            print(f"    verusfmt completed in {fmt_time:.2f}s")
        
        # Run cargo verus verify
        print(f"    Running cargo verus verify...")
        verus_time, verus_stdout, verus_stderr = run_command_with_time(
            ["cargo", "verus", "verify", "--", "--no-lifetime", "--output-json", "--time"],
            cwd=extraction_dir
        )
        
        if verus_time == -1:
            print(f"    Warning: cargo verus verify failed: {verus_stderr}")
            stats['verus_time'] = -1
        else:
            # Extract time from JSON output
            json_time = get_verus_time_from_json(verus_stdout)
            if json_time != -1:
                stats['verus_time'] = json_time
                print(f"    Extracted verus time from JSON output: {json_time:.2f}s")
            else:
                print(f"    Warning: could not extract verus time from JSON")            
        
        # Get Verus LoC
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
    
    fieldnames = ['file', 'owl_loc', 'owl_time', 'verus_loc', 'verus_time']
    
    with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(data)
    
    print(f"CSV data saved to {filename}")


def format_table(data: List[Dict]) -> str:
    """Format data as a nicely aligned table using PrettyTable."""
    if not data:
        return "No data to display"
    
    # Create PrettyTable
    table = PrettyTable()
    table.field_names = ["File", "OWL_LOC", "OWL_TIME", "VERUS_LOC", "VERUS_TIME"]
    
    # Add rows
    for row in data:
        owl_time_str = f"{row['owl_time']:.2f}s" if row['owl_time'] != -1 else "FAILED"
        verus_time_str = f"{row['verus_time']:.2f}s" if row['verus_time'] != -1 else "FAILED"
        
        table.add_row([
            row['file'],
            row['owl_loc'],
            owl_time_str,
            row['verus_loc'],
            verus_time_str
        ])
    
    # Configure table appearance
    table.align = "l"  # Left align by default
    table.align["OWL_LOC"] = "r"  # Right align numeric columns
    table.align["VERUS_LOC"] = "r"
    table.align["OWL_TIME"] = "r"
    table.align["VERUS_TIME"] = "r"
    
    return str(table)

def clean_smtcache_files(directory: str):
    """Remove all .smtcache files from the specified directory and subdirectories."""
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
    """Main function to orchestrate the statistics collection."""
    toy_protocols_dir = "owl_toy_protocols"
    full_case_studies_dir = "full_protocol_case_studies/owl_models/"
    wireguard_owl_filepath = "wg/wg_full.owl"
    hpke_owl_filepath = "hpke/hpke_full.owl"

    # Build OWL first to ensure we don't measure compilation time (might take longer)
    print("(Re)building OWL...")
    build_time, build_stdout, build_stderr = run_command_with_time(["cabal", "build", "owl"])
    if build_time == -1:
        print(f"Error: Failed to build OWL: {build_stderr}")
        return 1
    else:
        print(f"OWL build completed in {build_time:.2f}s")

    # Collect toy protocols files
    if not os.path.exists(toy_protocols_dir):
        print(f"Error: Directory '{toy_protocols_dir}' not found")
        return 1
    
    # Clean .smtcache files from examples directory
    print("Cleaning .smtcache files from examples directory...")
    clean_smtcache_files(toy_protocols_dir)
    print("=" * 50)   

    # Find all .owl files in examples directory
    example_files = []
    for root, dirs, files in os.walk(toy_protocols_dir):
        for file in files:
            if file.endswith('.owl'):
                file_path = os.path.join(root, file)
                example_files.append(file_path)
    
    if not example_files:
        print(f"No files found in {toy_protocols_dir}")
        return 1
    
    print(f"Found {len(example_files)} files in {toy_protocols_dir}")
    print("=" * 50)

    # Collect full case study files
    print("Cleaning smtcache files from full case studies directory...")
    clean_smtcache_files(full_case_studies_dir)
    print("=" * 50)

    full_case_studies_files = [os.path.join(full_case_studies_dir, wireguard_owl_filepath), os.path.join(full_case_studies_dir, hpke_owl_filepath)]

    all_files_to_process = [(f, False) for f in sorted(example_files)] + [(f, True) for f in full_case_studies_files]

    # Collect statistics for each file
    all_stats = []
    for file_path, is_full_case_study in all_files_to_process:
        try:
            stats = collect_file_statistics(file_path, is_full_case_study)
            all_stats.append(stats)
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
        print("-" * 30)
    
    if not all_stats:
        print("No statistics collected")
        return 1
    
    # Save CSV
    save_csv(all_stats, "experiment1.csv")
    
    # Generate and display formatted table
    table = format_table(all_stats)
    print("\nFormatted Results:")
    print("=" * 50)
    print(table)
    
    # Save formatted table to file
    with open("experiment1.txt", "w", encoding="utf-8") as f:
        f.write("Experiment 1 Results\n")
        f.write("=" * 50 + "\n\n")
        f.write(table)
    
    print(f"\nFormatted table saved to experiment1.txt")
    
    return 0


if __name__ == "__main__":
    exit(main())