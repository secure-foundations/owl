#!/usr/bin/env python3

import subprocess
import json
import time
import argparse
import os
import sys
import tempfile
from prettytable import PrettyTable

class WireguardBenchmark:
    def __init__(self, wireguard_bin, use_owl=False, use_kernel=False):
        self.wireguard_bin = os.path.realpath(wireguard_bin) if wireguard_bin else ""
        self.use_owl = use_owl
        self.use_kernel = use_kernel
        self.config_dir = 'full_protocol_case_studies/implementations/wireguard'
        self.delays = ['0ms', '0.5ms', '1ms', '1.5ms', '2ms', '3ms', '4ms', '5ms', '6ms', '7ms', '8ms', '9ms', '10ms']
        self.results = []

    def run_command(self, cmd, check=True, capture_output=False):
        """Run a shell command"""
        try:
            if capture_output:
                result = subprocess.run(cmd, shell=True, check=check, capture_output=True, text=True)
                return result
            else:
                subprocess.run(cmd, shell=True, check=check)
        except subprocess.CalledProcessError as e:
            print(f"Command failed: {cmd}")
            print(f"Error: {e}")
            if capture_output and e.stdout:
                print(f"Stdout: {e.stdout}")
            if capture_output and e.stderr:
                print(f"Stderr: {e.stderr}")
            raise

    def setup_network(self):
        """Set up the network configuration"""
        print("Setting up network configuration...")
        
        # Set up network namespace
        self.run_command("ip netns add net1")
        
        # Set up virtual ethernet interface pair
        self.run_command("ip link add veth1 type veth peer veth1n")
        
        # Move veth1n into the net1 namespace
        self.run_command("ip link set veth1n netns net1")
        
        # Bring up loopback in the net1 namespace
        self.run_command("ip netns exec net1 ip link set dev lo up")
        
        # Bring up the network interfaces
        self.run_command("ip link set dev veth1 up")
        self.run_command("ip netns exec net1 ip link set dev veth1n up")
        
        # Add IP addresses to veth1 and veth1n
        self.run_command("ip addr add 10.100.1.1/24 dev veth1")
        self.run_command("ip netns exec net1 ip addr add 10.100.1.2/24 dev veth1n")
        
        # Add default route to the net1 namespace
        self.run_command("ip netns exec net1 route add default gw 10.100.1.1")
        
        # Set up wireguard interfaces
        env = os.environ.copy()
        env['WG_THREADS'] = '1'
        env['GOMAXPROCS'] = '1'
        
        if self.use_owl:
            print("Using owl routines")
            subprocess.run(f"WG_THREADS=1 {self.wireguard_bin} --owl wg1", shell=True, env=env)
            subprocess.run(f"WG_THREADS=1 ip netns exec net1 {self.wireguard_bin} --owl wg1n", shell=True, env=env)
        elif self.use_kernel:
            print("Using kernel wireguard")
            self.run_command("ip link add wg1 type wireguard")
            self.run_command("ip netns exec net1 ip link add wg1n type wireguard")
        else:
            subprocess.run(f"WG_THREADS=1 {self.wireguard_bin} wg1", shell=True, env=env)
            subprocess.run(f"WG_THREADS=1 ip netns exec net1 {self.wireguard_bin} wg1n", shell=True, env=env)
        
        # Add IP addresses to Wireguard interfaces
        self.run_command("ip addr add 10.100.2.1/24 dev wg1")
        self.run_command("ip netns exec net1 ip addr add 10.100.2.2/24 dev wg1n")
        
        # Configure the Wireguard interfaces (run in background)
        wg1_conf = os.path.join(self.config_dir, 'wg1.conf')
        wg1n_conf = os.path.join(self.config_dir, 'wg1n.conf')
        subprocess.Popen(f"wg setconf wg1 {wg1_conf}", shell=True)
        subprocess.Popen(f"ip netns exec net1 wg setconf wg1n {wg1n_conf}", shell=True)
        
        # Bring up the Wireguard interfaces
        self.run_command("ip link set wg1 up")
        self.run_command("ip netns exec net1 ip link set wg1n up")

    def cleanup_network(self):
        """Clean up the network configuration"""
        print("Cleaning up network configuration...")
        
        try:
            # Delete wg1 interface
            self.run_command("ip link del wg1", check=False)
            self.run_command("ip netns exec net1 ip link del wg1n", check=False)
            
            # Delete veth1 interface
            self.run_command("ip link del veth1", check=False)
            
            # Delete net1 namespace
            self.run_command("ip netns del net1", check=False)
        except Exception as e:
            print(f"Warning: Cleanup may have been incomplete: {e}")

    def configure_delay(self, delay):
        """Configure network delay on interfaces"""
        print(f"Configuring delay: {delay}")
        
        # Clear any existing qdisc
        self.run_command("tc qdisc del dev veth1 root", check=False)
        self.run_command("ip netns exec net1 tc qdisc del dev veth1n root", check=False)
        
        # Set up link delay on outbound interface
        self.run_command(f"tc qdisc add dev veth1 root netem delay {delay}")
        
        # Set up link delay on inbound interface
        self.run_command(f"ip netns exec net1 tc qdisc add dev veth1n root netem delay {delay}")

    def run_iperf_test(self, delay):
        """Run iperf3 test and return the result"""
        print(f"Running iperf test with delay {delay}...")
        
        # Start iperf server in net1 namespace (daemon mode, one connection)
        self.run_command("ip netns exec net1 iperf3 -sD -1")
        
        # Wait a moment for server to start
        time.sleep(2)
        
        # Create temporary file for iperf output
        with tempfile.NamedTemporaryFile(mode='w+', suffix='.json', delete=False) as temp_file:
            temp_filename = temp_file.name
        
        try:
            # Run iperf client in default namespace
            self.run_command(f"timeout 15 iperf3 -c 10.100.2.2 --zerocopy --time 10 --logfile {temp_filename} --json")
            
            # Read and parse the JSON output
            with open(temp_filename, 'r') as f:
                result = json.load(f)
                
            # Extract bits per second from end summary
            bits_per_second = result['end']['sum_received']['bits_per_second']
            return bits_per_second
            
        finally:
            # Clean up temp file
            if os.path.exists(temp_filename):
                os.unlink(temp_filename)

    def run_benchmark(self):
        """Run the complete benchmark suite"""
        print("Starting Wireguard benchmark...")
        
        for delay in self.delays:
            try:
                # Set up network
                self.setup_network()
                
                # Configure delay
                self.configure_delay(delay)
                
                # Wait for network to stabilize
                time.sleep(5)
                
                # Run test
                bits_per_second = self.run_iperf_test(delay)
                
                # Convert to Mbps for easier reading
                mbps = bits_per_second / 1_000_000
                
                self.results.append({
                    'delay': delay,
                    'bits_per_second': bits_per_second,
                    'mbps': mbps
                })
                
                print(f"Delay {delay}: {mbps:.2f} Mbps")
                
            except Exception as e:
                print(f"Error testing delay {delay}: {e}")
                self.results.append({
                    'delay': delay,
                    'bits_per_second': 0,
                    'mbps': 0,
                    'error': str(e)
                })
            finally:
                # Always clean up
                self.cleanup_network()
                time.sleep(2)

    def print_results(self):
        """Print results in a formatted table"""
        if not self.results:
            print("No results to display")
            return
            
        table = PrettyTable()
        table.field_names = ["Delay", "Throughput (Mbps)", "Throughput (bps)", "Status"]
        
        for result in self.results:
            if 'error' in result:
                table.add_row([result['delay'], "ERROR", "ERROR", result['error']])
            else:
                table.add_row([
                    result['delay'],
                    f"{result['mbps']:.2f}",
                    f"{result['bits_per_second']:,}",
                    "OK"
                ])
        
        print("\nBenchmark Results:")
        print(table)

def main():
    parser = argparse.ArgumentParser(description='Benchmark Wireguard performance with various network delays')
    parser.add_argument('wireguard_bin', nargs='?', help='Path to wireguard binary (not needed for kernel mode)')
    parser.add_argument('-o', '--owl', action='store_true', help='Use owl routines (for wireguard-rs)')
    parser.add_argument('-k', '--kernel', action='store_true', help='Use kernel wireguard')
    
    args = parser.parse_args()
    
    # Check if wireguard binary is provided when not using kernel mode
    if not args.kernel:
        if not args.wireguard_bin:
            print("Error: Path to wireguard binary is required unless using kernel mode (-k)")
            sys.exit(1)
        if not os.path.exists(args.wireguard_bin):
            print(f"Error: Wireguard binary not found: {args.wireguard_bin}")
            sys.exit(1)
    
    # Check for required config files
    config_dir = 'full_protocol_case_studies/implementations/wireguard'
    wg1_conf = os.path.join(config_dir, 'wg1.conf')
    wg1n_conf = os.path.join(config_dir, 'wg1n.conf')
    
    if not os.path.exists(wg1_conf):
        print(f"Error: wg1.conf not found at {wg1_conf}")
        sys.exit(1)
    
    if not os.path.exists(wg1n_conf):
        print(f"Error: wg1n.conf not found at {wg1n_conf}")
        sys.exit(1)
    
    # Check if we're running as root (required for network namespaces)
    if os.geteuid() != 0:
        print("Error: This script must be run as root (for network namespace operations)")
        sys.exit(1)
    
    # Run benchmark
    benchmark = WireguardBenchmark(
        args.wireguard_bin if args.wireguard_bin else "",
        use_owl=args.owl,
        use_kernel=args.kernel
    )
    
    try:
        benchmark.run_benchmark()
        benchmark.print_results()
    except KeyboardInterrupt:
        print("\nBenchmark interrupted by user")
        benchmark.cleanup_network()
    except Exception as e:
        print(f"Benchmark failed: {e}")
        benchmark.cleanup_network()
        sys.exit(1)

if __name__ == "__main__":
    main()