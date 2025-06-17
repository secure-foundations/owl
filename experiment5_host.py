import subprocess
import json
import time
import argparse
import os
import sys
import tempfile
import threading
from prettytable import PrettyTable
import matplotlib.pyplot as plt
import numpy as np

class WireguardBenchmark:
    def __init__(self, docker_image="owlc-aeval", iperf_duration=60, ping_test=False):
        self.docker_image = docker_image
        self.iperf_duration = iperf_duration
        self.ping_test = ping_test
        self.config_dir = 'full_protocol_case_studies/implementations/wireguard'
        self.delays = ['0ms', '0.5ms', '1ms', '1.5ms', '2ms', '3ms', '4ms', '5ms', '6ms', '7ms', '8ms', '9ms', '10ms']
        self.all_results = {}
        self.network_name = "wg-benchmark-net"
        self.container1_name = "wg-benchmark-server"
        self.container2_name = "wg-benchmark-client"
        self.animation_active = False
        
        # Define the three implementations to test
        self.implementations = {
            'modified-go': {
                'name': 'Modified wireguard-go',
                'use_kernel': False,
                'binary_path': '/root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-go/wireguard-go',
                'build_commands': ['cd /root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-go && make']
            },
            'vanilla-go': {
                'name': 'Baseline wireguard-go',
                'use_kernel': False,
                'binary_path': '/root/wireguard-go/wireguard-go',
                'build_commands': ['cd /root/wireguard-go && make']
            },
            'kernel': {
                'name': 'Kernel WireGuard',
                'use_kernel': True,
                'binary_path': None,
                'build_commands': []
            }
        }

    def animate(self):
        """Simple animation to indicate progress"""
        bar_length = 20
        i = 0
        while self.animation_active:
            filled = i % (bar_length + 1)
            bar = '█' * filled + '░' * (bar_length - filled)
            sys.stdout.write(f'\r[{bar}] Running...')
            sys.stdout.flush()
            time.sleep(0.1)
            i += 1

    def start_animating(self):
        """Start a simple animation to indicate progress"""
        if not self.animation_active:
            self.animation_active = True
            self.animation_thread = threading.Thread(target=self.animate)
            self.animation_thread.start()

    def stop_animating(self):
        if self.animation_active:
            # Stop animation and clear the line
            self.animation_active = False
            time.sleep(0.2)  # Give animation thread time to stop
            sys.stdout.write('\r' + ' ' * 50 + '\r')  # Clear the animation line
            sys.stdout.flush()

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

    def docker_exec(self, container_name, cmd, check=True, capture_output=False):
        """Execute command in Docker container"""
        docker_cmd = f"docker exec {container_name} bash -c '{cmd}'"
        return self.run_command(docker_cmd, check=check, capture_output=capture_output)

    def build_implementation(self, impl_config):
        """Build a specific wireguard implementation"""
        if not impl_config['build_commands']:
            return True
        
        print(f"Building {impl_config['name']}...")
        self.start_animating()

        for build_cmd in impl_config['build_commands']:
            try:
                # Run build command in both containers
                self.docker_exec(self.container1_name, build_cmd, capture_output=True)
                self.docker_exec(self.container2_name, build_cmd, capture_output=True)
                
                # # Verify the binary was created
                # if impl_config['binary_path']:
                #     self.docker_exec(self.container1_name, f"ls -la {impl_config['binary_path']}")
                #     self.docker_exec(self.container2_name, f"ls -la {impl_config['binary_path']}")
                
            except subprocess.CalledProcessError as e:
                self.stop_animating()
                print(f"Failed to build {impl_config['name']}: {e}")
                return False
        
        self.stop_animating()
        return True

    def setup_docker_network(self):
        """Set up Docker network and containers"""
        self.start_animating()
        
        # Create Docker network
        self.run_command(f"docker network create {self.network_name} --driver bridge", check=False, capture_output=True)
        
        # Start server container with TUN device access
        server_cmd = (
            f"docker run -d --name {self.container1_name} "
            f"--network {self.network_name} "
            f"--cap-add NET_ADMIN "
            f"--cap-add SYS_MODULE "
            f"--device /dev/net/tun:/dev/net/tun "  # Add TUN device access
            f"{self.docker_image} "
            f"sleep infinity"
        )
        self.run_command(server_cmd, capture_output=True)
        
        # Start client container with TUN device access
        client_cmd = (
            f"docker run -d --name {self.container2_name} "
            f"--network {self.network_name} "
            f"--cap-add NET_ADMIN "
            f"--cap-add SYS_MODULE "
            f"--device /dev/net/tun:/dev/net/tun "  # Add TUN device access
            f"{self.docker_image} "
            f"sleep infinity"
        )
        self.run_command(client_cmd, capture_output=True)
        
        # Wait for containers to be ready
        time.sleep(3)
        
        
        # Get container IP addresses
        server_ip_result = self.run_command(
            f"docker inspect -f '{{{{range .NetworkSettings.Networks}}}}{{{{.IPAddress}}}}{{{{end}}}}' {self.container1_name}",
            capture_output=True
        )
        client_ip_result = self.run_command(
            f"docker inspect -f '{{{{range .NetworkSettings.Networks}}}}{{{{.IPAddress}}}}{{{{end}}}}' {self.container2_name}",
            capture_output=True
        )
        
        self.server_ip = server_ip_result.stdout.strip()
        self.client_ip = client_ip_result.stdout.strip()

        self.stop_animating()
        
    def setup_wireguard(self, impl_config):
        """Set up Wireguard interfaces in both containers"""
        
        if impl_config['use_kernel']:
            # Set up kernel wireguard interfaces
            self.docker_exec(self.container1_name, "ip link add wg1 type wireguard")
            self.docker_exec(self.container2_name, "ip link add wg1n type wireguard")
        else:
            # # Kill any existing wireguard processes
            # self.docker_exec(self.container1_name, "pkill -f wireguard", check=False)
            # self.docker_exec(self.container2_name, "pkill -f wireguard", check=False)
            # time.sleep(1)
            
            # Set up userspace wireguard interfaces
            env_vars = "export WG_THREADS=1 && export GOMAXPROCS=1 &&"
            
            # Start wireguard in both containers
            wg_cmd_server = f"{env_vars} {impl_config['binary_path']} wg1"
            wg_cmd_client = f"{env_vars} {impl_config['binary_path']} wg1n"
            self.docker_exec(self.container1_name, f"{wg_cmd_server}", capture_output=True)
            self.docker_exec(self.container2_name, f"{wg_cmd_client}", capture_output=True)

            # Wait for interfaces to be created
            time.sleep(1)
            
            # Check if interfaces were created (silent check)
            try:
                self.docker_exec(self.container1_name, "ip link show wg1 > /dev/null 2>&1")
            except:
                logs = self.docker_exec(self.container1_name, "cat /tmp/wg1.log", capture_output=True, check=False)
                raise Exception(f"Server wg1 interface creation failed. Log: {logs.stdout.strip()}")
            
            try:
                self.docker_exec(self.container2_name, "ip link show wg1n > /dev/null 2>&1")
            except:
                logs = self.docker_exec(self.container2_name, "cat /tmp/wg1n.log", capture_output=True, check=False)
                raise Exception(f"Client wg1n interface creation failed. Log: {logs.stdout.strip()}")
        
        # Add IP addresses to Wireguard interfaces
        self.docker_exec(self.container1_name, "ip addr add 10.100.2.1/24 dev wg1")
        self.docker_exec(self.container2_name, "ip addr add 10.100.2.2/24 dev wg1n")
        
        # Create updated configuration files with correct Docker IPs
        self.create_docker_configs()
        
        # Configure the Wireguard interfaces
        self.docker_exec(self.container1_name, "wg setconf wg1 /tmp/wg1_docker.conf")
        self.docker_exec(self.container2_name, "wg setconf wg1n /tmp/wg1n_docker.conf")
        
        # Bring up the Wireguard interfaces
        self.docker_exec(self.container1_name, "ip link set wg1 up")
        self.docker_exec(self.container2_name, "ip link set wg1n up")
        
        # Wait for interfaces to be fully up
        time.sleep(1)

    def create_docker_configs(self):
        """Create Wireguard config files with dynamically generated keys"""
        # Generate private keys
        wg1_private_result = self.docker_exec(self.container1_name, "wg genkey", capture_output=True)
        wg1n_private_result = self.docker_exec(self.container2_name, "wg genkey", capture_output=True)
        
        wg1_private_key = wg1_private_result.stdout.strip()
        wg1n_private_key = wg1n_private_result.stdout.strip()
        
        # Generate public keys from private keys
        self.docker_exec(self.container1_name, f"echo '{wg1_private_key}' > /tmp/wg1_private.key")
        self.docker_exec(self.container2_name, f"echo '{wg1n_private_key}' > /tmp/wg1n_private.key")
        
        wg1_public_result = self.docker_exec(self.container1_name, "wg pubkey < /tmp/wg1_private.key", capture_output=True)
        wg1n_public_result = self.docker_exec(self.container2_name, "wg pubkey < /tmp/wg1n_private.key", capture_output=True)
        
        wg1_public_key = wg1_public_result.stdout.strip()
        wg1n_public_key = wg1n_public_result.stdout.strip()
        
        # Use default ports
        wg1_port = "9101"
        wg1n_port = "9102"
        
        # Create server config (wg1)
        wg1_docker_config = f"""[Interface]
PrivateKey = {wg1_private_key}
ListenPort = {wg1_port}

[Peer]
PublicKey = {wg1n_public_key}
Endpoint = {self.client_ip}:{wg1n_port}
AllowedIPs = 10.100.2.2/32
"""
        
        # Create client config (wg1n)
        wg1n_docker_config = f"""[Interface]
PrivateKey = {wg1n_private_key}
ListenPort = {wg1n_port}

[Peer]
PublicKey = {wg1_public_key}
Endpoint = {self.server_ip}:{wg1_port}
AllowedIPs = 10.100.2.1/32
"""
        
        # Write configs to containers
        wg1_config_cmd = f"""cat > /tmp/wg1_docker.conf << 'EOFCONFIG'
{wg1_docker_config}EOFCONFIG"""
        
        wg1n_config_cmd = f"""cat > /tmp/wg1n_docker.conf << 'EOFCONFIG'
{wg1n_docker_config}EOFCONFIG"""
        
        self.docker_exec(self.container1_name, wg1_config_cmd)
        self.docker_exec(self.container2_name, wg1n_config_cmd)
        
        # Clean up temporary private key files
        self.docker_exec(self.container1_name, "rm -f /tmp/wg1_private.key", check=False)
        self.docker_exec(self.container2_name, "rm -f /tmp/wg1n_private.key", check=False)

    def cleanup_docker(self):
        """Clean up Docker containers and network"""
        self.stop_animating()
        print("Cleaning up...")
        
        try:
            # Stop and remove containers
            self.run_command(f"docker stop {self.container1_name} {self.container2_name}", check=False)
            self.run_command(f"docker rm {self.container1_name} {self.container2_name}", check=False)
            
            # Remove network
            self.run_command(f"docker network rm {self.network_name}", check=False)
        except Exception as e:
            print(f"Warning: Cleanup may have been incomplete: {e}")

    def configure_delay(self, delay):
        """Configure network delay between containers"""
        # Clear any existing qdisc on both containers (suppress error output)
        self.docker_exec(self.container1_name, "tc qdisc del dev eth0 root 2>/dev/null || true", check=False)
        self.docker_exec(self.container2_name, "tc qdisc del dev eth0 root 2>/dev/null || true", check=False)
        
        if delay != "0ms":
            # Set up link delay on both containers' eth0 interfaces
            self.docker_exec(self.container1_name, f"tc qdisc add dev eth0 root netem delay {delay}")
            self.docker_exec(self.container2_name, f"tc qdisc add dev eth0 root netem delay {delay}")

    def run_iperf_test(self, delay):
        """Run iperf3 test and return the result"""
        print(f"Running iperf test with delay {delay}...")
        
        # Kill any existing iperf processes
        self.docker_exec(self.container1_name, "pkill -f iperf3", check=False)
        self.docker_exec(self.container2_name, "pkill -f iperf3", check=False)
        
        time.sleep(1)
        
        if self.ping_test:
            # Test connectivity first
            print("Testing Wireguard connectivity...")
            self.start_animating()
            try:
                self.docker_exec(self.container2_name, "ping -c 3 10.100.2.1", capture_output=True)
                self.stop_animating()
                print("Wireguard connectivity confirmed")
            except subprocess.CalledProcessError as e:
                self.stop_animating()
                print("Wireguard connectivity test failed!")
                # Debug information
                print("Server wg status:")
                self.docker_exec(self.container1_name, "wg show", check=False)
                print("Client wg status:")
                self.docker_exec(self.container2_name, "wg show", check=False)
                print("Server routes:")
                self.docker_exec(self.container1_name, "ip route", check=False)
                print("Client routes:")
                self.docker_exec(self.container2_name, "ip route", check=False)
                raise Exception("Wireguard tunnel not working")
            
        # Start iperf server in server container (daemon mode, one connection)
        self.docker_exec(self.container1_name, "iperf3 -sD -1 -B 10.100.2.1")
        
        # Wait a moment for server to start
        time.sleep(1)
        
        # Verify iperf server is running
        try:
            result = self.docker_exec(self.container1_name, "pgrep -f 'iperf3.*-s'", capture_output=True)
            # print(f"iperf3 server running with PID: {result.stdout.strip()}")
        except:
            print("Warning: iperf3 server may not be running properly")
        
        # Create temporary file for iperf output in client container
        temp_filename = "/tmp/iperf_result.json"
        
        try:
            # Run iperf client in client container
            timeout_duration = self.iperf_duration + 10
            iperf_cmd = f"timeout {timeout_duration} iperf3 -c 10.100.2.1 --zerocopy --time {self.iperf_duration} --logfile {temp_filename} --json"
            print(f"Running: {iperf_cmd}")
        
            self.start_animating()
            result = self.docker_exec(self.container2_name, iperf_cmd, capture_output=True, check=False)
            self.stop_animating()

            if result.returncode == 124:  # timeout
                print(f"iperf3 test timed out after {timeout_duration} seconds")
                # Try to get partial results or error info
                error_output = self.docker_exec(self.container2_name, f"cat {temp_filename} 2>/dev/null || echo 'No output file'", capture_output=True, check=False)
                print(f"Partial output: {error_output.stdout}")
                raise Exception(f"iperf3 test timed out after {timeout_duration} seconds")
            elif result.returncode != 0:
                print(f"iperf3 failed with return code {result.returncode}")
                print(f"stderr: {result.stderr}")
                print(f"stdout: {result.stdout}")
                raise Exception(f"iperf3 failed with return code {result.returncode}")
            
            # Read the JSON output from client container
            result_cmd = f"cat {temp_filename}"
            result_output = self.docker_exec(self.container2_name, result_cmd, capture_output=True)
            
            # Parse the JSON output
            result = json.loads(result_output.stdout)
                
            # Extract bits per second from end summary
            bits_per_second = result['end']['sum_received']['bits_per_second']
            return bits_per_second
            
        finally:
            # Clean up temp file
            self.docker_exec(self.container2_name, f"rm -f {temp_filename}", check=False)

    def run_implementation_benchmark(self, impl_key, impl_config):
        """Run benchmark for a specific implementation"""
        print(f"\n{'='*60}")
        print(f"Testing {impl_config['name']}")
        print(f"{'='*60}")
        
        results = []
        
        for delay in self.delays:
            try:
                print(f"\nRunning benchmark for implementation: {impl_config['name']}, delay: {delay}")
                
                print("Setting up Docker network...")

                self.start_animating()

                # Set up Docker environment
                self.setup_docker_network()

                self.stop_animating()

                # Build the implementation if needed
                if not self.build_implementation(impl_config):
                    raise Exception(f"Failed to build {impl_config['name']}")
                
                print("Setting up Wireguard interfaces...")

                self.start_animating()

                # Set up Wireguard
                self.setup_wireguard(impl_config)
                
                # Configure delay
                self.configure_delay(delay)
                
                # Wait for network to stabilize
                time.sleep(5)
                
                self.stop_animating()

                # Run test
                bits_per_second = self.run_iperf_test(delay)
                
                # Convert to Mbps for easier reading
                mbps = bits_per_second / 1_000_000
                
                results.append({
                    'delay': delay,
                    'bits_per_second': bits_per_second,
                    'mbps': mbps
                })
                
                print(f"Delay {delay}: {mbps:.2f} Mbps")
                
            except Exception as e:
                print(f"Error testing delay {delay}: {e}")
                results.append({
                    'delay': delay,
                    'bits_per_second': 0,
                    'mbps': 0,
                    'error': str(e)
                })
            finally:
                # Always clean up
                self.cleanup_docker()
                time.sleep(2)
        
        return results

    def run_benchmark(self):
        """Run the complete benchmark suite for all implementations"""
        print("Starting Wireguard benchmark with Docker...")
        print(f"Testing {len(self.implementations)} implementations: {', '.join([impl['name'] for impl in self.implementations.values()])}")
        
        for impl_key, impl_config in self.implementations.items():
            try:
                results = self.run_implementation_benchmark(impl_key, impl_config)
                self.all_results[impl_key] = {
                    'name': impl_config['name'],
                    'results': results
                }
            except Exception as e:
                print(f"Failed to test {impl_config['name']}: {e}")
                self.all_results[impl_key] = {
                    'name': impl_config['name'],
                    'results': [],
                    'error': str(e)
                }

    def print_results(self):
        """Print results in formatted tables"""
        if not self.all_results:
            print("No results to display")
            return
        
        # Print individual tables for each implementation
        for impl_key, impl_data in self.all_results.items():
            print(f"\n{impl_data['name']} Results:")
            print("-" * 50)
            
            if 'error' in impl_data:
                print(f"ERROR: {impl_data['error']}")
                continue
                
            if not impl_data['results']:
                print("No results available")
                continue
            
            table = PrettyTable()
            table.field_names = ["Delay", "Throughput (Mbps)", "Throughput (bps)", "Status"]
            
            for result in impl_data['results']:
                if 'error' in result:
                    table.add_row([result['delay'], "ERROR", "ERROR", result['error']])
                else:
                    table.add_row([
                        result['delay'],
                        f"{result['mbps']:.2f}",
                        f"{result['bits_per_second']:,}",
                        "OK"
                    ])
            
            print(table)
        
        # Print comparison table
        self.print_comparison_table()

    def print_comparison_table(self):
        """Print a comparison table across all implementations"""
        print(f"\n{'='*80}")
        print("COMPARISON TABLE")
        print(f"{'='*80}")
        
        # Get all delays that were tested
        all_delays = set()
        for impl_data in self.all_results.values():
            if 'results' in impl_data:
                for result in impl_data['results']:
                    all_delays.add(result['delay'])
        
        all_delays = sorted(list(all_delays), key=lambda x: float(x.replace('ms', '')))
        
        # Create comparison table
        table = PrettyTable()
        field_names = ["Delay"]
        
        # Add column for each implementation
        for impl_data in self.all_results.values():
            field_names.append(f"{impl_data['name']} (Mbps)")
        
        table.field_names = field_names
        
        # Add rows for each delay
        for delay in all_delays:
            row = [delay]
            
            for impl_data in self.all_results.values():
                if 'error' in impl_data or not impl_data['results']:
                    row.append("ERROR")
                else:
                    # Find result for this delay
                    result_for_delay = None
                    for result in impl_data['results']:
                        if result['delay'] == delay:
                            result_for_delay = result
                            break
                    
                    if result_for_delay is None:
                        row.append("N/A")
                    elif 'error' in result_for_delay:
                        row.append("ERROR")
                    else:
                        row.append(f"{result_for_delay['mbps']:.2f}")
            
            table.add_row(row)
        
        print(table)

def main():
    parser = argparse.ArgumentParser(description='Benchmark all Wireguard implementations with various network delays using Docker')
    parser.add_argument('--iperf-duration', type=int, default=60, help='Duration of iperf test in seconds (default: 60)')
    parser.add_argument('--ping-test', action='store_true', help='Perform ping connectivity test before iperf')
    
    args = parser.parse_args()
    
    # Run benchmark
    benchmark = WireguardBenchmark(iperf_duration=args.iperf_duration, ping_test=args.ping_test)
    
    try:
        benchmark.run_benchmark()
        benchmark.print_results()
    except KeyboardInterrupt:
        print("\nBenchmark interrupted by user")
        benchmark.cleanup_docker()
    except Exception as e:
        print(f"Benchmark failed: {e}")
        benchmark.cleanup_docker()
        sys.exit(1)

if __name__ == "__main__":
    main()