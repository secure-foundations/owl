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
    def __init__(self, wireguard_bin, use_owl=False, use_kernel=False, docker_image="owlc-aeval"):
        self.wireguard_bin = wireguard_bin if wireguard_bin else "/usr/bin/wireguard-go"
        self.use_owl = use_owl
        self.use_kernel = use_kernel
        self.docker_image = docker_image
        self.config_dir = 'full_protocol_case_studies/implementations/wireguard'
        self.delays = ['0ms', '0.5ms', '1ms', '1.5ms', '2ms', '3ms', '4ms', '5ms', '6ms', '7ms', '8ms', '9ms', '10ms']
        self.results = []
        self.network_name = "wg-benchmark-net"
        self.container1_name = "wg-benchmark-server"
        self.container2_name = "wg-benchmark-client"

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

    def setup_docker_network(self):
        """Set up Docker network and containers"""
        print("Setting up Docker network and containers...")
        
        # Create Docker network
        self.run_command(f"docker network create {self.network_name} --driver bridge", check=False)
        
        # Start server container
        server_cmd = (
            f"docker run -d --name {self.container1_name} "
            f"--network {self.network_name} "
            f"--cap-add NET_ADMIN "
            f"--cap-add SYS_MODULE "
            #f"--privileged "
            f"{self.docker_image} "
            f"sleep infinity"
        )
        self.run_command(server_cmd)
        
        # Start client container
        client_cmd = (
            f"docker run -d --name {self.container2_name} "
            f"--network {self.network_name} "
            f"--cap-add NET_ADMIN "
            f"--cap-add SYS_MODULE "
            #f"--privileged "
            f"{self.docker_image} "
            f"sleep infinity"
        )
        self.run_command(client_cmd)
        
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
        
        print(f"Server IP: {self.server_ip}")
        print(f"Client IP: {self.client_ip}")

    def setup_wireguard(self):
        """Set up Wireguard interfaces in both containers"""
        print("Setting up Wireguard interfaces...")
        
        if self.use_kernel:
            print("Using kernel wireguard")
            # Set up kernel wireguard interfaces
            self.docker_exec(self.container1_name, "ip link add wg1 type wireguard")
            self.docker_exec(self.container2_name, "ip link add wg1n type wireguard")
        else:
            print("Using userspace wireguard")
            # First, check if wireguard binary exists and is executable
            self.docker_exec(self.container1_name, f"ls -la {self.wireguard_bin}")
            
            # Kill any existing wireguard processes
            self.docker_exec(self.container1_name, "pkill -f wireguard", check=False)
            self.docker_exec(self.container2_name, "pkill -f wireguard", check=False)
            time.sleep(1)
            
            # Set up userspace wireguard interfaces
            env_vars = "export WG_THREADS=1 && export GOMAXPROCS=1 &&"
            
            if self.use_owl:
                print("Using owl routines")
                wg_cmd_server = f"{env_vars} {self.wireguard_bin} --owl wg1"
                wg_cmd_client = f"{env_vars} {self.wireguard_bin} --owl wg1n"
            else:
                wg_cmd_server = f"{env_vars} {self.wireguard_bin} wg1"
                wg_cmd_client = f"{env_vars} {self.wireguard_bin} wg1n"
            
            # Start wireguard processes in background and capture any errors
            print("Starting wireguard on server container...")
            result1 = self.docker_exec(self.container1_name, f"bash -c 'nohup {wg_cmd_server} > /tmp/wg1.log 2>&1 & echo $!'", capture_output=True)
            print(f"Server wireguard PID: {result1.stdout.strip()}")
            
            print("Starting wireguard on client container...")
            result2 = self.docker_exec(self.container2_name, f"bash -c 'nohup {wg_cmd_client} > /tmp/wg1n.log 2>&1 & echo $!'", capture_output=True)
            print(f"Client wireguard PID: {result2.stdout.strip()}")
            
            # Wait for interfaces to be created and check logs
            time.sleep(5)
            
            # Check if interfaces were created
            try:
                self.docker_exec(self.container1_name, "ip link show wg1")
                print("Server wg1 interface created successfully")
            except:
                print("Server wg1 interface creation failed, checking logs:")
                logs = self.docker_exec(self.container1_name, "cat /tmp/wg1.log", capture_output=True, check=False)
                print(f"Server logs: {logs.stdout}")
                raise
            
            try:
                self.docker_exec(self.container2_name, "ip link show wg1n")
                print("Client wg1n interface created successfully")
            except:
                print("Client wg1n interface creation failed, checking logs:")
                logs = self.docker_exec(self.container2_name, "cat /tmp/wg1n.log", capture_output=True, check=False)
                print(f"Client logs: {logs.stdout}")
                raise
        
        # Add IP addresses to Wireguard interfaces
        print("Adding IP addresses to Wireguard interfaces...")
        self.docker_exec(self.container1_name, "ip addr add 10.100.2.1/24 dev wg1")
        self.docker_exec(self.container2_name, "ip addr add 10.100.2.2/24 dev wg1n")
        
        # Create updated configuration files with correct Docker IPs
        print("Creating updated Wireguard configurations...")
        self.create_docker_configs()
        
        # Configure the Wireguard interfaces
        print("Configuring Wireguard interfaces...")
        self.docker_exec(self.container1_name, "wg setconf wg1 /tmp/wg1_docker.conf")
        self.docker_exec(self.container2_name, "wg setconf wg1n /tmp/wg1n_docker.conf")
        
        # Bring up the Wireguard interfaces
        print("Bringing up Wireguard interfaces...")
        self.docker_exec(self.container1_name, "ip link set wg1 up")
        self.docker_exec(self.container2_name, "ip link set wg1n up")
        
        # Wait for interfaces to be fully up and verify
        time.sleep(2)
        
        # Verify interfaces are up
        print("Verifying Wireguard setup...")
        self.docker_exec(self.container1_name, "wg show wg1")
        self.docker_exec(self.container2_name, "wg show wg1n")

    def create_docker_configs(self):
        """Create Wireguard config files with dynamically generated keys"""
        print("Generating fresh Wireguard keys...")
        
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
        
        print(f"Generated keys - Server public: {wg1_public_key}, Client public: {wg1n_public_key}")
        
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
        
        print(f"Created configs with endpoints {self.server_ip}:{wg1_port} and {self.client_ip}:{wg1n_port}")

    def cleanup_docker(self):
        """Clean up Docker containers and network"""
        print("Cleaning up Docker containers and network...")
        
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
        print(f"Configuring delay: {delay}")
        
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
        
        # Test connectivity first
        print("Testing Wireguard connectivity...")
        try:
            self.docker_exec(self.container2_name, "ping -c 3 10.100.2.1", capture_output=True)
            print("Wireguard connectivity confirmed")
        except subprocess.CalledProcessError as e:
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
        time.sleep(3)
        
        # Verify iperf server is running
        try:
            result = self.docker_exec(self.container1_name, "pgrep -f 'iperf3.*-s'", capture_output=True)
            print(f"iperf3 server running with PID: {result.stdout.strip()}")
        except:
            print("Warning: iperf3 server may not be running properly")
        
        # Create temporary file for iperf output in client container
        temp_filename = "/tmp/iperf_result.json"
        
        try:
            # Run iperf client in client container with more verbose output
            iperf_cmd = f"timeout 20 iperf3 -c 10.100.2.1 --zerocopy --time 10 --logfile {temp_filename} --json -V"
            print(f"Running: {iperf_cmd}")
            
            # Run with error capture to get better debugging info
            result = self.docker_exec(self.container2_name, iperf_cmd, capture_output=True, check=False)
            
            if result.returncode == 124:  # timeout
                print("iperf3 test timed out")
                # Try to get partial results or error info
                error_output = self.docker_exec(self.container2_name, f"cat {temp_filename} 2>/dev/null || echo 'No output file'", capture_output=True, check=False)
                print(f"Partial output: {error_output.stdout}")
                raise Exception("iperf3 test timed out")
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

    def run_benchmark(self):
        """Run the complete benchmark suite"""
        print("Starting Wireguard benchmark with Docker...")
        
        for delay in self.delays:
            try:
                # Set up Docker environment
                self.setup_docker_network()
                self.setup_wireguard()
                
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
                self.cleanup_docker()
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
    parser = argparse.ArgumentParser(description='Benchmark Wireguard performance with various network delays using Docker')
    parser.add_argument('wireguard_bin', nargs='?', help='Path to wireguard binary in container (default: /usr/bin/wireguard-go)')
    parser.add_argument('-o', '--owl', action='store_true', help='Use owl routines (for wireguard-rs)')
    parser.add_argument('-k', '--kernel', action='store_true', help='Use kernel wireguard')
    parser.add_argument('-i', '--image', default='owlc-aeval', help='Docker image to use (default: owlc-aeval)')
    
    args = parser.parse_args()
    
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
    
    # Check if Docker is available
    try:
        subprocess.run(["docker", "--version"], check=True, capture_output=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("Error: Docker is not available or not installed")
        sys.exit(1)
    
    # Run benchmark
    benchmark = WireguardBenchmark(
        args.wireguard_bin,
        use_owl=args.owl,
        use_kernel=args.kernel,
        docker_image=args.image
    )
    
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