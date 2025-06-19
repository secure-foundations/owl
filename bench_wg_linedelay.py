import subprocess
import json
import time
import argparse
import os
import sys
import tempfile
import threading
import csv
from prettytable import PrettyTable
import matplotlib.pyplot as plt
import numpy as np

ALL_IMPLEMENTATIONS = {
    'owlc-go': {
        'name': 'OwlC_V',
        'use_kernel': False,
        'binary_path': '/root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-go/wireguard-go',
        'build_commands': ['cd /root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-go && make'],
        'run_args': '',
        'env_vars': '',
        'color': 'r-',
        'marker': 's'
    },
    'baseline-go': {
        'name': 'wireguard-go',
        'use_kernel': False,
        'binary_path': '/root/wireguard-go/wireguard-go',
        'build_commands': ['cd /root/wireguard-go && make'],
        'run_args': '',
        'env_vars': '',
        'color': 'y-',
        'marker': 'x'
    },
    'kernel': {
        'name': 'wireguard-linux',
        'use_kernel': True,
        'binary_path': None,
        'build_commands': [],
        'run_args': '',
        'env_vars': '',
        'color': 'm-',
        'marker': 'D'
    },
    'baseline-rs': {
        'name': 'wireguard-rs',
        'use_kernel': False,
        'binary_path': '/root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-rs/target/release/wireguard-rs',
        'build_commands': ['cd /root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-rs && cargo build --features=nonverif-crypto --release'],
        'run_args': '',
        'env_vars': 'export WG_THREADS=1 &&',
        'color': 'y-',
        'marker': 'x'
    },
    'owlc-rs-baseline-crypto': {
        'name': 'OwlC_B',
        'use_kernel': False,
        'binary_path': '/root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-rs/target/release/wireguard-rs',
        'build_commands': ['cd /root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-rs && cargo build --features=nonverif-crypto --release'],
        'run_args': '--owl',
        'env_vars': 'export WG_THREADS=1 &&',
        'color': 'b-',
        'marker': '^'
    },
    'owlc-rs-verif-crypto': {
        'name': 'OwlC_V',
        'use_kernel': False,
        'binary_path': '/root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-rs/target/release/wireguard-rs',
        'build_commands': ['cd /root/owlc/full_protocol_case_studies/implementations/wireguard/wireguard-rs && cargo build --release'],
        'run_args': '--owl',
        'env_vars': 'export WG_THREADS=1 &&',
        'color': 'r-',
        'marker': 's'
    },
}

class WireguardBenchmark:
    def __init__(self, bench_choice, docker_image="owlc-aeval", iperf_duration=60):
        self.bench_choice = bench_choice
        self.docker_image = docker_image
        self.iperf_duration = iperf_duration
        self.config_dir = 'full_protocol_case_studies/implementations/wireguard'
        self.delays = ['0ms', '0.5ms', '1ms', '1.5ms', '2ms', '3ms', '4ms', '5ms', '6ms', '7ms', '8ms', '9ms', '10ms']
        self.all_results = {}
        self.network_name = "wg-benchmark-net"
        self.container1_name = "wg-benchmark-server"
        self.container2_name = "wg-benchmark-client"
        self.animation_active = False

        if bench_choice == 'go':
            self.implementations = {
                'owlc-go': ALL_IMPLEMENTATIONS['owlc-go'],
                'baseline-go': ALL_IMPLEMENTATIONS['baseline-go'],
                'kernel': ALL_IMPLEMENTATIONS['kernel']
            }
        elif bench_choice == 'rs':
            self.implementations = {
                'baseline-rs': ALL_IMPLEMENTATIONS['baseline-rs'],
                'owlc-rs-baseline-crypto': ALL_IMPLEMENTATIONS['owlc-rs-baseline-crypto'],
                'owlc-rs-verif-crypto': ALL_IMPLEMENTATIONS['owlc-rs-verif-crypto'],
            }
        else: 
            raise ValueError(f"Unknown benchmark choice: {bench_choice}. Must be one of: go, rs")

    def animate(self):
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
        if not self.animation_active:
            self.animation_active = True
            self.animation_thread = threading.Thread(target=self.animate)
            self.animation_thread.start()

    def stop_animating(self):
        if self.animation_active:
            self.animation_active = False
            time.sleep(0.2)
            sys.stdout.write('\r' + ' ' * 50 + '\r')
            sys.stdout.flush()

    def run_command(self, cmd, check=True, capture_output=False):
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
        docker_cmd = f"docker exec {container_name} bash -c '{cmd}'"
        return self.run_command(docker_cmd, check=check, capture_output=capture_output)

    def build_implementation(self, impl_config):
        if not impl_config['build_commands']:
            return True
        
        print(f"Building {impl_config['name']}...")
        self.start_animating()

        for build_cmd in impl_config['build_commands']:
            try:
                self.docker_exec(self.container1_name, build_cmd, capture_output=True)
                self.docker_exec(self.container2_name, build_cmd, capture_output=True)
                                
            except subprocess.CalledProcessError as e:
                self.stop_animating()
                print(f"Failed to build {impl_config['name']}: {e}")
                return False
        
        self.stop_animating()
        return True

    def setup_docker_network(self):
        self.start_animating()
        
        self.run_command(f"docker network create {self.network_name} --driver bridge", check=False, capture_output=True)
        
        server_cmd = (
            f"docker run -d --name {self.container1_name} "
            f"--network {self.network_name} "
            f"--cap-add NET_ADMIN "
            f"--device /dev/net/tun:/dev/net/tun "
            f"{self.docker_image} "
            f"sleep infinity"
        )
        self.run_command(server_cmd, capture_output=True)
        
        client_cmd = (
            f"docker run -d --name {self.container2_name} "
            f"--network {self.network_name} "
            f"--cap-add NET_ADMIN "
            f"--device /dev/net/tun:/dev/net/tun "
            f"{self.docker_image} "
            f"sleep infinity"
        )
        self.run_command(client_cmd, capture_output=True)
        
        time.sleep(3)
        
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
            self.docker_exec(self.container1_name, "ip link add wg1 type wireguard")
            self.docker_exec(self.container2_name, "ip link add wg1n type wireguard")
        else:           
            wg_cmd_server = f"{impl_config['env_vars']} {impl_config['binary_path']} {impl_config['run_args']} wg1"
            wg_cmd_client = f"{impl_config['env_vars']} {impl_config['binary_path']} {impl_config['run_args']} wg1n"
            self.docker_exec(self.container1_name, f"{wg_cmd_server}", capture_output=True)
            self.docker_exec(self.container2_name, f"{wg_cmd_client}", capture_output=True)

            time.sleep(1)
            
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
        
        self.docker_exec(self.container1_name, "ip addr add 10.100.2.1/24 dev wg1")
        self.docker_exec(self.container2_name, "ip addr add 10.100.2.2/24 dev wg1n")
        
        self.create_docker_configs()
        
        self.docker_exec(self.container1_name, "wg setconf wg1 /tmp/wg1_docker.conf")
        self.docker_exec(self.container2_name, "wg setconf wg1n /tmp/wg1n_docker.conf")
        
        self.docker_exec(self.container1_name, "ip link set wg1 up")
        self.docker_exec(self.container2_name, "ip link set wg1n up")
        
        time.sleep(1)

    def create_docker_configs(self):
        wg1_private_result = self.docker_exec(self.container1_name, "wg genkey", capture_output=True)
        wg1n_private_result = self.docker_exec(self.container2_name, "wg genkey", capture_output=True)
        
        wg1_private_key = wg1_private_result.stdout.strip()
        wg1n_private_key = wg1n_private_result.stdout.strip()
        
        self.docker_exec(self.container1_name, f"echo '{wg1_private_key}' > /tmp/wg1_private.key")
        self.docker_exec(self.container2_name, f"echo '{wg1n_private_key}' > /tmp/wg1n_private.key")
        
        wg1_public_result = self.docker_exec(self.container1_name, "wg pubkey < /tmp/wg1_private.key", capture_output=True)
        wg1n_public_result = self.docker_exec(self.container2_name, "wg pubkey < /tmp/wg1n_private.key", capture_output=True)
        
        wg1_public_key = wg1_public_result.stdout.strip()
        wg1n_public_key = wg1n_public_result.stdout.strip()
        
        wg1_port = "9101"
        wg1n_port = "9102"
        
        wg1_docker_config = f"""[Interface]
PrivateKey = {wg1_private_key}
ListenPort = {wg1_port}

[Peer]
PublicKey = {wg1n_public_key}
Endpoint = {self.client_ip}:{wg1n_port}
AllowedIPs = 10.100.2.2/32
"""
        
        wg1n_docker_config = f"""[Interface]
PrivateKey = {wg1n_private_key}
ListenPort = {wg1n_port}

[Peer]
PublicKey = {wg1_public_key}
Endpoint = {self.server_ip}:{wg1_port}
AllowedIPs = 10.100.2.1/32
"""
        
        wg1_config_cmd = f"""cat > /tmp/wg1_docker.conf << 'EOFCONFIG'
{wg1_docker_config}EOFCONFIG"""
        
        wg1n_config_cmd = f"""cat > /tmp/wg1n_docker.conf << 'EOFCONFIG'
{wg1n_docker_config}EOFCONFIG"""
        
        self.docker_exec(self.container1_name, wg1_config_cmd)
        self.docker_exec(self.container2_name, wg1n_config_cmd)
        
        self.docker_exec(self.container1_name, "rm -f /tmp/wg1_private.key", check=False)
        self.docker_exec(self.container2_name, "rm -f /tmp/wg1n_private.key", check=False)

    def cleanup_docker(self):
        self.stop_animating()
        print("Cleaning up...")
        
        try:
            self.run_command(f"docker stop {self.container1_name} {self.container2_name}", check=False)
            self.run_command(f"docker rm {self.container1_name} {self.container2_name}", check=False)
            
            self.run_command(f"docker network rm {self.network_name}", check=False)
        except Exception as e:
            print(f"Warning: Cleanup may have been incomplete: {e}")

    def configure_delay(self, delay):
        self.docker_exec(self.container1_name, "tc qdisc del dev eth0 root 2>/dev/null || true", check=False)
        self.docker_exec(self.container2_name, "tc qdisc del dev eth0 root 2>/dev/null || true", check=False)
        
        if delay != "0ms":
            self.docker_exec(self.container1_name, f"tc qdisc add dev eth0 root netem delay {delay}")
            self.docker_exec(self.container2_name, f"tc qdisc add dev eth0 root netem delay {delay}")

    def setup_for_implementation(self, impl_config):
        print("Setting up Docker network...")
        self.start_animating()
        self.setup_docker_network()
        self.stop_animating()

        if not self.build_implementation(impl_config):
            raise Exception(f"Failed to build {impl_config['name']}")
        
        print("Setting up Wireguard interfaces...")
        self.start_animating()
        self.setup_wireguard(impl_config)
        time.sleep(1)
        self.stop_animating()
        
    def run_iperf_test(self, delay):
        self.start_animating()
        self.docker_exec(self.container1_name, "pkill -f iperf3", check=False)
        self.docker_exec(self.container2_name, "pkill -f iperf3", check=False)
        time.sleep(0.5)

        self.docker_exec(self.container1_name, "iperf3 -sD -1 -B 10.100.2.1")
        time.sleep(1)
        self.stop_animating()
        
        temp_filename = "/tmp/iperf_result.json"
        
        try:
            timeout_duration = self.iperf_duration + 10
            iperf_cmd = f"timeout {timeout_duration} iperf3 -c 10.100.2.1 --zerocopy --time {self.iperf_duration} --logfile {temp_filename} --json"
            
            self.start_animating()
            result = self.docker_exec(self.container2_name, iperf_cmd, capture_output=True, check=False)
            self.stop_animating()

            if result.returncode == 124:  # iperf timeout
                print(f"iperf3 test timed out after {timeout_duration} seconds")
                raise TimeoutError(f"iperf3 test timed out after {timeout_duration} seconds")
            elif result.returncode != 0:
                print(f"iperf3 failed with return code {result.returncode}")
                print(f"stderr: {result.stderr}")
                print(f"stdout: {result.stdout}")
                raise Exception(f"iperf3 failed with return code {result.returncode}")
            
            result_cmd = f"cat {temp_filename}"
            result_output = self.docker_exec(self.container2_name, result_cmd, capture_output=True)
            result = json.loads(result_output.stdout)
            bits_per_second = result['end']['sum_received']['bits_per_second']
            return bits_per_second
            
        finally:
            self.docker_exec(self.container2_name, f"rm -f {temp_filename}", check=False)

    def run_implementation_benchmark(self, impl_config):
        print(f"\n{'='*60}")
        print(f"Testing {impl_config['name']}")
        print(f"{'='*60}")
        
        results = []
        
        try:            
            print(f"\nRunning benchmark for implementation: {impl_config['name']}")
            
            self.setup_for_implementation(impl_config)
           
            for delay in self.delays:
                max_attempts = 2
                attempt = 1

                while attempt <= max_attempts:
                    try:
                        print(f"\nTesting delay: {delay}")
                        self.start_animating()
                        self.configure_delay(delay)
                        time.sleep(1)
                        self.stop_animating()
                        
                        bits_per_second = self.run_iperf_test(delay)
                        
                        mbps = bits_per_second / 1_000_000
                        
                        results.append({
                            'delay': delay,
                            'mbps': mbps
                        })

                        print(f"Delay {delay}: {mbps:.2f} Mbps")
                        
                        break

                    except TimeoutError as e:
                        print(f"Attempt {attempt} failed with timeout for delay {delay}: {e}")

                        if attempt < max_attempts:
                            print("Cleaning up and retrying...")
                            self.cleanup_docker()
                            time.sleep(2)
                            
                            try:
                                self.setup_for_implementation(impl_config)
                                attempt += 1
                                print(f"Retrying delay {delay} test (attempt {attempt})...")
                            except Exception as setup_error:
                                print(f"Failed to set up for retry: {setup_error}")
                                results.append({
                                    'delay': delay,
                                    'mbps': 0,
                                    'error': f"Setup failed on retry: {str(setup_error)}"
                                })
                                break

                    except Exception as e:
                        self.stop_animating()
                        print(f"Error testing delay {delay}: {e}")
                        results.append({
                            'delay': delay,
                            'mbps': 0,
                            'error': str(e)
                        })
        
        except Exception as e:
            print(f"Failed to set up {impl_config['name']}: {e}")
            return [{
                'delay': delay,
                'mbps': 0,
                'error': str(e)
            } for delay in self.delays]
        
        finally:
            self.cleanup_docker()
            time.sleep(1)
        
        return results

    def run_benchmark(self):
        print(f"Testing {len(self.implementations)} implementations: {', '.join([impl['name'] for impl in self.implementations.values()])}")
        
        for impl_key, impl_config in self.implementations.items():
            try:
                results = self.run_implementation_benchmark(impl_config)
                self.all_results[impl_key] = {
                    'name': impl_config['name'],
                    'results': results,
                    'color': impl_config['color'],
                    'marker': impl_config['marker']
                }
            except Exception as e:
                print(f"Failed to test {impl_config['name']}: {e}")
                self.all_results[impl_key] = {
                    'name': impl_config['name'],
                    'results': [],
                    'error': str(e)
                }

    def save_csv(self):
        filename = f"bench_wg_linedelay-{self.bench_choice}.csv"
        
        all_delays = set()
        for impl_data in self.all_results.values():
            if 'results' in impl_data:
                for result in impl_data['results']:
                    all_delays.add(result['delay'])
        
        all_delays = sorted(list(all_delays), key=lambda x: float(x.replace('ms', '')))
        
        with open(filename, 'w', newline='') as csvfile:
            fieldnames = ['Delay_ms']
            for impl_data in self.all_results.values():
                if 'error' not in impl_data:
                    fieldnames.append(f"{impl_data['name']}_Gbps")
            
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            
            for delay in all_delays:
                row = {'Delay_ms': float(delay.replace('ms', ''))}
                
                for impl_data in self.all_results.values():
                    if 'error' in impl_data or not impl_data['results']:
                        continue
                    result_for_delay = None
                    for result in impl_data['results']:
                        if result['delay'] == delay:
                            result_for_delay = result
                            break                    
                    col_name = f"{impl_data['name']}_Gbps"
                    if result_for_delay is None or 'error' in result_for_delay:
                        row[col_name] = None
                    else:
                        row[col_name] = result_for_delay['mbps'] / 1000.0
                
                writer.writerow(row)
        
        print(f"Results saved to {filename}")

    def mk_comparison_table(self):
        all_delays = set()
        for impl_data in self.all_results.values():
            if 'results' in impl_data:
                for result in impl_data['results']:
                    all_delays.add(result['delay'])
        
        all_delays = sorted(list(all_delays), key=lambda x: float(x.replace('ms', '')))
        
        table = PrettyTable()
        field_names = ["Delay"]
        
        for impl_data in self.all_results.values():
            field_names.append(f"{impl_data['name']} (Mbps)")
        
        table.field_names = field_names
        
        for delay in all_delays:
            row = [delay]
            
            for impl_data in self.all_results.values():
                if 'error' in impl_data or not impl_data['results']:
                    row.append("ERROR")
                else:
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
        
        return table

    def save_txt(self):
        filename = f"bench_wg_linedelay-{self.bench_choice}.txt"
        
        with open(filename, 'w') as f:
            f.write("WIREGUARD BENCHMARK RESULTS\n")
            f.write("=" * 80 + "\n\n")
            table = self.mk_comparison_table()
            f.write(str(table) + "\n")
        
        print(f"Formatted tables saved to {filename}")

    def generate_graph(self):
        if not self.all_results:
            print("No results to plot")
            return
        
        plt.figure(figsize=(12, 8))
        plt.style.use('default')
        
        all_delays = set()
        for impl_data in self.all_results.values():
            if 'results' in impl_data and 'error' not in impl_data:
                for result in impl_data['results']:
                    all_delays.add(result['delay'])
        
        all_delays = sorted(list(all_delays), key=lambda x: float(x.replace('ms', '')))
        delay_values = [float(d.replace('ms', '')) for d in all_delays]
                
        for i, (_impl_key, impl_data) in enumerate(self.all_results.items()):
            if 'error' in impl_data or not impl_data['results']:
                continue

            throughput_gbps = []
            plot_delays = []
            
            for delay in all_delays:
                result_for_delay = None
                for result in impl_data['results']:
                    if result['delay'] == delay:
                        result_for_delay = result
                        break
                
                if result_for_delay is not None and 'error' not in result_for_delay:
                    throughput_gbps.append(result_for_delay['mbps'] / 1000.0)
                    plot_delays.append(float(delay.replace('ms', '')))

            if throughput_gbps:
                plt.plot(plot_delays, throughput_gbps, impl_data['color'],
                        marker=impl_data['marker'], linewidth=2, markersize=8,
                        label=impl_data['name'])
        
        plt.xlabel('Network Delay (ms)', fontsize=12)
        plt.ylabel('Throughput (Gbps)', fontsize=12)
        plt.title(f'WireGuard Performance vs Network Delay ({self.bench_choice.upper()})', fontsize=14, fontweight='bold')
        plt.grid(True, alpha=0.3)
        plt.legend(fontsize=10, loc='best')
        
        if delay_values:
            plt.xlim(0, 10)
        y_min, y_max = plt.ylim()
        plt.ylim(0, y_max * 1.05)
        
        plt.tight_layout()
        
        pdf_filename = f"bench_wg_linedelay-{self.bench_choice}.pdf"
        plt.savefig(pdf_filename, format='pdf', dpi=300, bbox_inches='tight')
        print(f"Graph saved as {pdf_filename}")
        
        png_filename = f"bench_wg_linedelay-{self.bench_choice}.png"
        plt.savefig(png_filename, format='png', dpi=300, bbox_inches='tight')
        print(f"Graph saved as {png_filename}")
        
        plt.close()

    def print_results(self):
        if not self.all_results:
            print("No results to display")
            return
        
        print(f"\n{'='*80}")
        print("BENCHMARK RESULTS")
        print(f"{'='*80}")
        table = self.mk_comparison_table()
        print(table)

    def save_all_outputs(self):
        print(f"\n{'='*60}")
        print("SAVING OUTPUT FILES")
        print(f"{'='*60}")
        
        try:
            self.save_csv()
        except Exception as e:
            print(f"Error saving CSV: {e}")
        
        try:
            self.save_txt()
        except Exception as e:
            print(f"Error saving TXT: {e}")
        
        try:
            self.generate_graph()
        except Exception as e:
            print(f"Error generating graph: {e}")

def main():
    parser = argparse.ArgumentParser(description='Benchmark Wireguard implementations on synthetic Docker network with varying network delays')
    parser.add_argument('--iperf-duration', type=int, default=60, help='Duration of iperf test in seconds (default: 60)')
    parser.add_argument('--bench-choice', choices=['go', 'rs'], required=True, help='Which benchmark to run')
    args = parser.parse_args()
    
    benchmark = WireguardBenchmark(args.bench_choice, iperf_duration=args.iperf_duration)
    
    try:
        benchmark.run_benchmark()
        benchmark.print_results()
        benchmark.save_all_outputs()
    except KeyboardInterrupt:
        print("\nBenchmark interrupted by user")
        benchmark.cleanup_docker()
    except Exception as e:
        print(f"Benchmark failed: {e}")
        benchmark.cleanup_docker()
        sys.exit(1)

if __name__ == "__main__":
    main()