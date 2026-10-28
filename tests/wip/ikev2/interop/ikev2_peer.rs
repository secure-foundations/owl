// Runs one party of the extracted Owl IKEv2 code (tests/wip/ikev2/full.owl)
// over stdin/stdout, for run_interop.py.
//
//   ikev2_peer (init|resp) <my_sk> <my_vk> <peer_vk> <my_id> <peer_id>
//
// Arguments are hex: RSA keys as PKCS#8 / SPKI DER, IDs as 16 bytes.
// Each message the party sends is printed as `OUT <hex>`; each message it
// receives is read from stdin as one hex line. At the end it prints
// `RESULT <spi_i> <spi_r> <esp_spi_i> <esp_spi_r> <k_i2r> <k_r2i>` or `FAIL`.
//
// This file is plain Rust: it is not verified, and it builds the ghost
// tokens the extracted code expects with Tracked::assume_new().

use extraction::*;
use std::io::{BufRead, Write};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

struct Stdio;

impl OwlEffects for Stdio {
    fn owl_output<A>(
        &mut self,
        _t: Tracked<&mut ITreeToken<A, Endpoint>>,
        x: &[u8],
        _dest_addr: Option<&str>,
        _ret_addr: &str,
    ) {
        println!("OUT {}", hex(x));
        std::io::stdout().flush().unwrap();
    }

    fn owl_input<A>(&mut self, _t: Tracked<&mut ITreeToken<A, Endpoint>>) -> (Vec<u8>, String) {
        let mut line = String::new();
        std::io::stdin().lock().read_line(&mut line).unwrap();
        (unhex(line.trim()), String::from("peer"))
    }

    fn owl_sample<'a, A>(&mut self, _t: Tracked<&mut ITreeToken<A, Endpoint>>, n: usize) -> SecretBuf<'a> {
        OwlBuf::from_vec(owl_util::gen_rand_bytes(n)).into_secret()
    }

    fn owl_output_serialize_fused<A, T: DeepView, C: Serializer<Vec<u8>, T>>(
        &mut self,
        _t: Tracked<&mut ITreeToken<A, Endpoint>>,
        _comb: C,
        _val: T,
        _dest_addr: Option<&str>,
        _ret_addr: &str,
    ) {
        unimplemented!("only used with --bufopt")
    }
}

fn reveal(k: &SecretBuf) -> String {
    hex(k.declassify(Tracked::assume_new()).as_slice())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (role, my_sk, my_vk, peer_vk, my_id, peer_id) = (
        args[1].as_str(),
        unhex(&args[2]),
        unhex(&args[3]),
        unhex(&args[4]),
        unhex(&args[5]),
        unhex(&args[6]),
    );
    // This party's ephemeral; the peer's is not known in advance (the
    // extracted code never reads it)
    let e = owl_util::gen_rand_bytes(32);
    let e_pk = owl_dhke::ecdh_dhpk(&e);
    let unknown = vec![0u8; 32];

    match role {
        "init" => {
            let cfg = cfg_Initiator {
                owl_skI: OwlBuf::from_vec(my_sk).into_secret(),
                owl_E_i: OwlBuf::from_vec(e).into_secret(),
                pk_owl_skR: OwlBuf::from_vec(peer_vk.clone()),
                pk_owl_skI: OwlBuf::from_vec(my_vk),
                pk_owl_E_r: OwlBuf::from_vec(unknown),
                pk_owl_E_i: OwlBuf::from_vec(e_pk),
            };
            let mut st = state_Initiator::init_state_Initiator();
            let r = cfg.owl_init_main(
                &mut Stdio,
                Tracked::assume_new(),
                &mut st,
                OwlBuf::from_vec(peer_vk),
                OwlBuf::from_vec(my_id),
                OwlBuf::from_vec(peer_id),
            );
            match r {
                Ok((Some(x), _)) => println!(
                    "RESULT {} {} {} {} {} {}",
                    hex(x.owl_ir_spi_i.as_slice()),
                    hex(x.owl_ir_spi_r.as_slice()),
                    hex(x.owl_ir_esp_spi_i.as_slice()),
                    hex(x.owl_ir_esp_spi_r.as_slice()),
                    reveal(&x.owl_ir_k_i2r),
                    reveal(&x.owl_ir_k_r2i)
                ),
                _ => println!("FAIL"),
            }
        }
        "resp" => {
            // get_pk_info (patched in by patch_stubs.py) looks up this ID
            std::env::set_var("IKEV2_PEER_ID", hex(&peer_id));
            let cfg = cfg_Responder {
                owl_skR: OwlBuf::from_vec(my_sk).into_secret(),
                owl_E_r: OwlBuf::from_vec(e).into_secret(),
                pk_owl_skR: OwlBuf::from_vec(my_vk),
                pk_owl_skI: OwlBuf::from_vec(peer_vk),
                pk_owl_E_r: OwlBuf::from_vec(e_pk),
                pk_owl_E_i: OwlBuf::from_vec(unknown),
            };
            let mut st = state_Responder::init_state_Responder();
            let r = cfg.owl_resp_main(&mut Stdio, Tracked::assume_new(), &mut st, OwlBuf::from_vec(my_id));
            match r {
                Ok((Some(x), _)) => println!(
                    "RESULT {} {} {} {} {} {}",
                    hex(x.owl_rr_spi_i.as_slice()),
                    hex(x.owl_rr_spi_r.as_slice()),
                    hex(x.owl_rr_esp_spi_i.as_slice()),
                    hex(x.owl_rr_esp_spi_r.as_slice()),
                    reveal(&x.owl_rr_k_i2r),
                    reveal(&x.owl_rr_k_r2i)
                ),
                _ => println!("FAIL"),
            }
        }
        _ => panic!("role must be init or resp"),
    }
    std::io::stdout().flush().unwrap();
}
