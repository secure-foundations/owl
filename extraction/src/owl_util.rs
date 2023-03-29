use rand::{distributions::Uniform, Rng};

pub fn gen_rand_bytes(len: usize) -> Vec<u8> {
    let range = Uniform::from(0..u8::MAX);
    rand::thread_rng().sample_iter(&range).take(len).collect()
}
