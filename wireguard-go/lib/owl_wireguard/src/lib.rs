use std::ffi::CStr;
use std::{thread, time};

#[no_mangle]
pub extern "C" fn test(name: *const libc::c_char) {
    let name_cstr = unsafe { CStr::from_ptr(name) };
    let name = name_cstr.to_str().unwrap();
    println!("Hello {}!", name);
    let t = time::Duration::from_millis(100);
    thread::sleep(t);
}