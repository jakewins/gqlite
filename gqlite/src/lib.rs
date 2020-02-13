
use std::str;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int};
use std::mem::transmute;

#[repr(C)]
#[derive(Debug)]
pub struct Cursor {
    pub msg : c_int,
}

#[no_mangle]
pub extern fn gqlite_run(raw_query: *const c_char) -> *mut Cursor {
    println!("You are in gqlite");
    let query_bytes = unsafe { CStr::from_ptr(raw_query).to_bytes() };
    let query: &str = str::from_utf8(query_bytes).unwrap();
    println!("{}", query);
    return unsafe { transmute(Box::new(Cursor { msg: 1337, })) }
}

#[no_mangle]
pub extern fn gqlite_cursor_next(raw_cursor: *mut Cursor) -> c_int {
    let cursor = unsafe { &mut *raw_cursor };
    println!("{:?}.next", cursor.msg);
    return 0
}