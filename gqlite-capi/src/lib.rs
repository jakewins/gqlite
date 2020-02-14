use std::str;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int};
use std::mem::transmute;

#[repr(C)]
#[derive(Debug)]
pub struct database {
    pub msg : c_int,
}

#[repr(C)]
#[derive(Debug)]
pub struct cursor {
    pub msg : c_int,
}

// Open a database file
#[no_mangle]
pub extern fn gqlite_open(raw_url: *const c_char) -> *mut database {
    let url_bytes = unsafe { CStr::from_ptr(raw_url).to_bytes() };
    let url: &str = str::from_utf8(url_bytes).unwrap();
    println!("opening {}", url);
    return unsafe { transmute(Box::new(database { msg: 1337, })) }
}

// Close the database, free associated file handles and cursors
#[no_mangle]
pub extern fn gqlite_close(db: *mut database) -> c_int {
    // from https://stackoverflow.com/questions/34754036/who-is-responsible-to-free-the-memory-after-consuming-the-box/34754403
    // Need to test this actually works to deallocate
    let owned_db = unsafe { Box::from_raw(db) };
    return 0
}

// Allocate a new cursor for the specified database
#[no_mangle]
pub extern fn gqlite_cursor_new(db: *mut database) -> *mut cursor {
    return unsafe { transmute(Box::new(cursor { msg: 1337, })) }
}

// Run a query, optionally provide result in cursor
#[no_mangle]
pub extern fn gqlite_run(raw_cursor: *mut cursor, raw_query: *const c_char) -> c_int {
    println!("You are in gqlite");
    let query_bytes = unsafe { CStr::from_ptr(raw_query).to_bytes() };
    let query: &str = str::from_utf8(query_bytes).unwrap();
    println!("{}", query);
    return 0
}

// Move cursor to next row
#[no_mangle]
pub extern fn gqlite_cursor_next(raw_cursor: *mut cursor) -> c_int {
    let cursor = unsafe { &mut *raw_cursor };
    println!("{:?}.next", cursor.msg);
    return 0
}
