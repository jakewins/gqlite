use lazy_static::lazy_static;
use std::cell::RefCell;

use std::str;
use std::ffi::CStr;
use std::os::raw::{c_char, c_int};
use std::mem::transmute;
use gqlite::{Database, Cursor};
use std::borrow::BorrowMut;

#[repr(C)]
#[derive(Debug)]
pub struct database {
    db: Database,
}

#[repr(C)]
#[derive(Debug)]
pub struct cursor {
    cursor: Cursor,
}

// Open a database file
#[no_mangle]
pub extern fn gqlite_open(raw_url: *const c_char) -> *mut database {
    let url_bytes = unsafe { CStr::from_ptr(raw_url).to_bytes() };
    let url: &str = str::from_utf8(url_bytes).unwrap();
    return unsafe { transmute(Box::new(database { db: Database::open(url).unwrap() })) }
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
pub extern fn gqlite_cursor_new() -> *mut cursor {
    return unsafe { transmute(Box::new(cursor { cursor: Cursor::new(), })) }
}

// Run a query, provide result in cursor
#[no_mangle]
pub extern fn gqlite_run(raw_db: *mut database, raw_cursor: *mut cursor, raw_query: *const c_char) -> c_int {
    let query_bytes = unsafe { CStr::from_ptr(raw_query).to_bytes() };
    let query: &str = str::from_utf8(query_bytes).unwrap();
    println!("Running {}", query);

    let mut cursor = unsafe { &mut *raw_cursor };
    let mut db = unsafe { &mut *raw_db };

    let mut result = db.db.run(memory_leak(query), &mut cursor.cursor);
    if let Ok(_) = result {
        return 0
    }

    println!("err: {:?}", result);
    return 1
}

// TODO lol
fn memory_leak(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

// Move cursor to next row
#[no_mangle]
pub extern fn gqlite_cursor_next(raw_cursor: *mut cursor) -> c_int {
    let mut cursor = unsafe { &mut *raw_cursor };
    match cursor.cursor.next() {
        Ok(_) => return 0,
        Err(e) => {
            println!("ERR: {:?}", e);
            return 1
        }
    }
}
