// If the documentation is available, we should warn on this (remove the next line and this comment)
#![allow(clippy::missing_safety_doc)]

use gqlite::{Cursor, Database, Error, GramCursor, GramDatabase};
use std::ffi::CStr;
use std::fs::File;
use std::os::raw::{c_char, c_int};
use std::str;

#[repr(C)]
#[derive(Debug)]
pub struct database {
    pub db: Option<GramDatabase>,
    pub last_error: Option<Error>,
}

#[repr(C)]
#[derive(Debug)]
pub struct cursor {
    cursor: GramCursor,
}

// Open a database file
#[no_mangle]
pub unsafe extern "C" fn gqlite_open(raw_url: *const c_char) -> *const database {
    let url_bytes = CStr::from_ptr(raw_url).to_bytes();
    let url: &str = str::from_utf8(url_bytes).unwrap();

    match File::open(url) {
        Ok(file) => Box::into_raw(Box::new(database {
            db: Some(Database::open(file).unwrap()),
            last_error: None,
        })),
        Err(error) => Box::into_raw(Box::new(database {
            db: None,
            last_error: Some(error.into()),
        })),
    }
}

#[no_mangle]
pub unsafe extern "C" fn gqlite_last_error(ptr: *const database) -> i32 {
    // TODO: expose error information properly to caller
    let db = {
        assert!(!ptr.is_null());
        &*ptr
    };

    if db.last_error.is_some() {
        let e = db.last_error.as_ref().unwrap();
        println!("Error: {}", e);
        1
    } else {
        0
    }
}

// Close the database, free associated file handles and cursors
#[no_mangle]
pub unsafe extern "C" fn gqlite_close(ptr: *mut database) -> c_int {
    // from https://stackoverflow.com/questions/34754036/who-is-responsible-to-free-the-memory-after-consuming-the-box/34754403
    // Need to test this actually works to deallocate
    let mut db = Box::from_raw(ptr);
    db.db = None;

    0
}

// Move cursor to next row
#[no_mangle]
pub unsafe extern "C" fn gqlite_cursor_close(raw_cursor: *mut cursor) {
    let _cur = Box::from_raw(raw_cursor);
}

// Allocate a new cursor for the specified database
#[no_mangle]
pub extern "C" fn gqlite_cursor_new() -> *mut cursor {
    Box::into_raw(Box::new(cursor {
        cursor: Cursor::new(),
    }))
}

// Run a query, provide result in cursor
#[no_mangle]
pub unsafe extern "C" fn gqlite_run(
    raw_db: *mut database,
    raw_cursor: *mut cursor,
    raw_query: *const c_char,
) -> c_int {
    let query_bytes = CStr::from_ptr(raw_query).to_bytes();
    let query: &str = str::from_utf8(query_bytes).unwrap();
    println!("Running {}", query);

    let cursor = &mut *raw_cursor;
    let db = (*raw_db).db.as_mut().unwrap();

    match db.run(&query, &mut cursor.cursor) {
        Ok(_) => 0,
        Err(error) => {
            println!("err: {:?}", error);
            (*raw_db).last_error = Some(error);
            1
        }
    }
}

// Move cursor to next row
#[no_mangle]
pub unsafe extern "C" fn gqlite_cursor_next(raw_cursor: *mut cursor) -> c_int {
    let cursor = &mut *raw_cursor;
    match cursor.cursor.next() {
        Ok(_) => 0,
        Err(e) => {
            println!("ERR: {:?}", e);
            1
        }
    }
}
