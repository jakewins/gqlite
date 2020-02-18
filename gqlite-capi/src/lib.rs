use gqlite::{Cursor, Database, Error};
use std::any::Any;
use std::ffi::CStr;
use std::fmt::Display;
use std::fs::File;
use std::mem::transmute;
use std::os::raw::{c_char, c_int};
use std::str;

#[repr(C)]
#[derive(Debug)]
pub struct database {
    pub db: Option<Database>,
    pub last_error: Option<Error>,
}

#[repr(C)]
#[derive(Debug)]
pub struct cursor {
    cursor: Cursor,
}

fn wrap_error<T: Any + Display>(error: &T) -> Error {
    let value_any = error as &dyn Any;
    return match value_any.downcast_ref::<Error>() {
        Some(as_error) => as_error.clone(),
        None => Error { msg: format!("{}", error) }
    };
}

// Open a database file
#[no_mangle]
pub extern fn gqlite_open(raw_url: *const c_char) -> *const database {
    let url_bytes = unsafe { CStr::from_ptr(raw_url).to_bytes() };
    let url: &str = str::from_utf8(url_bytes).unwrap();

    return match File::open(url) {
        Ok(mut file) => {
            return Box::into_raw(Box::new(database { db: Some(Database::open(&mut file).unwrap()), last_error: None }));
        }
        Err(error) => {
            Box::into_raw(Box::new(database { db: None, last_error: Some(wrap_error(&error)) }))
        }
    };
}

#[no_mangle]
pub extern fn gqlite_last_error(ptr: *const database) -> i32 {
    // TODO: expose error information properly to caller
    let db = unsafe {
        assert!(!ptr.is_null());
        &*ptr
    };

    if db.last_error.is_some() {
        let e = db.last_error.as_ref().unwrap();
        println!("Error: {}", e);
        return 1;
    } else {
        return 0;
    };
}

// Close the database, free associated file handles and cursors
#[no_mangle]
pub extern fn gqlite_close(ptr: *mut database) -> c_int {
    // from https://stackoverflow.com/questions/34754036/who-is-responsible-to-free-the-memory-after-consuming-the-box/34754403
    // Need to test this actually works to deallocate
    unsafe {
        let mut db = unsafe {
            Box::from_raw(ptr)
        };
        db.db = None
    }

    return 0;
}

// Move cursor to next row
#[no_mangle]
pub extern fn gqlite_cursor_close(raw_cursor: *mut cursor) {
    let cur = unsafe {
        Box::from_raw(raw_cursor)
    };
}

// Allocate a new cursor for the specified database
#[no_mangle]
pub extern fn gqlite_cursor_new() -> *mut cursor {
    return Box::into_raw(Box::new(cursor { cursor: Cursor::new() }));
}

// Run a query, provide result in cursor
#[no_mangle]
pub extern fn gqlite_run(raw_db: *mut database, raw_cursor: *mut cursor, raw_query: *const c_char) -> c_int {
    let query_bytes = unsafe { CStr::from_ptr(raw_query).to_bytes() };
    let query: &str = str::from_utf8(query_bytes).unwrap();
    println!("Running {}", query);

    let cursor = unsafe { &mut *raw_cursor };

    let mut db = unsafe { (&mut *raw_db).db.as_mut().unwrap() };

    return match db.run(&query, &mut cursor.cursor) {
        Ok(_) => 0,
        Err(error) => {
            println!("err: {:?}", error);
            unsafe { (*raw_db).last_error = Some(wrap_error(&error)) };
            return 1;
        }
    };
}

// Move cursor to next row
#[no_mangle]
pub extern fn gqlite_cursor_next(raw_cursor: *mut cursor) -> c_int {
    let cursor = unsafe { &mut *raw_cursor };
    match cursor.cursor.next() {
        Ok(_) => return 0,
        Err(e) => {
            println!("ERR: {:?}", e);
            return 1;
        }
    }
}
