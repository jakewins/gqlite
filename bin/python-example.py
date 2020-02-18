from ctypes import cdll, c_wchar_p, c_char_p, c_uint32, Structure, POINTER
from sys import platform
import os

# Create a class 'wrapper' for opaque structs from rust
class OpaqueStruct(Structure):
    pass

if platform == 'darwin':
    prefix = 'lib'
    ext = 'dylib'
elif platform == 'win32':
    prefix = ''
    ext = 'dll'
else:
    prefix = 'lib'
    ext = 'so'

# fetch the directory of this file
dir_path = os.path.dirname(os.path.realpath(__file__))
# get the parent directory (project root)
parent_dir = os.path.dirname(dir_path)

lib = cdll.LoadLibrary(parent_dir + '/target/debug/{}gqlite.{}'.format(prefix, ext))


# Declare response type for gqlite_open
lib.gqlite_open.restype = POINTER(OpaqueStruct)

db = lib.gqlite_open(c_char_p((parent_dir + "/miserables.gram").encode('utf-8')))


# Declare argument types for gqlite_last_error
lib.gqlite_last_error.argtypes = (POINTER(OpaqueStruct), )

if lib.gqlite_last_error(db) != 0:
    print("error opening db")
    os.exit(1)


# Declare response type for gqlite_cursor_new
lib.gqlite_cursor_new.restype = POINTER(OpaqueStruct)

cursor = lib.gqlite_cursor_new(db)


# Declare the argument types for gqlite_run
lib.gqlite_run.argtypes = (POINTER(OpaqueStruct), POINTER(OpaqueStruct),  c_char_p)

res = lib.gqlite_run(db, cursor, c_char_p("MATCH (n:Person) RETURN n.name".encode('utf-8')))
print(f"run => {res}")


# Declare the argument types for gqlite_cursor_next
lib.gqlite_cursor_next.argtypes = (POINTER(OpaqueStruct), )

res = lib.gqlite_cursor_next(cursor)
print(f"cursor.next => {res}")


# Declare the argument types for gqlite_close
lib.gqlite_close.argtypes = (POINTER(OpaqueStruct), )

res = lib.gqlite_close(db)
print(f"db.close => {res}")