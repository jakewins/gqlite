from ctypes import cdll, c_wchar_p, c_char_p
from sys import platform

if platform == 'darwin':
    prefix = 'lib'
    ext = 'dylib'
elif platform == 'win32':
    prefix = ''
    ext = 'dll'
else:
    prefix = 'lib'
    ext = 'so'

lib = cdll.LoadLibrary('/home/jake/Code/toy/graf/target/debug/{}gqlite.{}'.format(prefix, ext))

db = lib.gqlite_open(c_char_p("/home/jake/Code/toy/graf/miserables.gram".encode('utf-8')))
cursor = lib.gqlite_cursor_new(db)

res = lib.gqlite_run(db, cursor, c_char_p("MATCH (n:Person) RETURN n.name".encode('utf-8')))
print(f"run => {res}")

res = lib.gqlite_cursor_next(cursor)
print(f"cursor.next => {res}")

res = lib.gqlite_close(db)
print(f"db.close => {res}")