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

db = lib.gqlite_open(c_char_p("gram://miserables.gram".encode('utf-8')))
cursor = lib.gqlite_cursor_new(db)

res = lib.gqlite_run(cursor, c_char_p("MATCH (n:Note) RETURN n.message".encode('utf-8')))
print(f"{cursor}")

res = lib.gqlite_cursor_next(cursor)
print(f"cursor.next => {res}")
