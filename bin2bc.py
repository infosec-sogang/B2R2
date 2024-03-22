#!/usr/bin/python3
import sys, os


def convert_to_bc(buf):
    if len(buf) % 2 == 1:
        print("Odd-length input provided")
        exit(1)

    i = 0
    bc = b""
    while i < len(buf):
        bc += bytes([int(buf[i:i+2], 16)])
        i += 2
    return bc

if len(sys.argv) != 2:
    print("Usage: %s <directory of bin files>" % sys.argv[0])
    exit(1)

for file in os.listdir(sys.argv[1]):
    if not file.endswith(".bin"):
        continue

    print(file)
    f = open(os.path.join(sys.argv[1], file), "r")
    buf = f.read()
    f.close()

    bc = convert_to_bc(buf)

    new_file = file.replace(".bin", ".bc")
    f = open(os.path.join(sys.argv[1], new_file), "wb")
    f.write(bc)
    f.close()
