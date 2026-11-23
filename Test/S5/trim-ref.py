#!/usr/bin/python3
"""Reference for the live byte-stream filter. LF delimits lines."""
import sys

data = sys.stdin.buffer.read()
clean = b"\n".join(line.rstrip(b" \t") for line in data.split(b"\n"))
if sys.argv[1:] == ["--check"] and clean != data:
    sys.exit(2)
sys.stdout.buffer.write(clean)
