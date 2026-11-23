#!/usr/bin/python3
"""Fixture dialect: paragraphs, HTML escaping and a forward [^1] definition."""
import sys

lines = sys.stdin.read().splitlines()
note = next((line[6:] for line in lines if line.startswith("[^1]: ")), None)
for line in lines:
    if not line or line.startswith("[^1]: "):
        continue
    escaped = line.replace("&", "&amp;").replace("<", "&lt;")
    if note is not None:
        escaped = escaped.replace("[^1]", "<sup>" + note + "</sup>")
    print("<p>" + escaped + "</p>")
