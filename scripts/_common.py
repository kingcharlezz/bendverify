"""Shared helpers for the command-line tools. TRUSTED (part of the verifier group)."""
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(ROOT, "trusted", "verifier"))
sys.path.insert(0, os.path.join(ROOT, "trusted", "benchmark"))


def banner(lines):
    w = max(len(k) for k, _ in lines)
    for k, v in lines:
        print(f"{(k + ':').ljust(w + 1)} {v}")
