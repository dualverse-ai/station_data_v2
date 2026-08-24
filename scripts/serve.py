#!/usr/bin/env python3
"""Serve the static archive locally with no external dependencies."""

from __future__ import annotations

import argparse
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    handler = lambda *handler_args, **kwargs: SimpleHTTPRequestHandler(  # noqa: E731
        *handler_args, directory=str(ROOT), **kwargs
    )
    server = ThreadingHTTPServer((args.host, args.port), handler)
    print(f"Station V2 archive: http://{args.host}:{args.port}/", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
