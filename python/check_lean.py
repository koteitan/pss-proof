#!/usr/bin/env python3
"""Verify a Lean file (or a snippet on stdin) through kimina-lean-server.

    python3 python/check_lean.py lean/7/7.2-scb-unique.lean
    cat snippet.lean | python3 python/check_lean.py -

Exit code
    0  clean      : no error, no `sorry`  -> the file is ✅
    1  sorry      : no error, but `sorry`/`sorryAx` remains  -> still 🚨
    2  error      : Lean rejected it      -> still 🚨
    3  infra      : server unreachable / REPL failed to start (NOT a proof verdict)

The server is expected to be running (see lean/kimina.md).  Port and host are read
from kimina-lean-server/.env, so nothing machine-specific is hard-coded here.
"""
import json
import os
import sys
import urllib.error
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENV = os.path.join(os.path.dirname(REPO), "kimina-lean-server", ".env")


def server_url() -> str:
    host, port = "localhost", None
    if os.path.exists(ENV):
        for line in open(ENV, encoding="utf-8"):
            line = line.strip()
            if line.startswith("LEAN_SERVER_PORT="):
                port = line.split("=", 1)[1].strip()
            elif line.startswith("LEAN_SERVER_HOST="):
                host = line.split("=", 1)[1].strip() or host
    port = os.environ.get("LEAN_SERVER_PORT", port)
    if not port:
        sys.exit("check_lean: no LEAN_SERVER_PORT (set it in kimina-lean-server/.env)")
    return f"http://{host}:{port}/api/check"


def check(code: str, ident: str) -> dict:
    # Large chapter files can take longer than kimina's 30-second API default
    # even though the same file builds normally with Lake.  Keep the HTTP
    # timeout and the server-side Lean command timeout in the same regime.
    body = json.dumps({
        "snippets": [{"id": ident, "code": code}],
        "timeout": 300,
    }).encode()
    req = urllib.request.Request(
        server_url(), data=body, headers={"Content-Type": "application/json"}
    )
    try:
        with urllib.request.urlopen(req, timeout=1800) as r:
            return json.loads(r.read())
    except urllib.error.URLError as e:
        print(f"INFRA: cannot reach kimina at {server_url()}: {e}", file=sys.stderr)
        print("       start it:  cd ~/proofs/pss-proof/kimina-lean-server && "
              "nohup .venv/bin/python -m server > /tmp/kimina-pss.log 2>&1 &",
              file=sys.stderr)
        sys.exit(3)


def main() -> int:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    path = sys.argv[1]
    code = sys.stdin.read() if path == "-" else open(path, encoding="utf-8").read()

    resp = check(code, os.path.basename(path))
    results = resp.get("results") or []
    if not results:
        print("INFRA: empty response:", json.dumps(resp)[:400], file=sys.stderr)
        return 3

    res = results[0]
    if res.get("error"):
        print(f"INFRA: REPL error: {res['error']}", file=sys.stderr)
        return 3

    diag = (res.get("response") or {}).get("messages") or []
    errors = [m for m in diag if m.get("severity") == "error"]
    # `sorry` shows up as a warning ("declaration uses 'sorry'"), which is exactly the
    # thing a green build does NOT catch.  Treat it as failure, not as noise.
    sorries = [m for m in diag if "sorry" in (m.get("data") or "").lower()]

    for m in diag:
        pos = m.get("pos") or {}
        print(f"[{m.get('severity')}] line {pos.get('line')}: {m.get('data')}")

    if errors:
        print(f"\nERROR  {path}: {len(errors)} error(s)")
        return 2
    if sorries:
        print(f"\nSORRY  {path}: {len(sorries)} declaration(s) still use sorry")
        return 1
    print(f"\nOK     {path}: no errors, no sorry")
    return 0


if __name__ == "__main__":
    sys.exit(main())
