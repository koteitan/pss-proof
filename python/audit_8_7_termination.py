#!/usr/bin/env python3
"""Audit the import closure of `lean/8/8.7-termination.lean`.

Two questions, both of which cost us real time when answered by guesswork:

1. **Name collisions** — two files declaring the same `PSS.<name>` with DIFFERENT
   statements cannot be co-imported, and kimina fails SILENTLY (header poisoning,
   `trivial` becomes an unknown identifier) rather than with an error.  The main
   theorem imports both descent-props files plus the OT pillar, so its closure is
   the widest in the project.  This walks the closure and reports every duplicated
   top-level name, flagging those whose statement text differs.

2. **Residual Props** — which named `Prop`s (`FseqDesc_*`, `OTdisp_*`, `ExchV_*`,
   `Exch84_*`, `Cond*_masterCF`, `CondVI*`) are declared in the closure, and which
   of them are discharged by a `_holds` theorem somewhere in the closure.  What is
   declared-but-not-discharged is exactly what stands between us and the
   unconditional termination theorem.

    python3 python/audit_8_7_termination.py
    python3 python/audit_8_7_termination.py lean/8/8.7-termination.lean
"""
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(REPO, "lean")

IMPORT_RE = re.compile(r"^import\s+(.+?)\s*$", re.M)
# top-level declaration: not indented, not `private`
DECL_RE = re.compile(
    r"^(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([^\s:({\[]+)", re.M
)
PROP_PREFIXES = ("FseqDesc_", "OTdisp_", "ExchV_", "Exch84_", "CondI_", "CondII_",
                 "CondVI", "TransPreservesOT", "OT_B_wf", "RankSuccD1posLeg")


EXTERNAL = ("Mathlib", "Init", "Std", "Lean", "Batteries", "Aesop", "Qq", "Plausible")


def module_to_path(mod: str) -> str | None:
    """`«8».«8.7-fseq-descend»` -> lean/8/8.7-fseq-descend.lean; `PSS.Buchholz` -> lean/PSS/Buchholz.lean."""
    if mod.split(".")[0] in EXTERNAL:
        return "<external>"
    # split honouring guillemets: «8».«8.7-x» -> ['8', '8.7-x']
    raw = re.findall(r"«([^»]*)»|([A-Za-z_][A-Za-z0-9_']*)", mod)
    parts = [a or b for a, b in raw]
    cand = os.path.join(LEAN, *parts) + ".lean"
    return cand if os.path.exists(cand) else None


def closure(root: str) -> list[str]:
    seen, order, stack = set(), [], [root]
    while stack:
        f = stack.pop()
        if f in seen or f == "<external>" or not os.path.exists(f):
            continue
        seen.add(f)
        order.append(f)
        src = open(f, encoding="utf-8").read()
        # imports may only precede the first docstring/namespace; prose in a module
        # docstring can begin with the word "import" and must not be scanned
        head = re.split(r"^(/-|namespace )", src, maxsplit=1, flags=re.M)[0]
        for mod in IMPORT_RE.findall(head):
            p = module_to_path(mod)
            if p:
                stack.append(p)
            else:
                print(f"  !! {os.path.relpath(f, REPO)}: unresolved import {mod!r} "
                      f"(kimina would poison the header SILENTLY -- FIX THIS)")
    return order


def decls(path: str) -> dict[str, str]:
    """name -> statement text (decl line through the first `:=` or `by`)."""
    out = {}
    src = open(path, encoding="utf-8").read()
    for m in DECL_RE.finditer(src):
        name = m.group(2)
        tail = src[m.start():m.start() + 1200]
        cut = min((tail.find(t) for t in (":= by", ":=\n", " :=", "\nend ") if t in tail),
                  default=len(tail))
        out[name] = " ".join(tail[:cut].split())
    return out


def main() -> int:
    root = sys.argv[1] if len(sys.argv) > 1 else "lean/8/8.7-termination.lean"
    root = os.path.join(REPO, root) if not os.path.isabs(root) else root
    if not os.path.exists(root):
        print(f"audit: {root} does not exist yet")
        return 3

    files = closure(root)
    print(f"import closure of {os.path.relpath(root, REPO)}: {len(files)} files\n")

    # ---- 1. collisions -------------------------------------------------------
    where: dict[str, list[tuple[str, str]]] = {}
    for f in files:
        for name, stmt in decls(f).items():
            where.setdefault(name, []).append((os.path.relpath(f, REPO), stmt))
    bad = 0
    print("== name collisions in the closure ==")
    for name, hits in sorted(where.items()):
        if len(hits) > 1:
            stmts = {s for _, s in hits}
            tag = "DIFFERENT STATEMENTS -- LANDMINE" if len(stmts) > 1 else "same text"
            print(f"  {name}: {len(hits)}x [{tag}]")
            for f, _ in hits:
                print(f"      {f}")
            bad += len(stmts) > 1
    if not bad:
        print("  none with differing statements -- closure is co-importable")

    # ---- 2. residual Props ---------------------------------------------------
    # A Prop is a `def X : Prop := ...`.  A DISCHARGER of X is any theorem whose
    # TYPE is X (the house pattern `theorem foo : SomeProp := by ...`); its
    # dependencies are the other Props named in its binders.  A Prop is CLOSED if
    # some discharger's dependencies are all CLOSED (least fixed point).
    props = {n: hits[0][0] for n, hits in where.items()
             if n.startswith(PROP_PREFIXES) and re.match(r"def \S+\s*:\s*Prop\b", hits[0][1])}
    dischargers: dict[str, list[tuple[str, frozenset[str]]]] = {}
    for f in files:
        for name, stmt in decls(f).items():
            if not stmt.startswith(("theorem", "lemma")):
                continue
            m = re.search(r":\s*([A-Za-z_][A-Za-z0-9_'.]*)\s*$", stmt)
            if not m or m.group(1) not in props:
                continue
            target = m.group(1)
            binders = stmt[:m.start()]
            deps = frozenset(p for p in props if p != target
                             and re.search(rf"\b{re.escape(p)}\b", binders))
            dischargers.setdefault(target, []).append((name, deps))

    closed: dict[str, str] = {}
    changed = True
    while changed:
        changed = False
        for p, ds in dischargers.items():
            if p in closed:
                continue
            for name, deps in ds:
                if deps <= closed.keys():
                    closed[p] = name
                    changed = True
                    break

    print("\n== named Props in the closure ==")
    print(f"  CLOSED -- provable outright from the closure ({len(closed)}):")
    for p in sorted(closed):
        print(f"      {p:58s} <- {closed[p]}")
    open_ = sorted(set(props) - set(closed))
    leaves = [p for p in open_ if not dischargers.get(p)]
    print(f"\n  OPEN ({len(open_)}) = LEAVES ({len(leaves)}) + wired-but-not-closed "
          f"({len(open_) - len(leaves)}):")
    for p in open_:
        wiring = dischargers.get(p)
        note = "   <-- LEAF (needs a real port)"
        if wiring:
            name, deps = min(wiring, key=lambda x: len(x[1]))
            note = f"  [{name} reduces it to {len(deps)}: {', '.join(sorted(deps))}]"
        print(f"      {p:58s} {props[p]}{note}")
    print(f"\n== VERDICT ==\n  {len(leaves)} leaf Props stand between us and the "
          f"unconditional termination theorem.")
    print("  (`TerminationResidual` in lean/8/8.7-termination.lean bundles these,"
          "\n   minus `TransPreservesOT`, which that file derives from the 12 `OTdisp_*`.)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
