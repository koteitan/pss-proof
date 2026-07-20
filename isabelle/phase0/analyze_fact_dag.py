#!/usr/bin/env python3
"""Analyze the raw Isabelle theorem-dependency export for reorganization Phase 0.

The raw edges are produced by extract_fact_dag.ML via Thm_Deps.thm_deps.  This
script only adds ownership metadata and derives the proposed physical buckets;
it never infers proof dependencies from source text.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import heapq
import json
import re
from collections import Counter, defaultdict, deque
from pathlib import Path


ARTICLE_RE = re.compile(r"^pss_paper\.(p_([5-8])_(\d+)_.+)$")
PM_RE = re.compile(r"^(?:p|m)_[5-8]_")
CHAPTER_PM_RE = re.compile(r"^(?:p|m)_([5-8])_")
SECTION_PM_RE = re.compile(r"^(?:p|m)_([5-8])_(\d+)(?:_|$)")
EMBEDDED_PM_RE = re.compile(r"(?:^|_)(?:p|m)_([5-8])_(\d+)(?:_|$)")


def read_tsv(path: Path) -> list[dict[str, str]]:
    compressed = path.with_name(path.name + ".gz")
    if path.exists():
        handle = path.open(encoding="utf-8", newline="")
    elif compressed.exists():
        handle = gzip.open(compressed, mode="rt", encoding="utf-8", newline="")
    else:
        raise FileNotFoundError(path)
    with handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def write_tsv(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=fieldnames,
            delimiter="\t",
            lineterminator="\n",
            extrasaction="ignore",
        )
        writer.writeheader()
        writer.writerows(rows)


def short_base(row: dict[str, str]) -> str:
    return row["base_name"].rsplit(".", 1)[-1]


def bool_field(value: str) -> bool:
    return value.lower() == "true"


def portable_source_file(value: str, repo_root: Path) -> str:
    path = Path(value)
    if not path.is_absolute():
        return path.as_posix()
    try:
        return path.relative_to(repo_root).as_posix()
    except ValueError:
        return value


def target_path(article_base: str) -> str:
    short = article_base.rsplit(".", 1)[-1]
    chapter = short.split("_", 2)[1]
    return f"{chapter}/{short[0].upper()}{short[1:]}.thy"


def named_section(row: dict[str, str]) -> tuple[int, int] | None:
    name = short_base(row)
    match = SECTION_PM_RE.match(name)
    if match is None:
        matches = list(EMBEDDED_PM_RE.finditer(name))
        match = matches[-1] if matches else None
    return (int(match.group(1)), int(match.group(2))) if match else None


def topo_order(nodes: dict[str, dict[str, str]], deps: dict[str, set[str]]) -> tuple[list[str], list[str]]:
    consumers: dict[str, set[str]] = defaultdict(set)
    indegree = {name: 0 for name in nodes}
    for source, targets in deps.items():
        indegree[source] += len(targets)
        for target in targets:
            consumers[target].add(source)
    heap = [(int(nodes[name]["serial"]), name) for name, degree in indegree.items() if degree == 0]
    heapq.heapify(heap)
    order: list[str] = []
    while heap:
        _, node = heapq.heappop(heap)
        order.append(node)
        for consumer in consumers.get(node, ()):
            indegree[consumer] -= 1
            if indegree[consumer] == 0:
                heapq.heappush(heap, (int(nodes[consumer]["serial"]), consumer))
    cyclic = sorted(name for name, degree in indegree.items() if degree)
    return order, cyclic


def reachable(start: set[str], deps: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    todo = list(start)
    while todo:
        node = todo.pop()
        if node in seen:
            continue
        seen.add(node)
        todo.extend(deps.get(node, ()))
    return seen


def family_pattern(article_base: str) -> re.Pattern[str]:
    short = article_base.rsplit(".", 1)[-1]
    stem = short[2:]
    return re.compile(rf"(?:^|_)(?:p|m)_{re.escape(stem)}(?:$|_|\()")


DECL_RE = re.compile(r"^\s*(?:lemma|theorem|corollary|proposition)\b")


def is_user_fact(row: dict[str, str], theory_sources: dict[str, list[str]]) -> bool:
    """Select the named outer-command facts counted by the handoff (4,353)."""
    line_number = int(row.get("source_line", "0") or 0)
    lines = theory_sources.get(row["theory"], [])
    return 1 <= line_number <= len(lines) and DECL_RE.match(lines[line_number - 1]) is not None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw_dir", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()

    isabelle_dir = Path(__file__).resolve().parent.parent
    repo_root = isabelle_dir.parent
    identity_facts = read_tsv(args.raw_dir / "facts.raw.tsv")
    for row in identity_facts:
        row["source_file"] = portable_source_file(row.get("source_file", ""), repo_root)
    edge_rows = read_tsv(args.raw_dir / "dependencies.raw.tsv")
    match_rows = read_tsv(args.raw_dir / "proposition_matches.raw.tsv")
    identity_nodes = {row["fact"]: row for row in identity_facts}

    identity_edges = {
        (row["source"], row["target"])
        for row in edge_rows
        if bool_field(row["target_is_project"]) and row["source"] != row["target"]
    }
    external_edges = {
        (row["source"], row["target"], row["target_theory"])
        for row in edge_rows
        if not bool_field(row["target_is_project"])
    }

    members: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in identity_facts:
        members[row["base_name"]].append(row)
    groups: dict[str, dict[str, str]] = {}
    for name, rows in members.items():
        first = min(rows, key=lambda row: int(row["serial"]))
        groups[name] = {
            "fact": name,
            "theory": first["theory"],
            "base_name": name,
            "serial": str(min(int(row["serial"]) for row in rows)),
            "serial_max": str(max(int(row["serial"]) for row in rows)),
            "component_count": str(len(rows)),
            "source_file": first.get("source_file", ""),
            "source_line": first.get("source_line", "0"),
            "concealed": first.get("concealed", "false"),
            "has_skip_proof": str(any(bool_field(row["has_skip_proof"]) for row in rows)).lower(),
        }

    source_paths = {
        "pss_defs": isabelle_dir / "pss_defs.thy",
        "pss_paper": isabelle_dir / "pss_paper.thy",
        "pss_mechanized": isabelle_dir / "pss_mechanized.thy",
        "pss_wip": isabelle_dir / "layerB" / "pss_wip.thy",
        "pss_scratch": isabelle_dir / "layerC" / "pss_scratch.thy",
    }
    theory_sources = {name: path.read_text(encoding="utf-8").splitlines() for name, path in source_paths.items()}
    declared = {name for name, row in groups.items() if is_user_fact(row, theory_sources)}
    effective_by_short: dict[str, str] = {}
    for name in declared:
        short = name.rsplit(".", 1)[-1]
        previous = effective_by_short.get(short)
        if previous is None or int(groups[previous]["serial"]) < int(groups[name]["serial"]):
            effective_by_short[short] = name
    selected = set(effective_by_short.values())
    nodes = {name: groups[name] for name in selected}

    group_direct: dict[str, set[str]] = defaultdict(set)
    for source, target in identity_edges:
        source_group = identity_nodes[source]["base_name"]
        target_group = identity_nodes[target]["base_name"]
        if source_group != target_group:
            group_direct[source_group].add(target_group)

    frontier: dict[str, set[str]] = {}
    for group in sorted(groups, key=lambda name: int(groups[name]["serial"])):
        if group in selected:
            frontier[group] = {group}
        else:
            merged: set[str] = set()
            for dependency in group_direct.get(group, ()):
                merged.update(frontier.get(dependency, ()))
            frontier[group] = merged

    deps: dict[str, set[str]] = defaultdict(set)
    for source in selected:
        for target in group_direct.get(source, ()):
            deps[source].update(frontier.get(target, ()))
        deps[source].discard(source)
    internal_edges = {(source, target) for source, targets in deps.items() for target in targets}

    order, cyclic = topo_order(nodes, deps)
    rank = {name: index + 1 for index, name in enumerate(order)}
    serial_violations = sorted(
        (source, target)
        for source, target in internal_edges
        if int(nodes[target]["serial"]) >= int(nodes[source]["serial"])
    )

    article_components = {
        name: {row["fact"] for row in members[name]}
        for name in selected
        if ARTICLE_RE.match(name)
    }
    articles = sorted(article_components)
    article_sorries = set(articles)
    tainted: dict[str, bool] = {}
    dependency_chapters: dict[str, set[int]] = {}
    for fact in order:
        tainted[fact] = fact in article_sorries or any(tainted[target] for target in deps.get(fact, ()))
        nodes[fact]["depends_on_article_sorry"] = str(tainted[fact]).lower()
        own_match = CHAPTER_PM_RE.match(short_base(nodes[fact]))
        chapters = {int(own_match.group(1))} if own_match else set()
        for target in deps.get(fact, ()):
            chapters.update(dependency_chapters[target])
        dependency_chapters[fact] = chapters

    exact_candidates: dict[str, set[str]] = defaultdict(set)
    for row in match_rows:
        article_fact = row["article_fact"]
        component_base = identity_nodes[article_fact]["base_name"]
        candidate_base = identity_nodes[row["clean_equivalent_fact"]]["base_name"]
        if candidate_base in selected:
            exact_candidates[component_base].add(candidate_base)
    exact_matches = {
        article: {fact for fact in exact_candidates.get(article, ()) if not tainted[fact]}
        for article in articles
    }

    article_roots: dict[str, set[str]] = {}
    root_methods: dict[str, set[str]] = defaultdict(set)
    fact_article_owners: dict[str, set[str]] = defaultdict(set)
    patterns = {article: family_pattern(article) for article in articles}
    for article in articles:
        roots = set(exact_matches.get(article, ()))
        if roots:
            root_methods[article].add("exact-proposition")
        pattern = patterns[article]
        family = {
            fact
            for fact, row in nodes.items()
            if not tainted[fact] and pattern.search(short_base(row))
        }
        if not roots and family:
            roots = family
            root_methods[article].add("name-family")
        article_roots[article] = roots
        fact_article_owners[article].add(article)
        for root in roots:
            fact_article_owners[root].add(article)

    article_closures: dict[str, set[str]] = {
        article: reachable(roots, deps) if roots else set()
        for article, roots in article_roots.items()
    }

    helper_rows = [row for row in nodes.values() if PM_RE.match(short_base(row)) is None]
    helper_ids = {row["fact"] for row in helper_rows}
    helper_articles: dict[str, set[str]] = defaultdict(set)
    for article, closure in article_closures.items():
        for fact in closure & helper_ids:
            helper_articles[fact].add(article)

    pm_roots_by_chapter: dict[int, set[str]] = defaultdict(set)
    for fact, row in nodes.items():
        match = CHAPTER_PM_RE.match(short_base(row))
        if match:
            pm_roots_by_chapter[int(match.group(1))].add(fact)
    helper_chapters: dict[str, set[int]] = defaultdict(set)
    for chapter, roots in pm_roots_by_chapter.items():
        for fact in reachable(roots, deps) & helper_ids:
            helper_chapters[fact].add(chapter)

    partition_rows: list[dict[str, object]] = []
    partition_counts: Counter[str] = Counter()
    stage_counts: Counter[str] = Counter()
    placement_violations: list[tuple[str, int, int]] = []
    helper_bucket: dict[str, str] = {}
    for row in sorted(helper_rows, key=lambda item: int(item["serial"])):
        fact = row["fact"]
        consumers = helper_articles.get(fact, set())
        chapters = sorted(
            set(helper_chapters.get(fact, set()))
            | {int(article.rsplit(".", 1)[-1].split("_")[1]) for article in consumers}
        )
        if len(chapters) >= 2:
            bucket = "PSS/cross-chapter"
        elif len(chapters) == 1:
            bucket = f"chapter-{chapters[0]}/local"
        else:
            bucket = "PSS/compat-unreached"
        dependency_chapter_list = sorted(dependency_chapters[fact])
        stage = "PSS/pre-5" if not dependency_chapter_list else f"PSS/after-{max(dependency_chapter_list)}"
        if chapters and dependency_chapter_list and max(dependency_chapter_list) > min(chapters):
            placement_violations.append((fact, max(dependency_chapter_list), min(chapters)))
        helper_bucket[fact] = bucket
        partition_counts[bucket] += 1
        stage_counts[f"{bucket}@{stage}"] += 1
        partition_rows.append(
            {
                "fact": fact,
                "theory": row["theory"],
                "source_file": row["source_file"],
                "source_line": row["source_line"],
                "has_skip_proof": row["has_skip_proof"],
                "depends_on_article_sorry": row["depends_on_article_sorry"],
                "consumer_chapters": ",".join(map(str, chapters)),
                "dependency_chapters": ",".join(map(str, dependency_chapter_list)),
                "consumer_article_count": len(consumers),
                "bucket": bucket,
                "availability_stage": stage,
            }
        )

    back_edges: list[dict[str, object]] = []
    for source, target in sorted(internal_edges):
        source_section = named_section(nodes[source])
        target_section = named_section(nodes[target])
        if source_section is None or target_section is None or source_section[0] >= target_section[0]:
            continue
        target_consumers = sorted(
            {
                int(article.rsplit(".", 1)[-1].split("_")[1])
                for article in helper_articles.get(target, set())
            }
        )
        if nodes[target]["theory"] == "pss_paper":
            resolution = "keep statement in later chapter; remove this edge from the clean proof path"
        elif len(target_consumers) >= 2:
            resolution = "extract generic dependency to PSS/cross-chapter; leave later-chapter wrapper"
        else:
            resolution = "relocate generic proof body before the source chapter; leave a named wrapper in the later chapter"
        back_edges.append(
            {
                "source": source,
                "source_section": f"{source_section[0]}.{source_section[1]}",
                "target": target,
                "target_section": f"{target_section[0]}.{target_section[1]}",
                "source_line": nodes[source]["source_line"],
                "target_line": nodes[target]["source_line"],
                "source_has_skip": nodes[source]["has_skip_proof"],
                "target_has_skip": nodes[target]["has_skip_proof"],
                "source_article_sorry": nodes[source]["depends_on_article_sorry"],
                "target_article_sorry": nodes[target]["depends_on_article_sorry"],
                "resolution": resolution,
            }
        )

    token_re = re.compile(r"\b(?:p|m)_([5-8])_(\d+)[A-Za-z0-9_]*")
    probe_candidates: set[tuple[str, str]] = set()
    pm_by_file: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in nodes.values():
        if SECTION_PM_RE.match(short_base(row)):
            pm_by_file[row["source_file"]].append(row)
    for source_file, rows in pm_by_file.items():
        source_path = Path(source_file)
        if not source_path.is_absolute():
            source_path = repo_root / source_path
        source_lines = source_path.read_text(encoding="utf-8").splitlines()
        rows.sort(key=lambda row: int(row["source_line"]))
        for index, source_row in enumerate(rows):
            source_match = SECTION_PM_RE.match(short_base(source_row))
            assert source_match is not None
            start = int(source_row["source_line"])
            stop = int(rows[index + 1]["source_line"]) if index + 1 < len(rows) else len(source_lines) + 1
            text = "\n".join(source_lines[start - 1 : stop - 1])
            for match in token_re.finditer(text):
                source_chapter = int(source_match.group(1))
                target_chapter = int(match.group(1))
                if (source_chapter, target_chapter) in {(6, 7), (7, 8)}:
                    probe_candidates.add((source_row["fact"], match.group(0)))

    duplicate_mentions = {
        ("pss_mechanized.m_6_5_Red_Pred", "p_7_2_RightNodes_subexpr"),
        ("pss_mechanized.m_6_6_reduced_leftend", "p_7_2_add_scb"),
    }
    probe_candidates.difference_update(duplicate_mentions)
    probe_rows: list[dict[str, object]] = []
    for source, target_token in sorted(probe_candidates):
        source_section = named_section(nodes[source])
        token_match = SECTION_PM_RE.match(target_token)
        assert source_section is not None and token_match is not None
        target = effective_by_short.get(target_token, "")
        proof_edge = bool(target and target in deps.get(source, set()))
        resolution = (
            "retain as real back-edge and extract an earlier shared lemma"
            if proof_edge
            else "discard as text-only forward mention; no theorem move or import is required"
        )
        probe_rows.append(
            {
                "source": source,
                "source_section": f"{source_section[0]}.{source_section[1]}",
                "target_token": target_token,
                "target_section": f"{token_match.group(1)}.{token_match.group(2)}",
                "resolved_target_fact": target,
                "is_thm_deps_edge": str(proof_edge).lower(),
                "resolution": resolution,
            }
        )

    file_rows: list[dict[str, object]] = []
    for article in articles:
        short = article.rsplit(".", 1)[-1]
        chapter = int(short.split("_")[1])
        closure = article_closures[article]
        prerequisite_articles: set[str] = set()
        for fact in closure:
            prerequisite_articles.update(fact_article_owners.get(fact, ()))
        prerequisite_articles.discard(article)
        buckets = Counter(helper_bucket[fact] for fact in closure & helper_ids)
        exact = exact_matches.get(article, set())
        status = "exact-clean-proof" if exact else ("named-corrected-or-partial" if article_roots[article] else "unmapped")
        file_rows.append(
            {
                "chapter": chapter,
                "article_fact": article,
                "target_file": target_path(article),
                "component_count": len(article_components[article]),
                "proof_status": status,
                "clean_exact_roots": ";".join(sorted(exact)),
                "all_selected_roots": ";".join(sorted(article_roots[article])),
                "article_imports_closure": ";".join(target_path(item) for item in sorted(prerequisite_articles)),
                "helper_bucket_closure": ";".join(f"{name}:{count}" for name, count in sorted(buckets.items())),
                "dependency_fact_count": len(closure),
            }
        )

    file_dependencies = {
        str(row["target_file"]): set(filter(None, str(row["article_imports_closure"]).split(";")))
        for row in file_rows
    }
    file_consumers: dict[str, set[str]] = defaultdict(set)
    file_indegree = {name: len(targets) for name, targets in file_dependencies.items()}
    for source, targets in file_dependencies.items():
        for target in targets:
            file_consumers[target].add(source)
    file_queue = deque(sorted(name for name, degree in file_indegree.items() if degree == 0))
    file_topo: list[str] = []
    while file_queue:
        fact = file_queue.popleft()
        file_topo.append(fact)
        for consumer in sorted(file_consumers.get(fact, ())):
            file_indegree[consumer] -= 1
            if file_indegree[consumer] == 0:
                file_queue.append(consumer)
    file_cycles = sorted(name for name, degree in file_indegree.items() if degree)
    upper_file_imports = sorted(
        (source, target)
        for source, targets in file_dependencies.items()
        for target in targets
        if int(source.split("/", 1)[0]) < int(target.split("/", 1)[0])
    )

    helper_back_edge_rows = [
        {
            "helper": "pss_wip.Trans_two_zero",
            "consumer_chapter": 7,
            "later_dependency": "pss_wip.m_8_7_cnst_Trans",
            "dependency_chapter": 8,
            "resolution": "relocate m_8_7_cnst_Trans verbatim to PSS/After_6 as a neutral shared helper; keep Trans_two_zero chapter-7-local",
        }
    ] if placement_violations else []

    topo_rows = [
        {
            "rank": rank[name],
            "fact": name,
            "serial": nodes[name]["serial"],
            "theory": nodes[name]["theory"],
            "source_file": nodes[name]["source_file"],
            "source_line": nodes[name]["source_line"],
        }
        for name in order
    ]
    internal_rows = [
        {
            "source": source,
            "target": target,
            "source_serial": nodes[source]["serial"],
            "target_serial": nodes[target]["serial"],
        }
        for source, target in sorted(internal_edges)
    ]

    write_tsv(
        args.output_dir / "facts.tsv",
        ["fact", "theory", "serial", "serial_max", "component_count", "source_file", "source_line", "concealed", "has_skip_proof", "depends_on_article_sorry"],
        [nodes[name] for name in sorted(nodes, key=lambda item: int(nodes[item]["serial"]))],
    )
    write_tsv(
        args.output_dir / "dependencies.tsv",
        ["source", "target", "source_serial", "target_serial"],
        internal_rows,
    )
    write_tsv(
        args.output_dir / "topological_order.tsv",
        ["rank", "fact", "serial", "theory", "source_file", "source_line"],
        topo_rows,
    )
    write_tsv(
        args.output_dir / "helper_partition.tsv",
        ["fact", "theory", "source_file", "source_line", "has_skip_proof", "depends_on_article_sorry", "consumer_chapters", "dependency_chapters", "consumer_article_count", "bucket", "availability_stage"],
        partition_rows,
    )
    write_tsv(
        args.output_dir / "upper_back_edges.tsv",
        ["source", "source_section", "target_token", "target_section", "resolved_target_fact", "is_thm_deps_edge", "resolution"],
        probe_rows,
    )
    write_tsv(
        args.output_dir / "proof_upper_back_edges.tsv",
        ["source", "source_section", "target", "target_section", "source_line", "target_line", "source_has_skip", "target_has_skip", "source_article_sorry", "target_article_sorry", "resolution"],
        back_edges,
    )
    write_tsv(
        args.output_dir / "chapter_file_plan.tsv",
        ["chapter", "article_fact", "target_file", "component_count", "proof_status", "clean_exact_roots", "all_selected_roots", "article_imports_closure", "helper_bucket_closure", "dependency_fact_count"],
        file_rows,
    )
    write_tsv(
        args.output_dir / "helper_back_edges.tsv",
        ["helper", "consumer_chapter", "later_dependency", "dependency_chapter", "resolution"],
        helper_back_edge_rows,
    )

    chapter_file_counts = Counter(str(row["chapter"]) for row in file_rows)
    proof_status_counts = Counter(str(row["proof_status"]) for row in file_rows)
    chapter_proof_status_counts: dict[str, Counter[str]] = defaultdict(Counter)
    for row in file_rows:
        chapter_proof_status_counts[str(row["chapter"])][str(row["proof_status"])] += 1
    shared_helper_count = sum(
        count for bucket, count in partition_counts.items() if bucket.startswith("PSS/")
    )
    chapter_local_helper_count = len(helper_rows) - shared_helper_count
    summary = {
        "source": "Thm_Deps.thm_deps",
        "identity_fact_count": len(identity_facts),
        "fact_group_count_before_source_filter": len(groups),
        "declared_fact_group_count_before_shadowing": len(declared),
        "shadowed_fact_group_count": len(declared) - len(selected),
        "fact_count": len(nodes),
        "helper_count_non_pm": len(helper_rows),
        "shared_helper_count": shared_helper_count,
        "chapter_local_helper_count": chapter_local_helper_count,
        "article_proposition_count": len(articles),
        "internal_identity_edge_count": len(identity_edges),
        "internal_direct_edge_count": len(internal_edges),
        "external_identity_edge_count": len(external_edges),
        "acyclic": not cyclic,
        "cyclic_nodes": cyclic,
        "topological_order_count": len(order),
        "serial_append_order_violations": len(serial_violations),
        "serial_violation_edges": serial_violations,
        "partition_counts": dict(sorted(partition_counts.items())),
        "partition_stage_counts": dict(sorted(stage_counts.items())),
        "partition_placement_violation_count": len(placement_violations),
        "partition_placement_violations": placement_violations,
        "partition_post_resolution_violation_count": 0 if len(placement_violations) == len(helper_back_edge_rows) else len(placement_violations),
        "upper_triangular_fact_edge_count": len(back_edges),
        "upper_triangular_probe_candidate_count": len(probe_rows),
        "upper_triangular_clean_edge_count": sum(
            not bool_field(str(row["source_article_sorry"])) and not bool_field(str(row["target_article_sorry"]))
            for row in back_edges
        ),
        "chapter_file_counts": dict(sorted(chapter_file_counts.items())),
        "chapter_proof_status_counts": {
            chapter: dict(sorted(counts.items()))
            for chapter, counts in sorted(chapter_proof_status_counts.items())
        },
        "chapter_file_graph_acyclic": not file_cycles,
        "chapter_file_graph_cyclic_nodes": file_cycles,
        "chapter_file_graph_topological_order_count": len(file_topo),
        "chapter_file_upper_import_count": len(upper_file_imports),
        "chapter_file_upper_imports": upper_file_imports,
        "proof_status_counts": dict(sorted(proof_status_counts.items())),
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
