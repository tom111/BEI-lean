#!/usr/bin/env python3
"""Generate repository statistics for the public docs.

This script reads tracked Lean files and git history, then writes a JSON data
file consumed by the Jekyll homepage at `docs/_data/repo_stats.json`.
"""

from __future__ import annotations

import json
import subprocess
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
OUTPUT_PATH = REPO_ROOT / "docs" / "_data" / "repo_stats.json"
LEAN_LINE_CACHE: dict[str, int] = {}

MILESTONES: list[dict[str, str]] = [
    {
        "date": "2026-03-09",
        "title": "Theorem 1.1",
        "description": "Closed graphs characterised by a quadratic Gröbner basis.",
        "note": "The bulk of the work that followed went into Theorem 2.1, which required importing substantial Gröbner-basis infrastructure from a Mathlib pull request.",
    },
    {
        "date": "2026-03-29",
        "title": "Theorem 3.2 and Corollary 2.2",
        "description": "Prime decomposition of J_G and radicality.",
    },
    {
        "date": "2026-04-06",
        "title": "Section 4 bridge",
        "description": "Conditional independence ideals identified with binomial edge ideals.",
        "note": "Closing Proposition 1.6 then required porting and extending a large amount of Cohen–Macaulay machinery into the project — the costliest infrastructure work of the formalisation.",
    },
    {
        "date": "2026-05-02",
        "title": "Proof complete; refactor begins",
        "description": "All paper results (Sections 1–4) axiom-clean — including Proposition 1.6 (2026-04-22). The fat-proof carving pass begins, shrinking the codebase by reusing existing helpers and collapsing sister-symmetric branches.",
    },
]


@dataclass
class LeanFileStats:
    total_lines: int = 0
    nonblank_lines: int = 0
    file_count: int = 0


def run_git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout


def format_int(value: int) -> str:
    return f"{value:,}"


def format_signed_int(value: int) -> str:
    return f"{value:+,}"


def month_label(month_key: str) -> str:
    parsed = datetime.strptime(month_key, "%Y-%m")
    return parsed.strftime("%b %Y")


def day_label(day_key: str) -> str:
    parsed = datetime.strptime(day_key, "%Y-%m-%d")
    return parsed.strftime("%b %d, %Y")


def short_day_label(day_key: str) -> str:
    parsed = datetime.strptime(day_key, "%Y-%m-%d")
    return parsed.strftime("%b %d")


def directory_label(path: Path) -> str:
    if len(path.parts) == 1:
        return "repo root"
    return f"{path.parts[0]}/"


def tracked_lean_paths() -> list[Path]:
    output = run_git("ls-files", "*.lean")
    return [Path(line) for line in output.splitlines() if line.strip()]


def collect_lean_stats() -> tuple[dict[str, int | str], list[dict[str, int | str]]]:
    per_directory: dict[str, LeanFileStats] = defaultdict(LeanFileStats)
    total_lines = 0
    nonblank_lines = 0
    lean_paths = tracked_lean_paths()

    for lean_path in lean_paths:
        contents = run_git("show", f"HEAD:{lean_path.as_posix()}")
        lines = contents.splitlines()
        line_count = len(lines)
        nonblank_count = sum(1 for line in lines if line.strip())

        label = directory_label(lean_path)
        per_directory[label].total_lines += line_count
        per_directory[label].nonblank_lines += nonblank_count
        per_directory[label].file_count += 1

        total_lines += line_count
        nonblank_lines += nonblank_count

    directory_rows: list[dict[str, int | str]] = []
    for label, stats in sorted(
        per_directory.items(),
        key=lambda item: (-item[1].total_lines, item[0]),
    ):
        directory_rows.append(
            {
                "label": label,
                "file_count": stats.file_count,
                "file_count_display": format_int(stats.file_count),
                "total_lines": stats.total_lines,
                "total_lines_display": format_int(stats.total_lines),
                "nonblank_lines": stats.nonblank_lines,
                "nonblank_lines_display": format_int(stats.nonblank_lines),
            }
        )

    summary: dict[str, int | str] = {
        "lean_files": len(lean_paths),
        "lean_files_display": format_int(len(lean_paths)),
        "lean_lines": total_lines,
        "lean_lines_display": format_int(total_lines),
        "nonblank_lean_lines": nonblank_lines,
        "nonblank_lean_lines_display": format_int(nonblank_lines),
    }
    return summary, directory_rows


def lean_lines_at_commit(commit: str) -> int:
    cached = LEAN_LINE_CACHE.get(commit)
    if cached is not None:
        return cached
    paths = [
        line
        for line in run_git("ls-tree", "-r", "--name-only", commit).splitlines()
        if line.strip().endswith(".lean")
    ]
    total_lines = 0
    for path in paths:
        contents = run_git("show", f"{commit}:{path}")
        total_lines += len(contents.splitlines())
    LEAN_LINE_CACHE[commit] = total_lines
    return total_lines


def daily_lean_commits() -> list[tuple[str, str]]:
    raw_history = [
        line
        for line in run_git(
            "log",
            "--format=%H\t%ad",
            "--date=short",
            "--",
            "*.lean",
        ).splitlines()
        if line.strip()
    ]

    if not raw_history:
        return []

    daily_commits: list[tuple[str, str]] = []
    seen_days: set[str] = set()
    for entry in raw_history:
        commit, day = entry.split("\t", maxsplit=1)
        if day in seen_days:
            continue
        seen_days.add(day)
        daily_commits.append((commit, day))

    daily_commits.reverse()
    return daily_commits


def build_lean_history_rows(
    daily_commits: list[tuple[str, str]],
) -> list[dict[str, int | str]]:
    history_rows: list[dict[str, int | str]] = []
    previous_lines: int | None = None

    for commit, day in daily_commits:
        total_lines = lean_lines_at_commit(commit)
        if previous_lines is None:
            delta = 0
            delta_display = "0"
            delta_direction = "flat"
        else:
            delta = total_lines - previous_lines
            delta_display = format_signed_int(delta)
            delta_direction = (
                "up" if delta > 0 else "down" if delta < 0 else "flat"
            )

        history_rows.append(
            {
                "date": day,
                "label": day_label(day),
                "short_label": short_day_label(day),
                "lean_lines": total_lines,
                "lean_lines_display": format_int(total_lines),
                "delta_from_previous": delta,
                "delta_from_previous_display": delta_display,
                "delta_direction": delta_direction,
            }
        )
        previous_lines = total_lines
    return history_rows


def summarize_lean_history(
    history_rows: list[dict[str, int | str]], snapshot_count: int = 8
) -> tuple[dict[str, int | str], list[dict[str, int | str]]]:
    if not history_rows:
        return {
            "lean_snapshot_count": 0,
            "lean_snapshot_count_display": "0",
            "lean_lines_recent_change": 0,
            "lean_lines_recent_change_display": "0",
            "lean_lines_recent_change_direction": "flat",
            "lean_snapshot_start_date": "",
            "lean_snapshot_end_date": "",
            "lean_snapshot_start_label": "",
            "lean_snapshot_end_label": "",
        }, []

    recent_rows = history_rows[-snapshot_count:]
    if len(recent_rows) >= 2:
        recent_change = recent_rows[-1]["lean_lines"] - recent_rows[0]["lean_lines"]
        recent_change_display = format_signed_int(recent_change)
        recent_change_direction = (
            "up" if recent_change > 0 else "down" if recent_change < 0 else "flat"
        )
    else:
        recent_change = 0
        recent_change_display = "0"
        recent_change_direction = "flat"

    summary: dict[str, int | str] = {
        "lean_snapshot_count": len(recent_rows),
        "lean_snapshot_count_display": format_int(len(recent_rows)),
        "lean_lines_recent_change": recent_change,
        "lean_lines_recent_change_display": recent_change_display,
        "lean_lines_recent_change_direction": recent_change_direction,
        "lean_snapshot_start_date": recent_rows[0]["date"],
        "lean_snapshot_end_date": recent_rows[-1]["date"],
        "lean_snapshot_start_label": recent_rows[0]["label"],
        "lean_snapshot_end_label": recent_rows[-1]["label"],
    }
    return summary, recent_rows


def build_lean_line_chart(
    history_rows: list[dict[str, int | str]],
    milestones: list[dict[str, str]] | None = None,
    width: int = 720,
    height: int = 220,
    tick_count: int = 5,
) -> dict[str, int | str | list[dict[str, int | str | float]]]:
    if not history_rows:
        return {
            "width": width,
            "height": height,
            "polyline_points": "",
            "area_points": "",
            "min_lines_display": "0",
            "max_lines_display": "0",
            "x_ticks": [],
        }

    pad_x = 20.0
    pad_y = 18.0
    plot_width = width - 2 * pad_x
    plot_height = height - 2 * pad_y
    line_values = [int(row["lean_lines"]) for row in history_rows]
    min_lines = min(line_values)
    max_lines = max(line_values)

    def point_for(index: int, line_total: int) -> tuple[float, float]:
        if len(history_rows) == 1:
            x = width / 2
        else:
            x = pad_x + index * plot_width / (len(history_rows) - 1)
        if max_lines == min_lines:
            y = pad_y + plot_height / 2
        else:
            y = pad_y + (max_lines - line_total) * plot_height / (max_lines - min_lines)
        return x, y

    points = [point_for(index, value) for index, value in enumerate(line_values)]
    polyline_points = " ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    area_points = " ".join(
        [
            f"{points[0][0]:.1f},{height - pad_y:.1f}",
            polyline_points,
            f"{points[-1][0]:.1f},{height - pad_y:.1f}",
        ]
    )

    start_date = datetime.strptime(str(history_rows[0]["date"]), "%Y-%m-%d")
    end_date = datetime.strptime(str(history_rows[-1]["date"]), "%Y-%m-%d")
    use_year_labels = (end_date - start_date).days > 180

    def tick_label(row: dict[str, int | str]) -> str:
        parsed = datetime.strptime(str(row["date"]), "%Y-%m-%d")
        return parsed.strftime("%b %Y" if use_year_labels else "%b %d")

    if len(history_rows) <= tick_count:
        tick_indices = list(range(len(history_rows)))
    else:
        tick_indices = sorted({
            round(i * (len(history_rows) - 1) / (tick_count - 1))
            for i in range(tick_count)
        })

    x_ticks = [
        {
            "x": round(points[index][0], 1),
            "x_percent": round(points[index][0] * 100 / width, 2),
            "label": tick_label(history_rows[index]),
        }
        for index in tick_indices
    ]

    milestone_markers: list[dict[str, int | str | float]] = []
    if milestones:
        date_to_index = {str(row["date"]): i for i, row in enumerate(history_rows)}
        for i, ms in enumerate(milestones, start=1):
            idx = date_to_index.get(ms["date"])
            if idx is None:
                continue
            mx, my = points[idx]
            milestone_markers.append({
                "number": i,
                "date": ms["date"],
                "date_label": day_label(ms["date"]),
                "title": ms.get("title", ""),
                "description": ms.get("description", ""),
                "note": ms.get("note", ""),
                "x": round(mx, 1),
                "y": round(my, 1),
                "label_y": round(max(my - 14, pad_y - 4), 1),
                "lean_lines": int(history_rows[idx]["lean_lines"]),
                "lean_lines_display": str(history_rows[idx]["lean_lines_display"]),
            })

    return {
        "width": width,
        "height": height,
        "polyline_points": polyline_points,
        "area_points": area_points,
        "min_lines_display": format_int(min_lines),
        "max_lines_display": format_int(max_lines),
        "x_ticks": x_ticks,
        "first_date": str(history_rows[0]["date"]),
        "latest_date": str(history_rows[-1]["date"]),
        "first_label": str(history_rows[0]["label"]),
        "latest_label": str(history_rows[-1]["label"]),
        "point_count": len(history_rows),
        "point_count_display": format_int(len(history_rows)),
        "milestones": milestone_markers,
    }


def collect_git_stats() -> tuple[
    dict[str, int | str],
    list[dict[str, int | str]],
    list[dict[str, int | str]],
]:
    raw_dates = [
        line
        for line in run_git("log", "--date=short", "--format=%ad").splitlines()
        if line.strip()
    ]
    commit_dates = [date.fromisoformat(line) for line in raw_dates]

    if not commit_dates:
        raise RuntimeError("repository has no commits")

    today = date.today()
    first_commit = min(commit_dates)
    latest_commit = max(commit_dates)
    last_30_cutoff = today - timedelta(days=30)
    last_90_cutoff = today - timedelta(days=90)
    last_365_cutoff = today - timedelta(days=365)

    by_month = Counter(commit.strftime("%Y-%m") for commit in commit_dates)
    by_year = Counter(commit.strftime("%Y") for commit in commit_dates)

    recent_month_rows = [
        {
            "month": month,
            "label": month_label(month),
            "commit_count": by_month[month],
            "commit_count_display": format_int(by_month[month]),
        }
        for month in sorted(by_month)[-6:]
    ]

    yearly_rows = [
        {
            "year": year,
            "commit_count": by_year[year],
            "commit_count_display": format_int(by_year[year]),
        }
        for year in sorted(by_year)
    ]

    commits_last_30 = sum(commit >= last_30_cutoff for commit in commit_dates)
    commits_last_90 = sum(commit >= last_90_cutoff for commit in commit_dates)
    commits_last_365 = sum(commit >= last_365_cutoff for commit in commit_dates)
    active_days = (latest_commit - first_commit).days + 1

    summary: dict[str, int | str] = {
        "total_commits": len(commit_dates),
        "total_commits_display": format_int(len(commit_dates)),
        "commits_last_30_days": commits_last_30,
        "commits_last_30_days_display": format_int(commits_last_30),
        "commits_last_90_days": commits_last_90,
        "commits_last_90_days_display": format_int(commits_last_90),
        "commits_last_365_days": commits_last_365,
        "commits_last_365_days_display": format_int(commits_last_365),
        "first_commit_date": first_commit.isoformat(),
        "latest_commit_date": latest_commit.isoformat(),
        "active_days": active_days,
        "active_days_display": format_int(active_days),
    }
    return summary, recent_month_rows, yearly_rows


def main() -> None:
    lean_summary, directory_rows = collect_lean_stats()
    full_lean_history_rows = build_lean_history_rows(daily_lean_commits())
    lean_history_summary, lean_history_rows = summarize_lean_history(full_lean_history_rows)
    git_summary, recent_month_rows, yearly_rows = collect_git_stats()

    payload = {
        "generated_on": date.today().isoformat(),
        "script_path": "scripts/generate_repo_stats.py",
        "summary": {**lean_summary, **lean_history_summary, **git_summary},
        "directory_breakdown": directory_rows,
        "recent_lean_history": lean_history_rows,
        "lean_line_chart": build_lean_line_chart(full_lean_history_rows, MILESTONES),
        "recent_months": recent_month_rows,
        "commits_by_year": yearly_rows,
    }

    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
