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


def month_label(month_key: str) -> str:
    parsed = datetime.strptime(month_key, "%Y-%m")
    return parsed.strftime("%b %Y")


def directory_label(path: Path) -> str:
    if len(path.parts) == 1:
        return "repo root"
    return f"{path.parts[0]}/"


def tracked_lean_paths() -> list[Path]:
    output = run_git("ls-files", "*.lean")
    return [REPO_ROOT / Path(line) for line in output.splitlines() if line.strip()]


def collect_lean_stats() -> tuple[dict[str, int | str], list[dict[str, int | str]]]:
    per_directory: dict[str, LeanFileStats] = defaultdict(LeanFileStats)
    total_lines = 0
    nonblank_lines = 0
    lean_paths = tracked_lean_paths()

    for lean_path in lean_paths:
        contents = lean_path.read_text(encoding="utf-8")
        lines = contents.splitlines()
        line_count = len(lines)
        nonblank_count = sum(1 for line in lines if line.strip())

        label = directory_label(lean_path.relative_to(REPO_ROOT))
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
    git_summary, recent_month_rows, yearly_rows = collect_git_stats()

    payload = {
        "generated_on": date.today().isoformat(),
        "script_path": "scripts/generate_repo_stats.py",
        "summary": {**lean_summary, **git_summary},
        "directory_breakdown": directory_rows,
        "recent_months": recent_month_rows,
        "commits_by_year": yearly_rows,
    }

    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
