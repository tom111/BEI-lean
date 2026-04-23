---
title: About
---

# About

{% assign repo_stats = site.data.repo_stats %}
{% assign line_chart = repo_stats.lean_line_chart %}

## Lean Code Over Time

<div class="stats-panels">
  <div class="stats-panel">
    <div class="stats-chart" role="img" aria-label="Total Lean lines across the project history, with numbered milestones">
      <div class="stats-chart__bounds">
        <span>{{ line_chart.max_lines_display }}</span>
        <span>{{ line_chart.min_lines_display }}</span>
      </div>
      <svg viewBox="0 0 {{ line_chart.width }} {{ line_chart.height }}" aria-hidden="true">
        <polygon class="stats-chart__area" points="{{ line_chart.area_points }}"></polygon>
        <polyline class="stats-chart__line" points="{{ line_chart.polyline_points }}"></polyline>
        {% for m in line_chart.milestones %}
        <g class="stats-chart__milestone">
          <line class="stats-chart__milestone-stem" x1="{{ m.x }}" y1="{{ m.y }}" x2="{{ m.x }}" y2="{{ m.label_y }}"></line>
          <circle class="stats-chart__milestone-dot" cx="{{ m.x }}" cy="{{ m.y }}" r="4.5"></circle>
          <circle class="stats-chart__milestone-label-bg" cx="{{ m.x }}" cy="{{ m.label_y }}" r="8"></circle>
          <text class="stats-chart__milestone-label" x="{{ m.x }}" y="{{ m.label_y }}" text-anchor="middle" dy="0.35em">{{ m.number }}</text>
        </g>
        {% endfor %}
      </svg>
      <div class="stats-chart__ticks" aria-hidden="true">
        {% for tick in line_chart.x_ticks %}
        <span class="stats-chart__tick" style="left: {{ tick.x_percent }}%;">{{ tick.label }}</span>
        {% endfor %}
      </div>
    </div>
    <p class="stats-caption">
      Total Lean lines at the end of each day with Lean-editing activity,
      from {{ line_chart.first_label }} to {{ line_chart.latest_label }}
      ({{ line_chart.point_count_display }} snapshots).
    </p>
    <ol class="stats-chart__legend">
      {% for m in line_chart.milestones %}
      <li>
        <span class="stats-chart__legend-date">{{ m.date_label }}</span>
        <strong>{{ m.title }}</strong> — {{ m.description }}
      </li>
      {% endfor %}
    </ol>
  </div>
</div>

## By The Numbers

<div class="stats-grid">
  <div class="stats-card">
    <span class="stats-card__value">{{ repo_stats.summary.lean_files_display }}</span>
    <span class="stats-card__label">tracked Lean files</span>
  </div>
  <div class="stats-card">
    <span class="stats-card__value">{{ repo_stats.summary.lean_lines_display }}</span>
    <span class="stats-card__label">Lean lines</span>
  </div>
  <div class="stats-card">
    <span class="stats-card__value">{{ repo_stats.summary.total_commits_display }}</span>
    <span class="stats-card__label">total commits</span>
  </div>
  <div class="stats-card">
    <span class="stats-card__value">{{ repo_stats.summary.commits_last_30_days_display }}</span>
    <span class="stats-card__label">commits in the last 30 days</span>
  </div>
</div>

## Lean Code By Directory

<div class="stats-panels">
  <div class="stats-panel">
    <table class="stats-table">
      <thead>
        <tr>
          <th>Directory</th>
          <th>Files</th>
          <th>Lines</th>
          <th>Nonblank lines</th>
        </tr>
      </thead>
      <tbody>
        {% for row in repo_stats.directory_breakdown %}
        <tr>
          <td>{{ row.label }}</td>
          <td>{{ row.file_count_display }}</td>
          <td>{{ row.total_lines_display }}</td>
          <td>{{ row.nonblank_lines_display }}</td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
  </div>
</div>

## Recent Commit Activity

<div class="stats-panels">
  <div class="stats-panel">
    <table class="stats-table">
      <thead>
        <tr>
          <th>Month</th>
          <th>Commits</th>
        </tr>
      </thead>
      <tbody>
        {% for row in repo_stats.recent_months %}
        <tr>
          <td>{{ row.label }}</td>
          <td>{{ row.commit_count_display }}</td>
        </tr>
        {% endfor %}
      </tbody>
    </table>
    <p class="stats-caption">
      First commit: {{ repo_stats.summary.first_commit_date }}.
      Latest commit: {{ repo_stats.summary.latest_commit_date }}.
    </p>
  </div>
</div>

## Project Links

<div class="quick-links">
  <a href="https://github.com/tom111/BEI-lean">GitHub repository</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Paper-to-Lean map</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/TODO.md">Current task list</a>
</div>
