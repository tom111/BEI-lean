---
title: About
---

# About

{% assign repo_stats = site.data.repo_stats %}

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
