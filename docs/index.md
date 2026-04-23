---
title: Binomial Edge Ideals
---

<div class="landing-hero landing-hero--clean">
  <div class="landing-hero__main">
    <div class="landing-hero__eyebrow">Formalization of Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010)</div>
    <p class="landing-hero__lede">
      This project formalizes the main algebraic results of
      <em>Binomial edge ideals and conditional independence statements</em> in Lean.
      All named results from Sections 1 through 4 of the paper are formalized.
    </p>
    <div class="quick-links quick-links--hero">
      <a href="{{ '/overview.html' | relative_url }}">Overview</a>
      <a href="{{ '/foundations.html' | relative_url }}">Definitions</a>
      <a href="{{ '/section-1.html' | relative_url }}">Section 1</a>
      <a href="{{ '/section-2.html' | relative_url }}">Section 2</a>
      <a href="{{ '/section-3.html' | relative_url }}">Section 3</a>
      <a href="{{ '/section-4.html' | relative_url }}">Section 4</a>
    </div>
    <div class="reference-strip">
      <a href="https://doi.org/10.1016/j.aam.2010.01.003">Published paper</a>
      <a href="https://arxiv.org/abs/0909.4717">arXiv</a>
      <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Detailed status</a>
    </div>
  </div>
  <div class="landing-summary">
    <div class="landing-summary__metric">
      <span class="landing-summary__value">21 / 21</span>
      <span class="landing-summary__label">named results from the paper</span>
    </div>
    <div class="landing-summary__metric">
      <span class="landing-summary__value">Done</span>
      <span class="landing-summary__label">project status</span>
    </div>
  </div>
</div>

## Start Here

Binomial edge ideals attach a quadratic binomial ideal to a graph. The paper
studies when these ideals admit quadratic Gröbner bases, how their prime
decomposition reflects the graph, and how they connect to conditional
independence statements from algebraic statistics.

This site is organized by the paper's four sections. Each section page lists
the paper results, points to the corresponding files, and notes the few places
where the formal statement is phrased a little differently.

## Main Results

<div class="result-board">
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Closed graphs and quadratic Gröbner bases</strong>
      <span>Section 1 covers the Gröbner-basis criterion, graph-theoretic consequences, the closure operation, and the Cohen--Macaulay criterion.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Reduced Gröbner bases and radicality</strong>
      <span>Section 2 records the reduced Gröbner basis theorem together with the radicality consequence.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Prime decomposition and dimension theory</strong>
      <span>Section 3 covers the prime ideals `P_S`, the decomposition of `J_G`, the dimension formula, the minimal-prime criterion, and the cycle criterion.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Conditional independence ideals</strong>
      <span>Section 4 identifies the conditional-independence ideals with binomial edge ideals and transfers radicality, prime decomposition, and minimal-prime results.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Guide to the paper</strong>
      <span>The section pages show where each result from the paper appears in the formalization and point to the relevant files.</span>
    </div>
  </div>
</div>

## Explore By Section

<div class="section-grid">
  <a class="section-card" href="{{ '/foundations.html' | relative_url }}">
    <span class="section-card__kicker">Foundations</span>
    <strong>Definitions, term order, and Gröbner setup</strong>
    <span class="section-card__meta">the main objects and theorems used across the project</span>
  </a>
  <a class="section-card" href="{{ '/section-1.html' | relative_url }}">
    <span class="section-card__kicker">Section 1</span>
    <strong>Closed graphs and quadratic Gröbner bases</strong>
    <span class="section-card__meta">criterion, consequences, closure, and Cohen--Macaulay condition</span>
  </a>
  <a class="section-card" href="{{ '/section-2.html' | relative_url }}">
    <span class="section-card__kicker">Section 2</span>
    <strong>Reduced Gröbner basis and radicality</strong>
    <span class="section-card__meta">reduced basis theorem and radicality consequence</span>
  </a>
  <a class="section-card" href="{{ '/section-3.html' | relative_url }}">
    <span class="section-card__kicker">Section 3</span>
    <strong>Prime decomposition, dimension, minimal primes</strong>
    <span class="section-card__meta">prime decomposition, dimension, minimal primes, and cycle criterion</span>
  </a>
  <a class="section-card" href="{{ '/section-4.html' | relative_url }}">
    <span class="section-card__kicker">Section 4</span>
    <strong>Conditional independence ideals and robustness</strong>
    <span class="section-card__meta">bridge theorems and transferred algebraic consequences</span>
  </a>
</div>

## Featured Theorems

Each card below pairs a statement from the paper with the corresponding formal
theorem. The section pages give the fuller context and the file locations.

<div class="featured-theorems">
  {% assign featured_keys = "theorem_1_1,corollary_2_2,theorem_3_2,corollary_3_4,ci_bridge" | split: "," %}
  {% for key in featured_keys %}
    {% assign item = site.data.homepage_featured[key] %}
    {% include theorem_highlight.html item=item %}
  {% endfor %}
</div>

{% assign repo_stats = site.data.repo_stats %}
{% assign line_chart = repo_stats.lean_line_chart %}

## The Project In Numbers

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
    <span class="stats-card__value stats-delta {% if repo_stats.summary.lean_lines_recent_change > 0 %}stats-delta--up{% elsif repo_stats.summary.lean_lines_recent_change < 0 %}stats-delta--down{% else %}stats-delta--flat{% endif %}">{{ repo_stats.summary.lean_lines_recent_change_display }}</span>
    <span class="stats-card__label">Lean lines across the latest {{ repo_stats.summary.lean_snapshot_count_display }} snapshots</span>
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

<div class="stats-panels">
  <div class="stats-panel">
    <h3>Recent Lean code over time</h3>
    <div class="stats-chart" role="img" aria-label="Lean lines over time">
      <div class="stats-chart__bounds">
        <span>{{ line_chart.max_lines_display }}</span>
        <span>{{ line_chart.min_lines_display }}</span>
      </div>
      <svg viewBox="0 0 {{ line_chart.width }} {{ line_chart.height }}" aria-hidden="true">
        <polygon class="stats-chart__area" points="{{ line_chart.area_points }}"></polygon>
        <polyline class="stats-chart__line" points="{{ line_chart.polyline_points }}"></polyline>
      </svg>
      <div class="stats-chart__ticks" aria-hidden="true">
        {% for tick in line_chart.x_ticks %}
        <span class="stats-chart__tick" style="left: {{ tick.x_percent }}%;">{{ tick.label }}</span>
        {% endfor %}
      </div>
    </div>
    <p class="stats-caption">
      One snapshot is taken from the latest Lean-editing commit on each active day.
      Net change across the recent window:
      <span class="stats-delta {% if repo_stats.summary.lean_lines_recent_change > 0 %}stats-delta--up{% elsif repo_stats.summary.lean_lines_recent_change < 0 %}stats-delta--down{% else %}stats-delta--flat{% endif %}">{{ repo_stats.summary.lean_lines_recent_change_display }}</span>
      from {{ repo_stats.summary.lean_snapshot_start_label }} to {{ repo_stats.summary.lean_snapshot_end_label }}.
    </p>
  </div>
  <div class="stats-panel">
    <h3>Lean code by directory</h3>
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
  <div class="stats-panel">
    <h3>Recent commit activity</h3>
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

## Notes For Readers

Most entries on the section pages follow the paper statements closely. A small
number are phrased differently in the formalization, while proving the same
mathematics.

- This occurs for Proposition 1.4, Theorem 2.1, Proposition 3.6, Proposition 3.8, and Corollary 3.9.

## Code And Status

<div class="quick-links">
  <a href="https://github.com/tom111/BEI-lean/tree/master/BEI">Lean files</a>
  <a href="https://github.com/tom111/BEI-lean/tree/master/toMathlib">Supporting library</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Detailed guide to the paper</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/TODO.md">Current task list</a>
</div>
