---
title: Binomial Edge Ideals
---

<header class="masthead">
  <div class="masthead__inner">
    <div class="masthead__eyebrow">
      Formalization of Herzog, Hibi, Hreinsdóttir, Kahle &amp; Rauh &middot; 2010
    </div>
    <h1 class="masthead__title">Binomial Edge Ideals</h1>
    <p class="masthead__lede">
      A machine-checked companion to <em>Binomial edge ideals and conditional independence statements</em>. Read the paper alongside the formal proofs, and follow any theorem down to the Lean code that verifies it.
    </p>
    <nav class="masthead__nav">
      <a href="{{ '/overview.html' | relative_url }}">Overview</a>
      <a href="{{ '/foundations.html' | relative_url }}">Definitions</a>
      <a href="{{ '/section-1.html' | relative_url }}">§&nbsp;1</a>
      <a href="{{ '/section-2.html' | relative_url }}">§&nbsp;2</a>
      <a href="{{ '/section-3.html' | relative_url }}">§&nbsp;3</a>
      <a href="{{ '/section-4.html' | relative_url }}">§&nbsp;4</a>
    </nav>
    <figure class="masthead__plate">
      <div class="masthead__plate-graph">
        <svg viewBox="0 0 300 110" xmlns="http://www.w3.org/2000/svg" role="img" aria-label="A path graph on four vertices labeled 1 through 4">
          <g fill="none" stroke="#1a1a1a" stroke-width="1.5" stroke-linecap="round">
            <line x1="30" y1="45" x2="110" y2="45"/>
            <line x1="110" y1="45" x2="190" y2="45"/>
            <line x1="190" y1="45" x2="270" y2="45"/>
          </g>
          <g fill="#fbfaf6" stroke="#1a1a1a" stroke-width="1.5">
            <circle cx="30" cy="45" r="7.5"/>
            <circle cx="110" cy="45" r="7.5"/>
            <circle cx="190" cy="45" r="7.5"/>
            <circle cx="270" cy="45" r="7.5"/>
          </g>
          <g fill="#1a1a1a" font-family="'Source Serif 4', serif" font-style="italic" font-size="16" text-anchor="middle">
            <text x="30" y="85">1</text>
            <text x="110" y="85">2</text>
            <text x="190" y="85">3</text>
            <text x="270" y="85">4</text>
          </g>
        </svg>
      </div>
      <figcaption class="masthead__plate-ideal">
        <div class="plate-line">$f_{12} \,=\, x_1 y_2 - x_2 y_1$</div>
        <div class="plate-line">$f_{23} \,=\, x_2 y_3 - x_3 y_2$</div>
        <div class="plate-line">$f_{34} \,=\, x_3 y_4 - x_4 y_3$</div>
        <div class="plate-line plate-line--ideal">$J_{P_4} \,=\, \langle\, f_{12},\; f_{23},\; f_{34}\, \rangle$</div>
        <span class="masthead__plate-caption">A path on four vertices, and the three quadratic generators of its binomial edge ideal.</span>
      </figcaption>
    </figure>
    <div class="masthead__refs">
      <a href="https://doi.org/10.1016/j.aam.2010.01.003">Adv. Math. 2010</a>
      <a href="https://arxiv.org/abs/0909.4717">arXiv:0909.4717</a>
      <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Paper-to-Lean map</a>
    </div>
  </div>
</header>

## What Is A Binomial Edge Ideal?

To a simple graph $G$ on vertices $\{1, \dots, n\}$, the binomial edge ideal
$J_G$ attaches one binomial per edge:

$$
J_G \;=\; \langle\, x_i y_j - x_j y_i \;:\; \{i, j\} \in E(G) \,\rangle
\;\subseteq\; K[x_1, \dots, x_n, y_1, \dots, y_n].
$$

The paper approaches these ideals from three sides: when the given generators
already form a Gröbner basis, how the prime decomposition is controlled by the
graph, and how the same ideals arise from conditional independence statements
in algebraic statistics. This site is organized around the paper's four
sections — every result links to the Lean file that verifies it.

## Explore By Section

<div class="section-grid">
  <a class="section-card" href="{{ '/foundations.html' | relative_url }}">
    <span class="section-card__kicker">Foundations</span>
    <strong>Definitions, term order, and Gröbner setup</strong>
    <span class="section-card__meta">The graph, the polynomial ring, and the lex term order — the objects everything else is built from.</span>
  </a>
  <a class="section-card" href="{{ '/section-1.html' | relative_url }}">
    <span class="section-card__kicker">Section 1</span>
    <strong>Closed graphs and quadratic Gröbner bases</strong>
    <span class="section-card__meta">When do the edge binomials already form a Gröbner basis? A graph-theoretic answer, plus the Cohen–Macaulay criterion.</span>
  </a>
  <a class="section-card" href="{{ '/section-2.html' | relative_url }}">
    <span class="section-card__kicker">Section 2</span>
    <strong>Reduced Gröbner basis and radicality</strong>
    <span class="section-card__meta">The edge binomials give a reduced Gröbner basis, and $J_G$ turns out to be a radical ideal.</span>
  </a>
  <a class="section-card" href="{{ '/section-3.html' | relative_url }}">
    <span class="section-card__kicker">Section 3</span>
    <strong>Prime decomposition, dimension, minimal primes</strong>
    <span class="section-card__meta">Prime decomposition, Krull dimension, and minimal primes — all described directly from the graph.</span>
  </a>
  <a class="section-card" href="{{ '/section-4.html' | relative_url }}">
    <span class="section-card__kicker">Section 4</span>
    <strong>Conditional independence ideals and robustness</strong>
    <span class="section-card__meta">Binomial edge ideals reappear as conditional independence ideals in algebraic statistics.</span>
  </a>
</div>

## A Taste Of The Formalization

Each card has the paper's statement on the left and the formal Lean theorem on
the right. Click through to open the Lean file and read the full proof.

<div class="featured-theorems">
  {% assign featured_keys = "theorem_1_1,corollary_2_2,theorem_3_2,corollary_3_4,ci_bridge" | split: "," %}
  {% for key in featured_keys %}
    {% assign item = site.data.homepage_featured[key] %}
    {% include theorem_highlight.html item=item %}
  {% endfor %}
</div>

{% assign repo_stats = site.data.repo_stats %}
{% assign line_chart = repo_stats.lean_line_chart %}

## Growth Of The Formalization

<div class="stats-grid">
  <div class="stats-card">
    <span class="stats-card__value">{{ repo_stats.summary.lean_lines_display }}</span>
    <span class="stats-card__label">Lean lines</span>
  </div>
  <div class="stats-card">
    <span class="stats-card__value stats-delta {% if repo_stats.summary.lean_lines_recent_change > 0 %}stats-delta--up{% elsif repo_stats.summary.lean_lines_recent_change < 0 %}stats-delta--down{% else %}stats-delta--flat{% endif %}">{{ repo_stats.summary.lean_lines_recent_change_display }}</span>
    <span class="stats-card__label">across the latest {{ repo_stats.summary.lean_snapshot_count_display }} snapshots</span>
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
      One snapshot from the latest Lean-editing commit on each active day, from
      {{ repo_stats.summary.lean_snapshot_start_label }} to
      {{ repo_stats.summary.lean_snapshot_end_label }}.
      More numbers on the <a href="{{ '/about.html' | relative_url }}">about page</a>.
    </p>
  </div>
</div>

## Go Deeper

<div class="quick-links">
  <a href="https://github.com/tom111/BEI-lean/tree/master/BEI">Lean files</a>
  <a href="https://github.com/tom111/BEI-lean/tree/master/toMathlib">Supporting library</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Paper-to-Lean map</a>
  <a href="https://doi.org/10.1016/j.aam.2010.01.003">Published paper</a>
  <a href="https://arxiv.org/abs/0909.4717">arXiv preprint</a>
</div>
