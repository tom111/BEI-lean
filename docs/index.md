---
title: Binomial Edge Ideals
---

<div class="landing-hero landing-hero--clean">
  <div class="landing-hero__main">
    <div class="landing-hero__eyebrow">Formalization of Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010)</div>
    <p class="landing-hero__lede">
      This project formalizes the main algebraic results of
      <em>Binomial edge ideals and conditional independence statements</em> in Lean.
      The Gröbner basis, radicality, prime decomposition, dimension, and
      conditional-independence bridge are formalized. The paper-faithful
      Cohen–Macaulay theorem of Proposition 1.6 is now formalized as well, and
      Corollary 3.4 is now formalized in its paper-faithful
      Cohen–Macaulay form. The remaining paper-level gap is the downstream
      Cohen–Macaulay branch of Corollary 3.7.
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
      <span class="landing-summary__value">20 / 21</span>
      <span class="landing-summary__label">main results completed</span>
    </div>
    <div class="landing-summary__metric">
      <span class="landing-summary__value">1</span>
      <span class="landing-summary__label">paper-level gap remains</span>
    </div>
    <div class="landing-summary__note">
      <strong>Current status:</strong> the project already covers the main
      Gröbner, radicality, prime-decomposition, and conditional-independence
      results from the paper, including the paper-faithful Proposition 1.6
      Cohen–Macaulay theorem and the paper-faithful Corollary 3.4.
      What remains is the full Cohen–Macaulay statement of Corollary 3.7.
    </div>
  </div>
</div>

## Start Here

Binomial edge ideals attach a quadratic binomial ideal to a graph. The paper
studies when these ideals admit quadratic Gröbner bases, how their prime
decomposition reflects the graph, and how they connect to conditional
independence statements from algebraic statistics.

This site is organized by the paper's four sections. Each section page lists
the paper results, the corresponding Lean declarations, and how closely the
formal statement matches the published one.

## Main Results

<div class="result-board">
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Closed graphs and quadratic Gröbner bases</strong>
      <span>Theorem 1.1 and the main Section 1 graph-theoretic consequences are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Section 2 complete</strong>
      <span>The Gröbner basis theorem and the radicality corollary are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Prime decomposition and dimension theory</strong>
      <span>The prime ideals, prime decomposition, dimension formula, minimal primes, and non-Cohen–Macaulay cycle branches are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Section 4 complete</strong>
      <span>Conditional independence ideals are linked to binomial edge ideals, with bridge theorems, radicality, prime decomposition, and minimal-prime results.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Paper-faithful Proposition 1.6 complete</strong>
      <span>The full Cohen–Macaulay theorem, its Gröbner deformation transfer, and the path-graph example are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Paper-faithful Corollary 3.4 complete</strong>
      <span>The Section 3 Cohen–Macaulay dimension formula is now formalized in its paper statement.</span>
    </div>
  </div>
  <div class="result-item result-item--open">
    <span class="result-item__icon" data-icon="&#9675;"></span>
    <div>
      <strong>One Section 3 CM corollary remains partial</strong>
      <span>Corollary 3.7 still uses an equidimensional surrogate for its Cohen–Macaulay branch.</span>
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
    <span class="section-card__meta">complete</span>
  </a>
  <a class="section-card" href="{{ '/section-2.html' | relative_url }}">
    <span class="section-card__kicker">Section 2</span>
    <strong>Reduced Gröbner basis and radicality</strong>
    <span class="section-card__meta">complete</span>
  </a>
  <a class="section-card" href="{{ '/section-3.html' | relative_url }}">
    <span class="section-card__kicker">Section 3</span>
    <strong>Prime decomposition, dimension, minimal primes</strong>
    <span class="section-card__meta">prime theory complete; Corollary 3.4 exact; Corollary 3.7 CM branch still partial</span>
  </a>
  <a class="section-card" href="{{ '/section-4.html' | relative_url }}">
    <span class="section-card__kicker">Section 4</span>
    <strong>Conditional independence ideals and robustness</strong>
    <span class="section-card__meta">bridge theorems and the main binary-output results are complete</span>
  </a>
</div>

## Featured Theorems

Each card shows a paper statement and the corresponding Lean theorem. The Lean
side includes the declaration name and a representative snippet, but the section
pages give the fuller context.

<div class="featured-theorems">
  {% assign featured_keys = "theorem_1_1,corollary_2_2,theorem_3_2,corollary_3_4,ci_bridge" | split: "," %}
  {% for key in featured_keys %}
    {% assign item = site.data.homepage_featured[key] %}
    {% include theorem_highlight.html item=item %}
  {% endfor %}
</div>

## Remaining Paper-Level Gaps

<div class="blocker-grid">
  <article class="blocker-card blocker-card--open">
    <span class="blocker-card__kicker">Corollary 3.7</span>
    <strong>Cycle-graph CM branch</strong>
    <p>The prime and unmixed branches are formalized exactly. The Cohen–Macaulay branch is still represented only by the equidimensional surrogate.</p>
    <a href="{{ '/section-3.html' | relative_url }}">See Section 3</a>
  </article>
</div>

## Code And Status

<div class="quick-links">
  <a href="https://github.com/tom111/BEI-lean/tree/master/BEI">Lean files</a>
  <a href="https://github.com/tom111/BEI-lean/tree/master/toMathlib">Supporting library</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Formalization map</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/TODO.md">Current task list</a>
</div>
