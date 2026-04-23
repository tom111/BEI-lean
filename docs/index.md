---
title: Binomial Edge Ideals
---

<div class="landing-hero landing-hero--clean">
  <div class="landing-hero__main">
    <div class="landing-hero__eyebrow">Formalization of Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010)</div>
    <p class="landing-hero__lede">
      This project formalizes the main algebraic results of
      <em>Binomial edge ideals and conditional independence statements</em> in Lean.
      The named results from Sections 1 through 4 are represented in Lean.
      The section pages distinguish exact statement matches from equivalent
      reformulations.
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
      <span class="landing-summary__label">named results tracked</span>
    </div>
    <div class="landing-summary__metric">
      <span class="landing-summary__value">5</span>
      <span class="landing-summary__label">equivalent reformulations</span>
    </div>
    <div class="landing-summary__note">
      <strong>Scope:</strong> the site covers the paper's Gröbner-basis,
      radicality, prime-decomposition, dimension, minimal-prime, and
      conditional-independence results. Equivalent packaging remains for
      Proposition 1.4, Theorem 2.1, Proposition 3.6, Proposition 3.8, and
      Corollary 3.9; the remaining named results are listed as exact matches.
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
      <strong>Statement map</strong>
      <span>The section pages mark each named result as either an exact match to the paper statement or an equivalent reformulation.</span>
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

## Statement Fidelity

The section pages record whether each Lean declaration matches the paper
exactly or is packaged as an equivalent reformulation.

- Equivalent packaging is used for Proposition 1.4, Theorem 2.1, Proposition 3.6, Proposition 3.8, and Corollary 3.9.
- All other named paper results listed on the section pages are formalized exactly.

## Code And Status

<div class="quick-links">
  <a href="https://github.com/tom111/BEI-lean/tree/master/BEI">Lean files</a>
  <a href="https://github.com/tom111/BEI-lean/tree/master/toMathlib">Supporting library</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Formalization map</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/TODO.md">Current task list</a>
</div>
