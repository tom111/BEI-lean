---
title: Binomial Edge Ideals
---

<div class="landing-hero landing-hero--clean">
  <div class="landing-hero__main">
    <div class="landing-hero__eyebrow">Formalization of Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010)</div>
    <p class="landing-hero__lede">
      This site tracks the Lean formalization of
      <em>Binomial edge ideals and conditional independence statements</em>.
      Sections 2, 3, and 4 are formalized. Section 1 is still open at
      Proposition 1.6.
    </p>
    <div class="quick-links quick-links--hero">
      <a href="{{ '/overview.html' | relative_url }}">Overview</a>
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
      <span class="landing-summary__label">main theorem still open</span>
    </div>
    <div class="landing-summary__note">
      <strong>Current status:</strong> The Proposition 1.6 branch uses a temporary
      equidimensional stand-in for Cohen-Macaulayness, but even that branch is not yet
      finished. The paper is not counted as fully formalized until the remaining
      Proposition 1.6 gap and the full Cohen-Macaulay theory are both in place.
    </div>
  </div>
</div>

## Main Results

<div class="result-board">
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Section 1 backbone</strong>
      <span>Theorem 1.1, Propositions 1.2, 1.4, 1.5, and Corollary 1.3 are formalized.</span>
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
      <strong>Section 3 complete</strong>
      <span>Prime decomposition, dimension, minimal primes, and the cycle-graph Cohen–Macaulay result are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Section 4 complete</strong>
      <span>Conditional independence ideals are linked to binomial edge ideals, with bridge theorems, radicality, prime decomposition, and minimal-prime results.</span>
    </div>
  </div>
  <div class="result-item result-item--open">
    <span class="result-item__icon" data-icon="&#9675;"></span>
    <div>
      <strong>One remaining paper-level gap</strong>
      <span>Proposition 1.6 is still open. The current Lean development uses an equidimensional stand-in for Cohen-Macaulayness, and the full depth-based theory is still missing.</span>
    </div>
  </div>
</div>

## Explore By Section

<div class="section-grid">
  <a class="section-card" href="{{ '/section-1.html' | relative_url }}">
    <span class="section-card__kicker">Section 1</span>
    <strong>Closed graphs and quadratic Gröbner bases</strong>
    <span class="section-card__meta">5 done, 1 open</span>
  </a>
  <a class="section-card" href="{{ '/section-2.html' | relative_url }}">
    <span class="section-card__kicker">Section 2</span>
    <strong>Reduced Gröbner basis and radicality</strong>
    <span class="section-card__meta">complete</span>
  </a>
  <a class="section-card" href="{{ '/section-3.html' | relative_url }}">
    <span class="section-card__kicker">Section 3</span>
    <strong>Prime decomposition, dimension, minimal primes</strong>
    <span class="section-card__meta">complete</span>
  </a>
  <a class="section-card" href="{{ '/section-4.html' | relative_url }}">
    <span class="section-card__kicker">Section 4</span>
    <strong>Conditional independence ideals and robustness</strong>
    <span class="section-card__meta">bridge theorems and the main binary-output results are complete</span>
  </a>
</div>
