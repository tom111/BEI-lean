---
title: BEI Blueprint
---

# Binomial Edge Ideals

<div class="landing-hero landing-hero--clean">
  <div class="landing-hero__main">
    <div class="landing-hero__eyebrow">Lean project for Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010)</div>
    <p class="landing-hero__lede">
      This blueprint tracks the Lean formalization of
      <em>Binomial edge ideals and conditional independence statements</em>.
      The Gröbner-basis backbone, the Section 3 prime-decomposition results, and the
      current Section 4 CI-ideal layer are in place. One main theorem is still unfinished.
    </p>
    <div class="quick-links quick-links--hero">
      <a href="{{ '/overview.html' | relative_url }}">Overview</a>
      <a href="{{ '/section-1.html' | relative_url }}">Section 1</a>
      <a href="{{ '/section-2.html' | relative_url }}">Section 2</a>
      <a href="{{ '/section-3.html' | relative_url }}">Section 3</a>
      <a href="{{ '/section-4.html' | relative_url }}">Section 4</a>
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
      <strong>Still open:</strong> Proposition 1.6, the Cohen–Macaulay theorem for a special class of closed graphs.
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
      <span>The Gröbner basis theorem and radicality consequence are both in place.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Section 3 complete</strong>
      <span>Prime decomposition, dimension, minimal primes, and the cycle-graph CM consequence are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon" data-icon="&#10003;"></span>
    <div>
      <strong>Section 4 is in place</strong>
      <span>The conditional-independence side is connected to binomial edge ideals, including radicality, prime decomposition, and minimal-prime results.</span>
    </div>
  </div>
  <div class="result-item result-item--open">
    <span class="result-item__icon" data-icon="&#9675;"></span>
    <div>
      <strong>One main theorem remains</strong>
      <span>Proposition 1.6 still needs the final Cohen–Macaulay step.</span>
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
    <strong>CI ideals and robustness specifications</strong>
    <span class="section-card__meta">the main binary-output results are in place</span>
  </a>
</div>

## Read More

<div class="reference-strip">
  <a href="https://doi.org/10.1016/j.aam.2010.01.003">Published paper</a>
  <a href="https://arxiv.org/abs/0909.4717">arXiv</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/BEI.lean">BEI.lean</a>
  <a href="https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md">Detailed status</a>
</div>

<div class="intro-card intro-card--tight">
This blueprint is a reader-facing map of the project. The section pages show which results
from the paper are already formalized in Lean, where they live in the codebase, and how
closely the Lean statements match the published mathematics.
</div>
