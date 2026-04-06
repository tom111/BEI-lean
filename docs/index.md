---
title: BEI Blueprint
---

# Binomial Edge Ideals

<div class="landing-hero">
  <div class="landing-hero__eyebrow">Lean blueprint for Herzog–Hibi–Hreinsdóttir–Kahle–Rauh (2010)</div>
  <h2 class="landing-hero__title">A paper-facing formalization dashboard</h2>
  <p class="landing-hero__lede">
    This site tracks the Lean formalization of
    <em>Binomial edge ideals and conditional independence statements</em>,
    theorem by theorem. The project now has the full Section 2 and Section 3 backbone,
    the Section 4 CI-ideal transfers, and one remaining paper endpoint.
  </p>
  <div class="landing-stats">
    <div class="landing-stat">
      <span class="landing-stat__value">20 / 21</span>
      <span class="landing-stat__label">tracked endpoints complete</span>
    </div>
    <div class="landing-stat">
      <span class="landing-stat__value">1</span>
      <span class="landing-stat__label">active paper endpoint open</span>
    </div>
    <div class="landing-stat">
      <span class="landing-stat__value">0</span>
      <span class="landing-stat__label">active sorries in Sections 3 and 4</span>
    </div>
  </div>
</div>

<div class="quick-links">
  <a href="{{ '/overview.html' | relative_url }}">Overview</a>
  <a href="{{ '/section-1.html' | relative_url }}">Section 1</a>
  <a href="{{ '/section-2.html' | relative_url }}">Section 2</a>
  <a href="{{ '/section-3.html' | relative_url }}">Section 3</a>
  <a href="{{ '/section-4.html' | relative_url }}">Section 4</a>
</div>

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
    <span class="section-card__meta">complete at the current paper-facing level</span>
  </a>
</div>

## Results At A Glance

<div class="result-board">
  <div class="result-item result-item--done">
    <span class="result-item__icon">&#10003;</span>
    <div>
      <strong>Section 1 core backbone</strong>
      <span>Theorem 1.1, Propositions 1.2, 1.4, 1.5, and Corollary 1.3 are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--open">
    <span class="result-item__icon">&#9675;</span>
    <div>
      <strong>Remaining paper endpoint</strong>
      <span>Proposition 1.6 still depends on the external CM input and the initial-ideal transfer step.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon">&#10003;</span>
    <div>
      <strong>Section 2 complete</strong>
      <span>The Gröbner basis theorem and radicality consequence are both in place.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon">&#10003;</span>
    <div>
      <strong>Section 3 complete</strong>
      <span>Prime decomposition, dimension, minimal primes, and the cycle-graph CM consequence are formalized.</span>
    </div>
  </div>
  <div class="result-item result-item--done">
    <span class="result-item__icon">&#10003;</span>
    <div>
      <strong>Section 4 theorem layer landed</strong>
      <span>Single-statement and specification bridges, radicality, prime decomposition, and minimal-prime transfer are proved.</span>
    </div>
  </div>
</div>

## What This Blueprint Shows

<div class="intro-card">
This blueprint is a reader-facing map of the project. It tells you which results from the
paper are formalized, where they live in the Lean codebase, and how closely the formal
statements match the originals.
</div>

- Published paper: [Advances in Applied Mathematics DOI](https://doi.org/10.1016/j.aam.2010.01.003)
- arXiv version: [arXiv:0909.4717](https://arxiv.org/abs/0909.4717)
- TeX source in this repository: [BEI.tex](https://github.com/tom111/BEI-lean/blob/master/BEI.tex)
- Main Lean entrypoint: [BEI.lean](https://github.com/tom111/BEI-lean/blob/master/BEI.lean)
- Repository theorem map: [FORMALIZATION_MAP.md](https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md)

## Fidelity Labels

<div class="badge-row">
  <span class="fidelity-badge fidelity-badge--exact">Exact</span>
  <span class="fidelity-badge fidelity-badge--equiv">Equivalent</span>
  <span class="fidelity-badge fidelity-badge--partial">Partial</span>
  <span class="fidelity-badge fidelity-badge--sorry">Sorry</span>
  <span class="fidelity-badge fidelity-badge--blocked">Blocked</span>
</div>

- **Exact**: the Lean theorem matches the paper statement.
- **Equivalent**: the Lean theorem is mathematically equivalent but phrased differently.
- **Weaker**: Lean proves a genuine weakening of the paper statement.
- **Partial**: part of the paper statement is formalized, part is still missing.
- **Sorry**: the statement is present in Lean, but the proof is still incomplete.
- **Blocked**: the intended statement is identified, but the needed foundation is not yet in place.
