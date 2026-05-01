---
layout: page
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
in algebraic statistics. Every result on this site links to the Lean file that
verifies it.

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

## Definitions In Lean

These are the formal counterparts of the objects above. The first three live in
[BEI/Definitions.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Definitions.lean)
and the last in
[BEI/MonomialOrder.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MonomialOrder.lean).
The [Foundations](./foundations.html) page tabulates the supporting
infrastructure (generators $f_{ij}$, leading-term lemmas, the closure
construction).

```lean
variable {K : Type*} [Field K] {V : Type*} [LinearOrder V]

def BinomialEdgeVars (V : Type*) := V ⊕ V

def binomialEdgeIdeal (G : SimpleGraph V) :
    Ideal (MvPolynomial (BinomialEdgeVars V) K) :=
  Ideal.span { f | ∃ i j, G.Adj i j ∧ i < j ∧ f = x i * y j - x j * y i }

def IsClosedGraph (G : SimpleGraph V) : Prop :=
  (∀ {i j k : V}, i < j → i < k → j ≠ k → G.Adj i j → G.Adj i k → G.Adj j k) ∧
  (∀ {i j k : V}, i < k → j < k → i ≠ j → G.Adj i k → G.Adj j k → G.Adj i j)

noncomputable def binomialEdgeMonomialOrder :
    MonomialOrder (BinomialEdgeVars V) := MonomialOrder.lex
```

In order: the index type for the two copies of variables $x_i$, $y_i$ (encoded
as $V \oplus V$); the ideal $J_G$; the closed-graph condition that
characterizes when the quadratic generators form a Gröbner basis (Theorem 1.1);
and the lexicographic monomial order from the paper,
$x_1 > \cdots > x_n > y_1 > \cdots > y_n$.

## Sections

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

## Project Links

<div class="quick-links">
  <a href="https://github.com/tom111/BEI-lean/tree/master/BEI">Lean files</a>
  <a href="https://github.com/tom111/BEI-lean/tree/master/toMathlib">Supporting library</a>
  <a href="https://machteburch.social/@tomkalei" rel="me"><svg class="mastodon-icon" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 74 79" aria-hidden="true" focusable="false"><path d="M73.7014 17.4323C72.5616 9.05152 65.1774 2.4469 56.424 1.1671C54.9472 0.950843 49.3518 0.163818 36.3901 0.163818H36.2933C23.3281 0.163818 20.5465 0.950843 19.0697 1.1671C10.56 2.41145 2.78877 8.34604 0.903306 16.826C-0.00357854 21.0022 -0.100361 25.6322 0.068112 29.8793C0.308275 35.9699 0.354874 42.0498 0.91406 48.1156C1.30064 52.1448 1.97502 56.1419 2.93215 60.0769C4.72441 67.3445 11.9795 73.3925 19.0876 75.86C26.6979 78.4332 34.8821 78.8603 42.724 77.0937C43.5866 76.8952 44.4398 76.6647 45.2833 76.4024C47.1867 75.8033 49.4199 75.1332 51.0616 73.9562C51.0841 73.9397 51.1026 73.9184 51.1156 73.8938C51.1286 73.8693 51.1359 73.8421 51.1368 73.8144V67.9366C51.1364 67.9107 51.1302 67.8852 51.1186 67.862C51.1069 67.8388 51.0902 67.8184 51.0695 67.8025C51.0489 67.7865 51.0249 67.7753 50.9994 67.7696C50.9738 67.764 50.9473 67.7641 50.9218 67.7699C45.8976 68.9569 40.7491 69.5519 35.5836 69.5425C26.694 69.5425 24.3031 65.3699 23.6184 63.6327C23.0681 62.1314 22.7186 60.5654 22.5789 58.9744C22.5775 58.9477 22.5825 58.921 22.5934 58.8965C22.6043 58.8721 22.621 58.8505 22.6419 58.8336C22.6629 58.8167 22.6876 58.8049 22.714 58.7992C22.7404 58.7934 22.7678 58.794 22.794 58.8007C27.7345 59.9796 32.799 60.5746 37.8813 60.5733C39.1036 60.5733 40.3223 60.5733 41.5447 60.5414C46.6562 60.3996 52.0437 60.1408 57.0728 59.1694C57.1983 59.1446 57.3237 59.1233 57.4313 59.0914C65.3638 57.5847 72.9128 52.8555 73.6799 40.8799C73.7086 40.4084 73.7803 35.9415 73.7803 35.4523C73.7839 33.7896 74.3216 23.6576 73.7014 17.4323ZM61.4925 47.3144H53.1514V27.107C53.1514 22.8528 51.3591 20.6832 47.7136 20.6832C43.7061 20.6832 41.6988 23.2499 41.6988 28.3194V39.3803H33.4078V28.3194C33.4078 23.2499 31.3969 20.6832 27.3894 20.6832C23.7654 20.6832 21.9552 22.8528 21.9516 27.107V47.3144H13.6176V26.4937C13.6176 22.2395 14.7157 18.8598 16.9118 16.3545C19.1772 13.8552 22.1488 12.5719 25.8373 12.5719C30.1064 12.5719 33.3325 14.1955 35.4832 17.4394L37.5587 20.8853L39.6377 17.4394C41.7884 14.1955 45.0145 12.5719 49.2765 12.5719C52.9614 12.5719 55.9329 13.8552 58.2055 16.3545C60.4017 18.8574 61.4997 22.2371 61.4997 26.4937L61.4925 47.3144Z"/></svg>Mastodon</a>
</div>
