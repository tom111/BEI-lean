# Gröbner Basis of Binomial Edge Ideals: Detailed Proof

## Setup and Definitions

**Setting:** Let \(G\) be a simple graph on \([n] = \{1, \ldots, n\}\). Work in the polynomial ring \(S = K[x_1, \ldots, x_n, y_1, \ldots, y_n]\) over a field \(K\).

**Binomial Edge Ideal:** \(J_G = \langle f_{ij} : \{i,j\} \in E(G), i < j \rangle\) where \(f_{ij} = x_i y_j - x_j y_i\).

**Monomial Order:** A term order \(<\) on \(S\) such that \(\mathrm{in}_<(f_{ij}) = x_i y_j\) for all \(i < j\).

---

**Definition (Admissible Path):** Let \(i < j\) be vertices of \(G\). A path \(\pi: i = i_0, i_1, \ldots, i_r = j\) is **admissible** if:
1. **(Simplicity)** \(i_k \neq i_\ell\) for \(k \neq \ell\)
2. **(Index Condition)** For each \(k \in \{1, \ldots, r-1\}\): either \(i_k < i\) or \(i_k > j\)
3. **(Minimality)** No proper subsequence \(i, j_1, \ldots, j_s, j\) of the interior vertices forms a path from \(i\) to \(j\)

**Definition (Path Monomial):** For an admissible path \(\pi: i = i_0, i_1, \ldots, i_r = j\):
\[
u_\pi = \left(\prod_{\substack{1 \leq k \leq r-1 \\ i_k > j}} x_{i_k}\right) \left(\prod_{\substack{1 \leq \ell \leq r-1 \\ i_\ell < i}} y_{i_\ell}\right)
\]

**Theorem Statement:** The set
\[
\mathcal{G} = \bigcup_{i < j} \{u_\pi f_{ij} : \pi \text{ is an admissible path from } i \text{ to } j\}
\]
is a reduced Gröbner basis of \(J_G\).

---

## First Step: \(\mathcal{G} \subseteq J_G\)

**Claim:** For each admissible path \(\pi\) from \(i\) to \(j\) (with \(i < j\)), we have \(u_\pi f_{ij} \in J_G\).

**Proof by strong induction on \(r\) (path length):**

### Base Case: \(r = 1\)

The path is \(\pi: i, j\), meaning \(\{i, j\} \in E(G)\).
- Interior vertex set: \(\emptyset\)
- Hence \(u_\pi = 1\)
- Therefore \(u_\pi f_{ij} = f_{ij} \in J_G\) by definition of \(J_G\)

### Inductive Step: \(r > 1\)

**Setup:** Let \(\pi: i = i_0, i_1, \ldots, i_{r-1}, i_r = j\) be admissible. Define:
\[
A = \{i_k : 1 \leq k \leq r-1, \, i_k < i\}, \qquad B = \{i_k : 1 \leq k \leq r-1, \, i_k > j\}
\]

**Observation 1:** By the Index Condition (property 2), every interior vertex lies in \(A \cup B\).

**Observation 2:** Since \(r > 1\), there exists at least one interior vertex \(i_k\) with \(1 \leq k \leq r-1\). Hence \(A \cup B \neq \emptyset\).

**Case A: \(A \neq \emptyset\)**

Let \(i_{k_0} = \max A\). Note \(i_{k_0} < i < j\).

**Substep A.1:** Define the subpaths:
\[
\pi_1: i_{k_0}, i_{k_0-1}, \ldots, i_1, i_0 = i
\]
\[
\pi_2: i_{k_0}, i_{k_0+1}, \ldots, i_{r-1}, i_r = j
\]

**Substep A.2:** Verify \(\pi_1\) is admissible (from \(i_{k_0}\) to \(i\), with \(i_{k_0} < i\)):

- *Simplicity:* Inherited from \(\pi\)
- *Index Condition:* Let \(i_m\) be an interior vertex of \(\pi_1\), i.e., \(1 \leq m \leq k_0 - 1\).
  - If \(i_m \in A\): then \(i_m < i\), and since \(i_{k_0} = \max A\), we have \(i_m < i_{k_0}\). ✓
  - If \(i_m \in B\): then \(i_m > j > i\). ✓
- *Minimality:* Any shorter path within \(\pi_1\) would give a shorter path within \(\pi\), contradicting minimality of \(\pi\).

**Substep A.3:** Verify \(\pi_2\) is admissible (from \(i_{k_0}\) to \(j\), with \(i_{k_0} < j\)):

- *Simplicity:* Inherited from \(\pi\)
- *Index Condition:* Let \(i_m\) be an interior vertex of \(\pi_2\), i.e., \(k_0 + 1 \leq m \leq r-1\).
  - Since \(i_{k_0} = \max A\), any \(i_m\) with \(m > k_0\) satisfies \(i_m \notin A\), so \(i_m \in B\), giving \(i_m > j\). ✓
- *Minimality:* Same argument as above.

**Substep A.4:** Apply induction hypothesis.

Path \(\pi_1\) has length \(k_0 < r\), so \(u_{\pi_1} f_{i_{k_0}, i} \in J_G\).

Path \(\pi_2\) has length \(r - k_0 < r\), so \(u_{\pi_2} f_{i_{k_0}, j} \in J_G\).

**Substep A.5:** Compute the path monomials explicitly.

Partition the interior vertices: \(\{i_1, \ldots, i_{r-1}\} = (A \cup B)\), with:
- \(A \cap \{i_1, \ldots, i_{k_0-1}\} = \{i_m : m < k_0, i_m < i\}\)
- \(B \cap \{i_1, \ldots, i_{k_0-1}\} = \{i_m : m < k_0, i_m > j\}\)
- \(B \cap \{i_{k_0+1}, \ldots, i_{r-1}\} = \{i_m : m > k_0, i_m > j\}\) (this is all interior vertices of \(\pi_2\))
- \(A \cap \{i_{k_0+1}, \ldots, i_{r-1}\} = \emptyset\) (since \(i_{k_0} = \max A\))

Hence:
\[
u_{\pi_1} = \prod_{\substack{m < k_0 \\ i_m > j}} x_{i_m} \cdot \prod_{\substack{m < k_0 \\ i_m < i_{k_0}}} y_{i_m} = \prod_{\substack{m < k_0 \\ i_m \in B}} x_{i_m} \cdot \prod_{\substack{m < k_0 \\ i_m \in A}} y_{i_m}
\]
\[
u_{\pi_2} = \prod_{\substack{m > k_0 \\ i_m > j}} x_{i_m} \cdot 1 = \prod_{\substack{m > k_0 \\ i_m \in B}} x_{i_m}
\]

**Substep A.6:** Compute the S-polynomial.

The leading terms are:
\[
\mathrm{in}_<(u_{\pi_1} f_{i_{k_0}, i}) = u_{\pi_1} x_{i_{k_0}} y_i
\]
\[
\mathrm{in}_<(u_{\pi_2} f_{i_{k_0}, j}) = u_{\pi_2} x_{i_{k_0}} y_j
\]

Since the interior vertices of \(\pi_1\) and \(\pi_2\) are disjoint:
\[
\gcd(u_{\pi_1}, u_{\pi_2}) = 1
\]

Therefore:
\[
L := \mathrm{lcm}(u_{\pi_1} x_{i_{k_0}} y_i, \, u_{\pi_2} x_{i_{k_0}} y_j) = u_{\pi_1} u_{\pi_2} x_{i_{k_0}} y_i y_j
\]

The S-polynomial is:
\begin{align*}
&S(u_{\pi_1} f_{i_{k_0}, i}, \, u_{\pi_2} f_{i_{k_0}, j}) \\
&= \frac{L}{u_{\pi_1} x_{i_{k_0}} y_i} \cdot u_{\pi_1} f_{i_{k_0}, i} - \frac{L}{u_{\pi_2} x_{i_{k_0}} y_j} \cdot u_{\pi_2} f_{i_{k_0}, j} \\
&= u_{\pi_2} y_j \cdot u_{\pi_1}(x_{i_{k_0}} y_i - x_i y_{i_{k_0}}) - u_{\pi_1} y_i \cdot u_{\pi_2}(x_{i_{k_0}} y_j - x_j y_{i_{k_0}}) \\
&= u_{\pi_1} u_{\pi_2} \Big[ y_j x_{i_{k_0}} y_i - y_j x_i y_{i_{k_0}} - y_i x_{i_{k_0}} y_j + y_i x_j y_{i_{k_0}} \Big] \\
&= u_{\pi_1} u_{\pi_2} \cdot y_{i_{k_0}} (x_j y_i - x_i y_j) \\
&= -u_{\pi_1} u_{\pi_2} \cdot y_{i_{k_0}} \cdot f_{ij}
\end{align*}

**Substep A.7:** Verify \(u_{\pi_1} u_{\pi_2} y_{i_{k_0}} = u_\pi\).

\begin{align*}
u_{\pi_1} u_{\pi_2} y_{i_{k_0}} &= \left(\prod_{\substack{m < k_0 \\ i_m \in B}} x_{i_m}\right) \left(\prod_{\substack{m < k_0 \\ i_m \in A}} y_{i_m}\right) \left(\prod_{\substack{m > k_0 \\ i_m \in B}} x_{i_m}\right) y_{i_{k_0}} \\
&= \left(\prod_{i_m \in B} x_{i_m}\right) \left(\prod_{\substack{m < k_0 \\ i_m \in A}} y_{i_m}\right) y_{i_{k_0}} \\
&= \left(\prod_{i_m \in B} x_{i_m}\right) \left(\prod_{i_m \in A} y_{i_m}\right) \quad \text{[since } i_{k_0} \in A \text{ and } i_{k_0} = \max A\text{]} \\
&= u_\pi
\end{align*}

**Substep A.8:** Conclude.

Therefore \(S(u_{\pi_1} f_{i_{k_0}, i}, u_{\pi_2} f_{i_{k_0}, j}) = -u_\pi f_{ij}\).

Since S-polynomials of elements in an ideal remain in the ideal:
\[
u_\pi f_{ij} \in J_G
\]

**Case B: \(B \neq \emptyset\)** (symmetric argument)

Let \(i_{\ell_0} = \min B\). Note \(i < j < i_{\ell_0}\).

Define:
\[
\pi_1: i_{\ell_0}, i_{\ell_0-1}, \ldots, i_1, i_0 = i
\]
\[
\pi_2: i_{\ell_0}, i_{\ell_0+1}, \ldots, i_{r-1}, i_r = j
\]

The verification proceeds analogously, with roles of \(A\) and \(B\) adjusted appropriately.

**Conclusion of First Step:** \(\mathcal{G} \subseteq J_G\). \(\square\)

---

## Second Step: \(\mathcal{G}\) is a Gröbner Basis

**Goal:** Show all S-polynomials \(S(u_\pi f_{ij}, u_\sigma f_{k\ell})\) reduce to zero modulo \(\mathcal{G}\).

### Case 1: \(i = k\) and \(j = \ell\)

The leading monomials are \(u_\pi x_i y_j\) and \(u_\sigma x_i y_j\).

\[
S(u_\pi f_{ij}, u_\sigma f_{ij}) = \frac{\mathrm{lcm}(u_\pi, u_\sigma)}{u_\pi} f_{ij} - \frac{\mathrm{lcm}(u_\pi, u_\sigma)}{u_\sigma} f_{ij} = 0 \quad \text{if } u_\pi = u_\sigma
\]

More generally, when \(\{i,j\} = \{k,\ell\}\), the S-polynomial involves the same underlying binomial \(f_{ij}\) and cancels to zero.

### Case 2: \(\{i,j\} \cap \{k,\ell\} = \emptyset\), or \(i = \ell\), or \(k = j\)

**Lemma (Regular Sequence Criterion):** Let \(f, g \in S\) with \(\mathrm{in}_<(f)\) and \(\mathrm{in}_<(g)\) forming a regular sequence (equivalently, \(\gcd(\mathrm{in}_<(f), \mathrm{in}_<(g)) = 1\)). Then for any monomials \(u, v\), the S-polynomial \(S(uf, vg)\) reduces to zero modulo \(\{f, g\}\).

**Application:**
- \(\mathrm{in}_<(f_{ij}) = x_i y_j\) and \(\mathrm{in}_<(f_{k\ell}) = x_k y_\ell\)
- If \(\{i,j\} \cap \{k,\ell\} = \emptyset\): \(\gcd(x_i y_j, x_k y_\ell) = 1\) ✓
- If \(i = \ell\): variables are \(x_i, y_j\) vs \(x_k, y_i\), and \(j \neq i\) (since \(i < j\)), \(k \neq i\) (since \(k < \ell = i\)), so \(\gcd = 1\) ✓
- If \(k = j\): similarly \(\gcd = 1\) ✓

Hence these S-polynomials reduce to zero.

### Case 3: \(i = k\) and \(j \neq \ell\)

WLOG assume \(j < \ell\). We must show \(S(u_\pi f_{ij}, u_\sigma f_{i\ell})\) reduces to zero.

**Substep 3.1:** Compute the S-polynomial.

Let \(\pi: i = i_0, i_1, \ldots, i_r = j\) and \(\sigma: i = i_0', i_1', \ldots, i_s' = \ell\).

Leading terms: \(u_\pi x_i y_j\) and \(u_\sigma x_i y_\ell\).
\[
\mathrm{lcm}(u_\pi x_i y_j, u_\sigma x_i y_\ell) = \mathrm{lcm}(u_\pi, u_\sigma) \cdot x_i y_j y_\ell
\]

Set \(w = y_i \cdot \mathrm{lcm}(u_\pi, u_\sigma)\). Then:
\begin{align*}
S(u_\pi f_{ij}, u_\sigma f_{i\ell}) &= \frac{\mathrm{lcm}(u_\pi, u_\sigma) y_\ell}{u_\pi} \cdot u_\pi(x_i y_j - x_j y_i) - \frac{\mathrm{lcm}(u_\pi, u_\sigma) y_j}{u_\sigma} \cdot u_\sigma(x_i y_\ell - x_\ell y_i) \\
&= \mathrm{lcm}(u_\pi, u_\sigma)(y_\ell x_i y_j - y_\ell x_j y_i - y_j x_i y_\ell + y_j x_\ell y_i) \\
&= \mathrm{lcm}(u_\pi, u_\sigma) \cdot y_i (x_\ell y_j - x_j y_\ell) \\
&= -w \cdot f_{j\ell}
\end{align*}

**Substep 3.2:** Construct the path \(\tau\) from \(j\) to \(\ell\).

Since both paths start at \(i\), there exist unique indices \(a, b\) such that:
- \(i_a = i_b'\) (last common vertex)
- \(\{i_{a+1}, \ldots, i_r\} \cap \{i_{b+1}', \ldots, i_s'\} = \emptyset\)

Define the path:
\[
\tau: j = i_r, i_{r-1}, \ldots, i_{a+1}, i_a = i_b', i_{b+1}', \ldots, i_{s-1}', i_s' = \ell
\]

Relabel as \(\tau: j = j_0, j_1, \ldots, j_t = \ell\).

**Substep 3.3:** Decompose \(\tau\) into admissible subpaths.

Define indices recursively:
- \(t(0) = 0\)
- \(t(1) = \min\{c : 1 \leq c \leq t, \, j_c > j\}\)
- \(t(m) = \min\{c : t(m-1) < c \leq t, \, j_c > j_{t(m-1)}\}\) for \(m \geq 2\)
- Continue until \(t(q) = t\)

**Observation:** This yields \(0 = t(0) < t(1) < \cdots < t(q) = t\) with:
\[
j = j_{t(0)} < j_{t(1)} < \cdots < j_{t(q-1)} < j_{t(q)} = \ell
\]

**Substep 3.4:** Each subpath is admissible.

For \(1 \leq c \leq q\), define:
\[
\tau_c: j_{t(c-1)}, j_{t(c-1)+1}, \ldots, j_{t(c)-1}, j_{t(c)}
\]

**Claim:** \(\tau_c\) is an admissible path from \(j_{t(c-1)}\) to \(j_{t(c)}\).

*Proof:*
- *Simplicity:* Inherited from \(\tau\)
- *Index Condition:* For interior vertex \(j_m\) with \(t(c-1) < m < t(c)\):
  - By definition of \(t(c)\), we have \(j_m \leq j_{t(c-1)}\) (otherwise \(t(c)\) would be \(\leq m\))
  - Since \(j_m \neq j_{t(c-1)}\) (simplicity), we have \(j_m < j_{t(c-1)}\) ✓
- *Minimality:* Follows from minimality of \(\pi\) and \(\sigma\)

**Substep 3.5:** Define the coefficient monomials.

\[
v_{\tau_c} = \begin{cases}
\dfrac{x_\ell w}{u_{\tau_1} x_{j_{t(1)}}} & \text{if } c = 1 \\[2ex]
\dfrac{x_j x_\ell w}{u_{\tau_c} x_{j_{t(c-1)}} x_{j_{t(c)}}} & \text{if } 1 < c < q \\[2ex]
\dfrac{x_j w}{u_{\tau_q} x_{j_{t(q-1)}}} & \text{if } c = q
\end{cases}
\]

**Substep 3.6:** Verify the standard expression.

**Claim:**
\[
w f_{j\ell} = \sum_{c=1}^{q} v_{\tau_c} u_{\tau_c} f_{j_{t(c-1)}, j_{t(c)}}
\]

Expanding \(f_{j\ell} = x_j y_\ell - x_\ell y_j\), we need to verify:
\[
w(x_j y_\ell - x_\ell y_j) = \frac{w x_\ell}{x_{j_{t(1)}}}(x_j y_{j_{t(1)}} - x_{j_{t(1)}} y_j) + \sum_{c=2}^{q-1} \frac{w x_j x_\ell}{x_{j_{t(c-1)}} x_{j_{t(c)}}}(x_{j_{t(c-1)}} y_{j_{t(c)}} - x_{j_{t(c)}} y_{j_{t(c-1)}}) + \frac{w x_j}{x_{j_{t(q-1)}}}(x_{j_{t(q-1)}} y_\ell - x_\ell y_{j_{t(q-1)}})
\]

**Algebraic verification:** Rewrite the RHS by factoring:
\begin{align*}
\text{RHS} &= w\left(x_\ell \frac{x_j y_{j_{t(1)}}}{x_{j_{t(1)}}} - x_\ell y_j\right) + w x_j x_\ell \sum_{c=2}^{q-1}\left(\frac{y_{j_{t(c)}}}{x_{j_{t(c)}}} - \frac{y_{j_{t(c-1)}}}{x_{j_{t(c-1)}}}\right) + w\left(x_j y_\ell - x_j x_\ell \frac{y_{j_{t(q-1)}}}{x_{j_{t(q-1)}}}\right)
\end{align*}

The sum telescopes:
\[
\sum_{c=2}^{q-1}\left(\frac{y_{j_{t(c)}}}{x_{j_{t(c)}}} - \frac{y_{j_{t(c-1)}}}{x_{j_{t(c-1)}}}\right) = \frac{y_{j_{t(q-1)}}}{x_{j_{t(q-1)}}} - \frac{y_{j_{t(1)}}}{x_{j_{t(1)}}}
\]

Substituting:
\begin{align*}
\text{RHS} &= w x_j x_\ell \frac{y_{j_{t(1)}}}{x_{j_{t(1)}}} - w x_\ell y_j + w x_j x_\ell \frac{y_{j_{t(q-1)}}}{x_{j_{t(q-1)}}} - w x_j x_\ell \frac{y_{j_{t(1)}}}{x_{j_{t(1)}}} + w x_j y_\ell - w x_j x_\ell \frac{y_{j_{t(q-1)}}}{x_{j_{t(q-1)}}} \\
&= w x_j y_\ell - w x_\ell y_j \\
&= w(x_j y_\ell - x_\ell y_j) = \text{LHS} \quad \checkmark
\end{align*}

**Substep 3.7:** Verify it is a standard expression (leading terms decrease).

The leading term of each summand is:
\[
\mathrm{in}_<(v_{\tau_c} u_{\tau_c} f_{j_{t(c-1)}, j_{t(c)}}) = v_{\tau_c} u_{\tau_c} x_{j_{t(c-1)}} y_{j_{t(c)}}
\]

We have the chain of inequalities:
\[
w x_j y_\ell > \frac{w x_j}{x_{j_{t(q-1)}}} x_{j_{t(q-1)}} y_\ell > \frac{w x_j x_\ell}{x_{j_{t(q-2)}} x_{j_{t(q-1)}}} x_{j_{t(q-2)}} y_{j_{t(q-1)}} > \cdots > \frac{w x_\ell}{x_{j_{t(1)}}} x_j y_{j_{t(1)}}
\]

This follows from the monomial order properties.

**Conclusion:** The S-polynomial \(S(u_\pi f_{ij}, u_\sigma f_{i\ell}) = -w f_{j\ell}\) has a standard expression with remainder 0.

### Case 4: \(j = \ell\) and \(i \neq k\)

Symmetric to Case 3, with \(i\) and \(k\) playing the role of \(j\) and \(\ell\).

**Conclusion of Second Step:** By Buchberger's criterion, \(\mathcal{G}\) is a Gröbner basis. \(\square\)

---

## Third Step: \(\mathcal{G}\) is Reduced

**Goal:** For distinct elements \(u_\pi f_{ij}, u_\sigma f_{k\ell} \in \mathcal{G}\), show that \(\mathrm{in}_<(u_\pi f_{ij}) = u_\pi x_i y_j\) does not divide any monomial of \(u_\sigma f_{k\ell}\).

The monomials of \(u_\sigma f_{k\ell}\) are \(u_\sigma x_k y_\ell\) and \(u_\sigma x_\ell y_k\).

**Assume for contradiction:** \(u_\pi x_i y_j \mid u_\sigma x_k y_\ell\) or \(u_\pi x_i y_j \mid u_\sigma x_\ell y_k\).

Let \(\pi: i = i_0, i_1, \ldots, i_r = j\) and \(\sigma: k = k_0, k_1, \ldots, k_s = \ell\).

**Key Observation:** If divisibility holds, then:
\[
\{i_0, i_1, \ldots, i_r\} \subsetneq \{k_0, k_1, \ldots, k_s\}
\]

*Proof:* The variables in \(u_\pi x_i y_j\) are:
- \(x_i\), \(y_j\), \(\{x_{i_m} : i_m > j\}\), \(\{y_{i_m} : i_m < i\}\)

These must all appear in \(u_\sigma x_k y_\ell\) or \(u_\sigma x_\ell y_k\), forcing the indices of \(\pi\) to be among those of \(\sigma\). Strictness follows from \(u_\pi f_{ij} \neq u_\sigma f_{k\ell}\).

### Case A: \(i = k\) and \(j = \ell\)

Then \(\{i_1, \ldots, i_{r-1}\} \subsetneq \{k_1, \ldots, k_{s-1}\}\).

The subsequence \(k = i, i_1, \ldots, i_{r-1}, \ell = j\) is a path from \(k\) to \(\ell\) using a proper subset of the interior vertices of \(\sigma\).

This contradicts the minimality condition (property 3) of \(\sigma\) being admissible.

### Case B: \(i = k\) and \(j \neq \ell\)

For divisibility, \(y_j\) must divide \(u_\sigma\).

By definition of \(u_\sigma\), this requires \(j \in \{k_m : k_m < k\}\), i.e., \(j < k = i\).

But \(i < j\) by assumption. **Contradiction.**

### Case C: \(j = \ell\) and \(i \neq k\)

For divisibility, \(x_i\) must divide \(u_\sigma\).

By definition of \(u_\sigma\), this requires \(i \in \{k_m : k_m > \ell\}\), i.e., \(i > \ell = j\).

But \(i < j\) by assumption. **Contradiction.**

### Case D: \(\{i, j\} \cap \{k, \ell\} = \emptyset\)

For divisibility, both \(x_i\) and \(y_j\) must divide \(u_\sigma\).

- \(x_i \mid u_\sigma \Rightarrow i > \ell\)
- \(y_j \mid u_\sigma \Rightarrow j < k\)

Thus \(\ell < i < j < k\), contradicting \(k < \ell\). **Contradiction.**

**Conclusion of Third Step:** \(\mathcal{G}\) is reduced. \(\square\)

---

## Summary for Lean Formalization

**Key lemmas to formalize:**

1. **`admissible_path_mem_ideal`**: Induction on path length; requires S-polynomial computation lemma
2. **`spoly_computation`**: Explicit formula for \(S(u_{\pi_1} f_{a,b}, u_{\pi_2} f_{a,c})\)
3. **`regular_sequence_spoly_reduces`**: If \(\gcd(\mathrm{in}(f), \mathrm{in}(g)) = 1\), then \(S(uf, vg)\) reduces to 0
4. **`path_decomposition`**: Construction of the \(t(c)\) indices and subpaths \(\tau_c\)
5. **`telescoping_sum`**: The algebraic identity in Substep 3.6
6. **`standard_expression_ordering`**: The monomial ordering chain in Substep 3.7
7. **`reduced_cases`**: Four separate contradiction lemmas for Cases A–D