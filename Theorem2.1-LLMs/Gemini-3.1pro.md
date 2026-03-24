**Proof of Theorem**

**Step 1: \(\mathcal{G} \subset J_G\)**

Let \(\pi: i=i_0, i_1, \dots, i_{r-1}, i_r=j\) be an admissible path in \(G\) with \(i < j\). We prove \(u_\pi f_{ij} \in J_G\) by induction on \(r\). 
If \(r = 1\), then \(\pi\) is the edge \(\{i, j\}\), \(u_\pi = 1\), and \(u_\pi f_{ij} = f_{ij} \in J_G\).

Assume \(r > 1\). Define \(A = \{ i_k \mid i_k < i, 0 < k < r \}\) and \(B = \{ i_\ell \mid i_\ell > j, 0 < \ell < r \}\). By admissibility of \(\pi\), every internal vertex belongs to \(A \cup B\). Since \(r > 1\), \(A \cup B \neq \emptyset\).

Case 1: \(A \neq \emptyset\). Let \(k_0\) be the index such that \(i_{k_0} = \max A\). The path \(\pi\) splits into two admissible paths: \(\pi_1: i_{k_0}, i_{k_0-1}, \dots, i_0 = i\) and \(\pi_2: i_{k_0}, i_{k_0+1}, \dots, i_r = j\). 
By the induction hypothesis, \(u_{\pi_1} f_{i_{k_0}, i} \in J_G\) and \(u_{\pi_2} f_{i_{k_0}, j} \in J_G\). 
Consider the algebraic identity:
\[
y_{i_{k_0}} f_{ij} = y_i f_{i_{k_0}, j} - y_j f_{i_{k_0}, i}
\]
Since \(i_{k_0} \in A\), we have \(i_{k_0} < i\), which means \(y_{i_{k_0}}\) divides \(u_\pi\). Multiplying the identity by \(\frac{u_\pi}{y_{i_{k_0}}}\) yields:
\[
u_\pi f_{ij} = \left( \frac{u_\pi y_i}{y_{i_{k_0}} u_{\pi_2}} \right) u_{\pi_2} f_{i_{k_0}, j} - \left( \frac{u_\pi y_j}{y_{i_{k_0}} u_{\pi_1}} \right) u_{\pi_1} f_{i_{k_0}, i}
\]
By construction of \(\pi_1\) and \(\pi_2\), the bracketed coefficients are monomials, demonstrating \(u_\pi f_{ij} \in J_G\).

Case 2: \(B \neq \emptyset\). Let \(\ell_0\) be the index such that \(i_{\ell_0} = \min B\). A symmetric argument applies using the identity \(x_{i_{\ell_0}} f_{ij} = x_i f_{j, i_{\ell_0}} - x_j f_{i, i_{\ell_0}}\), and the fact that \(x_{i_{\ell_0}}\) divides \(u_\pi\). Thus, \(\mathcal{G} \subset J_G\).

**Step 2: \(\mathcal{G}\) is a Gröbner basis**

We use Buchberger's criterion. Let \(g_1 = u_\pi f_{ij}\) and \(g_2 = u_\sigma f_{k\ell}\) be in \(\mathcal{G}\) with \(i < j\) and \(k < \ell\). We must show their S-polynomial \(S(g_1, g_2)\) reduces to \(0\) modulo \(\mathcal{G}\).

*   **Case 2.1:** \(i = k\) and \(j = \ell\). If \(\pi = \sigma\), \(S(g_1, g_2) = 0\). If \(\pi \neq \sigma\), the leading monomials are \(u_\pi x_i y_j\) and \(u_\sigma x_i y_j\). The S-polynomial trivially reduces to \(0\).
*   **Case 2.2:** \(\{i, j\} \cap \{k, \ell\} = \emptyset\), or \(i = \ell\), or \(k = j\). The leading monomials \(\mathrm{in}_<(f_{ij}) = x_i y_j\) and \(\mathrm{in}_<(f_{k\ell}) = x_k y_\ell\) share no variables, so they are coprime. By standard Gröbner basis properties, \(S(g_1, g_2)\) reduces to \(0\).
*   **Case 2.3:** \(i = k\) and \(j \neq \ell\). Assume without loss of generality that \(j < \ell\). The leading monomials are \(u_\pi x_i y_j\) and \(u_\sigma x_i y_\ell\). 
Let \(w = y_i \mathrm{lcm}(u_\pi, u_\sigma)\). The S-polynomial is exactly evaluated as:
\[
S(u_\pi f_{ij}, u_\sigma f_{i\ell}) = \frac{x_i y_j y_\ell \mathrm{lcm}(u_\pi, u_\sigma)}{u_\pi x_i y_j} u_\pi f_{ij} - \frac{x_i y_j y_\ell \mathrm{lcm}(u_\pi, u_\sigma)}{u_\sigma x_i y_\ell} u_\sigma f_{i\ell} = -w f_{j\ell}
\]
We must find a standard representation of \(w f_{j\ell} = w(x_j y_\ell - x_\ell y_j)\) with remainder \(0\). 
Let \(\pi: i=i_0, \dots, i_r=j\) and \(\sigma: i=i_0', \dots, i_s'=\ell\). Since both start at \(i\), let \(a\) and \(b\) be the uniquely determined indices such that \(i_a = i_b'\) and \(\{i_{a+1}, \dots, i_r\} \cap \{i_{b+1}', \dots, i_s'\} = \emptyset\). 
Concatenate the reverse of \(\pi\) (from \(j\) to \(i_a\)) and \(\sigma\) (from \(i_b'\) to \(\ell\)) to form a path \(\tau: j=j_0, j_1, \dots, j_t=\ell\).

Extract a sequence of indices \(0 = t(0) < t(1) < \dots < t(q) = t\) as follows:
Define \(t(1)\) as the unique index such that \(j_{t(1)} = \min \{ j_c \mid j_c > j, 1 \le c \le t \}\). 
Iteratively define \(t(k)\) such that \(j_{t(k)} = \min \{ j_c \mid j_c > j, t(k-1) < c \le t \}\), stopping when \(j_{t(q)} = \ell\). 
This produces a strictly increasing sequence of vertices \(j = j_{t(0)} < j_{t(1)} < \dots < j_{t(q)} = \ell\). For each \(1 \le c \le q\), the subpath \(\tau_c\) from \(j_{t(c-1)}\) to \(j_{t(c)}\) is admissible.

We assert the following telescoping identity is a standard representation:
\[
w(x_j y_\ell - x_\ell y_j) = \frac{w x_\ell}{x_{j_{t(1)}}} f_{j, j_{t(1)}} + \sum_{c=2}^{q-1} \frac{w x_j x_\ell}{x_{j_{t(c-1)}} x_{j_{t(c)}}} f_{j_{t(c-1)}, j_{t(c)}} + \frac{w x_j}{x_{j_{t(q-1)}}} f_{j_{t(q-1)}, \ell}
\]
Expanding the right hand side algebraically directly yields \(w(x_j y_\ell - x_\ell y_j)\) via cancellation of consecutive terms. 
By the construction of \(\tau\), the coefficient multipliers are all valid polynomials, and each is a multiple of the respective \(u_{\tau_c}\) (because \(w = y_i \mathrm{lcm}(u_\pi, u_\sigma)\) absorbs all required variables).
The initial monomials of the summands strictly decrease in the term order because \(j_{t(c-1)} < j_{t(c)}\) implies \(x_{j_{t(c-1)}} > x_{j_{t(c)}}\), leading to:
\[
w x_j y_\ell > \frac{w x_j x_\ell}{x_{j_{t(q-2)}} x_{j_{t(q-1)}}} x_{j_{t(q-2)}} y_{j_{t(q-1)}} > \dots > \frac{w x_\ell}{x_{j_{t(1)}}} x_j y_{j_{t(1)}}
\]
This strictly decreasing sequence confirms it is a standard representation with remainder \(0\).
*   **Case 2.4:** \(i \neq k\) and \(j = \ell\). The proof follows identically to Case 2.3 by symmetry.

**Step 3: \(\mathcal{G}\) is reduced**

Suppose \(u_\pi f_{ij}\) and \(u_\sigma f_{k\ell}\) belong to \(\mathcal{G}\) (with \(i < j\) and \(k < \ell\)) and \(u_\pi f_{ij} \neq u_\sigma f_{k\ell}\). Let \(\pi: i=i_0, \dots, i_r=j\) and \(\sigma: k=k_0, \dots, k_s=\ell\). Assume for contradiction that the leading term \(u_\pi x_i y_j\) divides a term of \(u_\sigma f_{k\ell}\) (either \(u_\sigma x_k y_\ell\) or \(u_\sigma x_\ell y_k\)). 
Because one divides the other and the binomials are distinct, the vertex set \(\{i_0, \dots, i_r\}\) must be a proper subset of \(\{k_0, \dots, k_s\}\).

*   If \(i = k\) and \(j = \ell\): The internal vertices \(\{i_1, \dots, i_{r-1}\}\) form a proper subset of \(\{k_1, \dots, k_{s-1}\}\) which still connects \(i\) to \(j\). This violates the admissibility condition (iii) for \(\sigma\).
*   If \(i = k\) and \(j \neq \ell\): Since \(x_i y_j\) divides \(u_\sigma x_i y_\ell\), \(y_j\) must divide \(u_\sigma y_\ell\). As \(j \neq \ell\), \(y_j\) strictly divides \(u_\sigma\). By the definition of \(u_\sigma\), any \(y\)-variable dividing it must have an index strictly less than its starting vertex \(k\). Therefore, \(j < k\). But \(k = i < j\), yielding \(j < j\), a contradiction.
*   If \(\{i, j\} \cap \{k, \ell\} = \emptyset\): \(x_i y_j\) divides \(u_\sigma x_k y_\ell\), forcing both \(x_i\) and \(y_j\) to divide \(u_\sigma\). By definition of \(u_\sigma\), an \(x\)-variable divides it only if its index is \(> \ell\), so \(i > \ell\). A \(y\)-variable divides it only if its index is \(< k\), so \(j < k\). Combining these gives \(j < k < \ell < i\). However, we require \(i < j\), yielding a contradiction.

Therefore, no term of any generator divides the leading term of another, proving \(\mathcal{G}\) is a reduced Gröbner basis.