# Guide: Rich Mathematical Homepage and Section Pages

## Task

Plan a stronger public-facing documentation site for the BEI formalization.

The target is a website that presents much more of the mathematics directly,
while still linking to the live Lean code.

The key design idea is:

- for each paper theorem/result, show the paper statement beautifully rendered;
- alongside the Lean formalization of that result;
- together with status, fidelity, and proof/source links.


## Current site stack

The existing site is a small Jekyll site rooted in:

- `docs/`

Current key files:

- `docs/_config.yml`
- `docs/index.md`
- `docs/overview.md`
- `docs/section-1.md`
- `docs/section-2.md`
- `docs/section-3.md`
- `docs/section-4.md`
- `docs/toMathlib.md`
- `docs/assets/main.scss`

**Phase 1 infrastructure landed (date unrecorded):** the structured
theorem data layer is partially in place:

- `docs/_data/section1.yml`
- `docs/_data/homepage_featured.yml`
- `docs/_includes/theorem_compare.html`
- `docs/_includes/theorem_highlight.html`

The Section 1 pilot uses these. Sections 2–4 still ship hand-written
status prose. The remaining scope of this guide is therefore narrowed
to: extend the data model and `_includes` partials to Sections 2–4
(Phase 3 below) and the homepage redesign (Phase 4).


## Main goal

Move the site from static status prose to structured theorem-comparison pages.

The ideal end state is:

1. a mathematically informative homepage;
2. section pages built from theorem metadata;
3. side-by-side paper/Lean comparison cards;
4. explicit fidelity/status badges;
5. direct links to the Lean declarations and proof files.


## Recommended content model

Create a structured theorem data source, for example:

- `docs/_data/theorems.yml`

or one file per section, for example:

- `docs/_data/section1.yml`
- `docs/_data/section2.yml`
- `docs/_data/section3.yml`
- `docs/_data/section4.yml`

Each theorem entry should contain fields like:

- `section`
- `paper_label`
- `paper_title`
- `paper_statement_tex`
- `paper_commentary`
- `lean_name`
- `lean_statement`
- `lean_file`
- `lean_url`
- `fidelity`
- `status`
- `notes`

This is the key anti-staleness decision: theorem content should live in one
structured place, not be copied manually across pages.


## Recommended page structure

### Homepage

The homepage should become a mathematical portal rather than only a status page.

Suggested structure:

1. hero section with the paper/project identity;
2. current formalization summary;
3. “Explore by section” cards;
4. a featured “Paper vs Lean” strip showing a few representative theorem cards;
5. current paper-level blockers;
6. links to the full Lean code and `FORMALIZATION_MAP.md`.

### Section pages

Each section page should have:

1. a short mathematical intro;
2. a compact theorem map / summary row;
3. theorem comparison cards, one per result;
4. a short “status and caveats” block for partial or surrogate-only results.


## The key UI component

Create a reusable theorem comparison include, for example:

- `docs/_includes/theorem_compare.html`

It should render:

1. theorem header:
   - paper label;
   - theorem title;
   - status badge;
   - fidelity badge.

2. body:
   - left column: paper statement rendered with MathJax/KaTeX;
   - right column: Lean formalization summary and theorem name.

3. footer:
   - link to the Lean file;
   - optional link to the exact declaration;
   - explanatory notes about mismatches or packaging choices.

On mobile, the two-column layout should stack with the paper statement first.


## Math rendering

Add math rendering to the Jekyll site using MathJax or KaTeX.

Requirements:

- display equations for paper statements;
- inline notation in commentary blocks;
- safe fallback if a page has no math.

This should be done at the site/include level, not by ad hoc per-page scripts.


## Visual language

The site should make paper-faithfulness visible.

Use clear visual distinctions for:

- `Exact`
- `Equivalent`
- `Partial`
- `Blocked`
- `Surrogate only`

This matters especially in Section 3, where several results are only represented
via the local equidimensional surrogate rather than the paper’s full
Cohen–Macaulay statement.


## Recommended implementation order

### Phase 1: infrastructure

1. add math rendering;
2. add theorem comparison include;
3. add theorem data files;
4. add CSS for comparison cards and badges.

### Phase 2: one pilot page

Start with:

- `docs/section-1.md`

because Theorem 1.1 is central, complete, and easy to present clearly.

The pilot should include:

- one side-by-side theorem card for Theorem 1.1;
- a proof link to `BEI/ClosedGraphs.lean`;
- the paper statement rendered mathematically;
- the Lean theorem name and statement summary.

### Phase 3: section conversion

Convert the other section pages to the same pattern, especially:

- Section 3, where the fidelity/status distinctions matter most.

### Phase 4: homepage redesign

Once the theorem card component exists, redesign:

- `docs/index.md`

to feature theorem comparisons, section summaries, and current blockers.


## Risks

### Risk 1: content drift

If the paper statement and Lean statement are copied manually across many pages,
the site will drift out of sync with the code.

Mitigation:

- keep theorem content in `_data/`;
- keep page templates thin;
- prefer generated cards over hand-written repetition.

### Risk 2: overly literal Lean display

Raw Lean declarations are useful, but not always pleasant to read.

Mitigation:

- show a readable Lean summary by default;
- make the exact theorem name and source link prominent;
- optionally add a collapsible raw declaration later.

### Risk 3: overbuilding too early

The site should not turn into a full static-site generator project inside the
formalization repo.

Mitigation:

- implement one pilot theorem card first;
- only generalize after the pilot looks good.


## Definition of done

Best outcome:

- the homepage and section pages are theorem-driven;
- paper statements render beautifully;
- Lean formalizations are shown side by side with proof links;
- fidelity and status are visually explicit.

Minimum useful outcome:

- one polished pilot implementation on Section 1 / Theorem 1.1;
- a reusable theorem comparison component;
- a data model ready for later expansion.
