# AGENTS.md — INFRA stage (bench-only infrastructure sprint)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **INFRA** stage (only-bench):
- Build minimal missing theory/infrastructure required to solve a single bench problem under `Question_bench/`.
- Keep infra small, reusable, and **strictly necessary** for the target bench file.
- When generating infra plan JSON, write each item’s `content` as **precise, rigorous mathematical natural language** (no Lean code), with explicit hypotheses and conclusions.
- For plan JSON items with `env != def`/`abbrev`, also include a detailed English `proof` sketch (stepwise, dependencies-aware).
- Plan items must be **provable within the current infra plan** (mathlib + earlier items in this plan); avoid items that would require further infra beyond this plan.
- Infra plan dependencies must be **acyclic**: no circular dependencies; each item should only depend on earlier items.

This file is the INFRA-stage rules source; the orchestrator swaps `M2F/AGENTS.md` to this before Codex calls when an infra sprint is active.

---

## A. Hard constraints (do not violate)

1) Edit scope (bench + its infra only)
- You may edit:
  - the target bench file `Question_bench/.../<id>.lean` (or its `_partXX.lean`), and
  - any files under the sibling directory `Question_bench/.../infra_<id>/`.
- Do not touch any other file. Do not rename/move files.
- `infra_<id>/Main.lean` is reserved as the entry/aggregator file (imports other infra files).

2) **`sorry` policy (infra)**
- `:= sorry` is allowed for scaffolding (including in `infra_<id>/**/*.lean`).
- If a lemma is not provable, do **not** fake it: instead, change strategy (weaken the lemma, add missing hypotheses, or avoid needing it).

3) Public API cap + must-list discipline
- Public infra API must be tracked in `infra_<id>/PUBLIC_API.json` (a JSON array).
- Keep the public API small (default cap is 30, enforced by the orchestrator).
- Do not add “extra” public theorems: every public API item must be used by `<id>.lean` (directly or via a short chain).

4) No embedded proof fragments inside terms
- Do not embed proofs inside a larger term (e.g. `⟨..., by ...⟩`, `(by ...)` as a subterm).
- It is OK to use `by ...` as the *top-level proof* of a `lemma` / `theorem`.
- If a term construction requires a proof obligation, introduce a **separate named lemma** and reference it.

5) Definitions must be proof-free
- Inside a `def` / `abbrev` body, do not use `by ...`.
- If a definition body must be a placeholder, use `:= sorry` in the **bench file only** (never in infra).

6) No axiom
- Never introduce `axiom`.

7) Docstrings + naming
- Every new helper declaration must have its own docstring immediately above it: `/-- ... -/`
- Name every new declaration by its mathematical meaning; avoid placeholder names like `helper1`, `tmp`, `h1`, etc.

8) Imports and module paths
- Keep imports consistent.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

9) Infra plan dependency graph (JSON planning stage)
- The `dependencies` relation must form a DAG (no cycles).
- A plan item may only depend on earlier items (topological order by `index`).
- If two ideas seem mutually dependent, refactor into one-way helper lemmas/defs.
- In plan/check stage, do not use future items in proof sketches; only dependency-closure + mathlib is allowed.
- If a non-def item is too coarse for normal proof budget, split it into finer items instead of writing pseudo-proof text.

---

## B. Goal discipline (avoid overbuilding)

1) Minimality
- Add only what is required to solve `<id>.lean`.
- Prefer the smallest lemma that matches the needed goal shapes.

2) Reusability (within the problem)
- Internal helpers are allowed, but keep them in infra only if they genuinely simplify reuse and are needed.
- Prefer general statements when they are not harder to prove than specialized ones.

3) Multiple declarations per item (allowed)
- In infra **statement** stage, you may split one item into multiple declarations (defs/lemmas) when it clarifies structure.
- Keep **one** main declaration labeled for semantic check; helper declarations should have their own docstrings.

4) Do not change the target theorem statement
- Do not strengthen the target theorem(s) in `<id>.lean` or add new hypotheses.
- Helper lemma statements may be adjusted as needed to be mathematically correct.

---

## C. Compilation discipline

- Do **not** run `lake build`.
- Mandatory before finishing: `lake env lean <target_file>` must succeed with no errors.
- Infra files must remain `sorry`-free at all times.
