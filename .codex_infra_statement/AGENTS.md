# AGENTS.md — INFRA STATEMENT stage (Lean 4 + mathlib)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **INFRA STATEMENT** stage:
- Generate declaration **skeletons** for infra items (definitions/lemmas/theorems).
- Inputs come from `infra_plan.json` (JSON, not LaTeX).
- **Primary goal:** translate the mathematical statement in `content` accurately into Lean.  
- Proofs are placeholders (`:= sorry`); statements must match intended math meaning.

This file is the INFRA‑STATEMENT‑stage rules source; the orchestrator swaps `M2F/AGENTS.md` to this before Codex calls during infra statement.

---

## A. Hard constraints (do not violate)

1) Edit scope (bench + its infra only)
- You may edit:
  - the target bench file `Question_bench/.../<id>.lean` (or its `_partXX.lean`), and
  - any files under the sibling directory `Question_bench/.../infra_<id>/`.
- Do not touch any other file. Do not rename/move files.
- `infra_<id>/Main.lean` is reserved as the entry/aggregator file (imports other infra files).
- Even within allowed files, avoid modifying any content unrelated to the current item.

2) Docstrings + label discipline
- Every new declaration must have its own docstring `/-- ... -/`.
- Each **item label** must correspond to **exactly one** *main* declaration whose docstring **starts with** the label.
- Helper declarations are allowed; their docstrings must **not** start with the label.

3) Multiple declarations per item (allowed)
- You may split one item into multiple declarations (defs/lemmas) when that clarifies structure.
- Keep **one** labeled main declaration per item; helpers should be separate and well‑named.

4) No embedded proof fragments inside terms
- Do not embed proofs inside a larger term (e.g. `⟨..., by ...⟩`, `(by ...)` as a subterm).
- Do not use tactic proofs inside terms.

5) Definitions must be proof‑free
- Inside a `def` / `abbrev` body, do not use `by ...`.
- If a definition body must be a placeholder, use `:= sorry` (not `by sorry`).
- For `lemma` / `theorem`, the proof must be exactly `:= sorry` at this stage.
- **Binder hygiene:** remove unused hypotheses/parameters/typeclass args if they are not required by types.

6) No axiom
- Never introduce `axiom`.

7) Semantic fidelity (mandatory self‑check)
- Do not weaken/strengthen assumptions or conclusions just to compile.
- Do not add spurious hypotheses; keep binders minimal and canonical.
- Preserve hidden dependencies: if the item relies on earlier setup, include those hypotheses explicitly.
- Maintain quantifier structure and dependence on chosen data.

8) Naming and layout
- Name every declaration by its mathematical meaning (no `tmp`, `h1`, `helper1`).
- Do not create chapter/section wrappers; infra items are **item‑per‑file**.
- Update existing labeled declarations if present; do not create duplicates.

9) Imports and module paths
- Keep imports consistent.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

---

## B. Statement‑stage success criteria

- The file compiles with `lake env lean <target_file>` (sorries allowed).
- The main declaration matches the item’s math meaning (semantic drift is not allowed).
