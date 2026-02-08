# AGENTS.md — INFRA FINAL stage (Lean 4 + mathlib)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **INFRA FINAL** stage:
- Eliminate remaining `sorry` in infra files and leave them compiling.
- Keep edits minimal and correct.

This file is the INFRA‑FINAL‑stage rules source; the orchestrator swaps `M2F/AGENTS.md` to this before Codex calls during infra final.

---

## A. Hard constraints (do not violate)

1) Edit scope
- Edit **only** the file explicitly provided by the orchestrator (`target_file` / `lean_file` in meta).
- Do not touch any other file. Do not rename/move files.
- Avoid modifying any content unrelated to the current item within that file.

2) No embedded proof fragments inside terms
- Do not embed proofs inside a larger term (e.g. `⟨..., by ...⟩`, `(by ...)` used as a subterm).
- It is OK to use `by ...` as the *top-level proof* of a `lemma` / `theorem`.

3) Definitions must be proof‑free
- Inside a `def` / `abbrev` body, do not use `by ...`.
- If a definition body must be a placeholder, use `:= sorry` (never `by sorry`).

4) No axiom
- Never introduce `axiom`.

5) Docstrings + label discipline
- Every new helper declaration must have its own docstring `/-- ... -/`.
- If you introduce helpers specific to this item, include the item label in their docstrings, but **do not** start the helper docstring with the raw label.

6) Preserve mathematical meaning
- Do not change the target statement’s meaning (no extra hypotheses, no weakening).
- Helper statements may be adjusted as needed, but must remain mathematically correct and preferably reusable.
- If a helper statement is false/missing assumptions, restate it correctly and update call sites.

7) Imports and module paths
- Do not introduce inconsistent imports.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

8) Long‑range progress (required)
- Each attempt should make **substantial** mathematical progress (main proof skeleton + multiple key helper lemmas), not just tiny local edits.
- **Agent A substantial progress rule (required):** every Agent A attempt must materially advance the proof (fewer `sorry`, solved key goals, or proved helper lemmas), not cosmetic/no-op edits.
- **Only exception:** if the target statement is mathematically wrong/unprovable as written, report `failed_bad_statement` with a concrete reason instead of forcing small edits.

---

## B. Final‑stage success criteria

- If you claim **done**, the target `sorry` must be eliminated and the file must compile.
- If blocked, request re‑plan and keep the file compiling with only small, well‑scoped `sorry`.
