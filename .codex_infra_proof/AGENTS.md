# AGENTS.md — INFRA PROOF stage (Lean 4 + mathlib)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **INFRA PROOF** stage:
- Replace the relevant `sorry` with proofs for infra items.
- Keep the target file compiling with `lake env lean`.

This file is the INFRA‑PROOF‑stage rules source; the orchestrator swaps `M2F/AGENTS.md` to this before Codex calls during infra proof.

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

7) Helper‑lemma discipline
- Prefer small, general helper lemmas with good names and docstrings.
- Avoid deeply nested `have` chains; keep the main proof flat and readable.
- Avoid “suggestion” tactics (`simp?`, `exact?`) in final code.
- **Long‑range progress (required):** each attempt should make **substantial** mathematical progress (build the main proof skeleton and prove multiple key helper lemmas), not just tiny local edits.
- **Agent A substantial progress rule (required):** every Agent A attempt must materially advance the proof (fewer `sorry`, solved key goals, or proved helper lemmas), not cosmetic/no-op edits.
- **Only exception:** if the target statement is mathematically wrong/unprovable as written, report `failed_bad_statement` with a concrete reason instead of forcing small edits.

8) Imports and module paths
- Do not introduce inconsistent imports.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

9) Dependency-order policy (strong default in prompts)
- Build the proof only from item `dependencies`, their transitive prerequisites, and mathlib.
- Default rule: do **not** import or rely on declarations that are later than the current target (later JSON items / later textual order in file).
- In particular, do not solve early infra items by importing later infra modules (e.g. proving `Infra:25:4` by importing `InvariantU`).
- If a later declaration is genuinely unavoidable, call out the exact declaration and concrete reason explicitly in feedback/notes.
- Do not bypass missing prerequisites by referencing later theorems; request re-plan and ask for prerequisite construction in dependency order.

---

## B. Proof‑stage success criteria

- The target `sorry` is eliminated (or a clear re‑plan is requested with compiling code).
- The file compiles with `lake env lean <target_file>`.
