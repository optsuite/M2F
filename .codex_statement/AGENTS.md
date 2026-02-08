# AGENTS.md — STATEMENT stage (strict rules, Lean 4 + mathlib)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **STATEMENT** stage:
- Convert one textbook entry into **Lean declarations (statements only)**.
- Proofs are placeholders (`:= sorry`) and the target must **compile** with `lake env lean`.

This file is the STATEMENT-stage rules source; the orchestrator copies it to `M2F/AGENTS.md` before each Codex call.

---

## A. Hard constraints (do not violate)

1) Edit scope
- Edit **only** the file explicitly provided by the orchestrator (`target_file` in meta).
- Do not touch any other file. Do not rename/move files.

1.1) Agent B edit scope (statement stage)
- When acting as Agent B (fixing errors after Agent A), prefer editing:
  - necessary `import ...` lines in the import preamble; and
  - the declarations that were introduced/modified for the **current** textbook entry.
- However, if compilation fails due to an earlier declaration in the same file, you may repair it as well (minimal edits; preserve mathematical meaning; avoid unrelated refactors).
- Do not “sorrify” unrelated declarations to make the file compile.

2) No embedded proof fragments inside terms
- Do not embed proofs inside a larger term (e.g. `⟨..., by ...⟩`, `(by ...)` used as a subterm, etc.).
- If a term construction requires a proof obligation (Subtype/structure fields, closure properties, etc.), introduce a **separate named lemma** and reference it.

3) Definitions must be proof-free
- Inside a `def` / `abbrev` body, do not use `by ...`.
- If a definition body must be a placeholder, use `:= sorry` (never `by sorry`).
3.1) `def` binder hygiene
- For `def`/`abbrev`, do not keep unused hypotheses/parameters/typeclass arguments.
  - If a binder is unused and can be removed without changing the intended meaning (or only changes it negligibly), **delete it**.

4) Placeholders style
- For `lemma` / `theorem`, use `:= sorry` (not `by sorry`).
- Never introduce `axiom`.

4.1) Statement-only means no proofs
- In the STATEMENT stage, do not write real proofs.
- For any `lemma` / `theorem` you introduce, the proof must be exactly `:= sorry`.
- Do not use `by ...` in this stage (except inside comments/docstrings).

5) Docstrings are required
- Every new declaration must have its own docstring immediately above it: `/-- ... -/`

5.1) Label must appear in the comment/docstring
- For every textbook entry, you will be given a `label` in the orchestrator meta.
- **Exactly one declaration per label:** each textbook `label` must correspond to **exactly one** Lean declaration in the file (the “main declaration” for that entry).
- The main declaration must have a docstring `/-- ... -/` immediately above it that includes the `label`, and the docstring should **start with** the label (e.g. `/-- Definition 1.5: ... -/`).
- If you introduce helper declarations (to satisfy typing/compilation), they must still have docstrings, but their docstrings must **not** start with the textbook `label` (and preferably should not include the label at all).
- Preserve any numbering from the source (e.g. (i), (ii), (A1), etc.) in the docstring when present.
- If the file already contains declarations for the same `label`, update them instead of adding duplicates.

5.2) Semantic fidelity (statement stage)
- The Lean declaration for the main labeled statement should match the natural-language math meaning as closely as possible.
- Do not weaken/strengthen assumptions or conclusions just to make Lean compilation easier.
- Prefer mathlib-aligned formulations only when they are genuinely equivalent to the text; otherwise define the book notion and optionally state an equivalence lemma.
- **No spurious conditions:** do not add extra hypotheses/assumptions/typeclass arguments that are not part of the intended mathematical meaning.
  - If you introduced a condition/parameter and it does not appear in the statement (or is not required for types), **delete it**.
  - Keep binders minimal and canonical; avoid “context variables” that are never used.
- **Semantic-drift guard (mandatory self-check):** after writing the skeleton, re-read the original textbook `content` and your Lean statement and actively check for semantic drift.
  - **Hidden dependencies:** if the text says “assume the setup of the previous subgoal/lemma/proposition” (or otherwise references earlier setup), do **not** drop it. Either:
    - add the missing hypotheses explicitly; or
    - parameterize the statement by a previously defined setup structure/lemma that encapsulates those assumptions.
  - **No accidental weakening / over-generalization:** do not turn a conditional statement into an unconditional one. Common pitfall: replacing “the specific map/object constructed from …” with “for any map/object satisfying …”, which can make the statement false.
  - **Quantifiers and dependence:** verify that binders match the text’s intended dependence on chosen data (e.g. a section `s : K → R`, a chosen maximal ideal, a fixed nilpotence index).

6) Mathlib first
- Prefer existing mathlib notions (types/structures/predicates) over re-defining.
- If the book’s definition matches mathlib, do not re-define it; define the book’s axiom/predicate layer if needed and state equivalence.

7) Imports and module paths
- Do not introduce inconsistent imports.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

---

## B. File layout and placement

The orchestrator writes to project files like:
- `<project>/Chapters/ChapXX/sectionYY.lean`

Keep (or create) the standard section layout:

```lean
import Mathlib

section ChapXX
section SectionYY

-- new declarations go here

end SectionYY
end ChapXX
```

- Append new declarations inside the correct `ChapXX` / `SectionYY` sections.
- Do not remove existing labels/comments.

---

## C. Choosing the right declaration form (philosophy)

Use the most canonical, mathlib-aligned form:
- `def`: define data/function/predicate (`Prop`-valued definitions are allowed).
- `abbrev`: like `def`, but prefer it when definitional unfolding should stay lightweight.
- `structure`: package data/fields (not typeclass inference by default).
- `class`: only if downstream should rely on typeclass inference.
- `lemma`/`theorem`: facts in `Prop` (use `theorem` for main book theorems, otherwise `lemma`).
- `instance`: only for canonical/natural instances (do not abuse instances for convenience).

Keep binders minimal and canonical; avoid unnecessary parameters or typeclass assumptions.
When introducing helper declarations, prefer statements that are as general as reasonable for reuse in later proof stages (without changing the intended meaning).

---

## D. Naming and stability

- Use mathematically meaningful names.
- **Names must reflect mathematical meaning (including helpers):**
  - For every `def`/`abbrev`/`lemma`/`theorem`/`instance` you introduce (including helper declarations), choose a name that reflects the mathematical content.
  - Avoid placeholder or bookkeeping names like `helper1`, `tmp`, `foo`, `bar`, `test`, `h1`, `lemma_1_1`, etc. (use the textbook `label` in the docstring instead).
- Avoid book-specific identifiers (do not include the textbook name, “Book”, “Chapter”, etc. in declaration names).
- Prefer simple, stable names that will remain usable in later proof stages.

---

## E. Compilation and tooling expectations

- You must keep the target file syntactically correct and type-correct (allowing `sorry`).
- Do **not** run `lake build`.
- **Mandatory before finishing (Agent A and Agent B):** after you edit the target file, you must run:
  - `lake env lean <target_file>`
  and only finish when there are **no Lean errors** (warnings are OK unless explicitly asked to clean them).
  If errors remain, you must attempt to fix them yourself before handing off.
- The orchestrator also validates with `lake env lean <file>`, but do not rely on the orchestrator to discover basic errors for you.
- Prefer using Lean LSP tooling (if available) for diagnostics/completions; rely on `lake env lean` only as the lightweight final check.
- Warnings discipline:
  - Do not silence lints/warnings via `set_option` or disabling linters.
  - If the orchestrator asks you to clean non-`sorry` warnings, fix them by adjusting code (unused args/vars, simplifying `simp`, etc.).

---

## F. Output discipline (what you should produce)

- Add a brief docstring and then the Lean declaration(s).
- Keep changes minimal, local, and stable.
- Prefer small helper lemmas over clever term tricks.
