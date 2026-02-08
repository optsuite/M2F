# AGENTS.md — PROOF stage (strict rules, Lean 4 + mathlib)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **PROOF** stage:
- Given existing declaration skeletons, **replace the relevant `sorry` with proofs**.
- The target file must **compile** with `lake env lean`.

This file is the PROOF-stage rules source; the orchestrator copies it to `M2F/AGENTS.md` before each Codex call.

---

## A. Hard constraints (do not violate)

1) Edit scope
- Edit **only** the file explicitly provided by the orchestrator (`target_file` / `lean_file` in meta).
- Do not touch any other file. Do not rename/move files.

2) No embedded proof fragments inside terms
- Do not embed proofs inside a larger term (e.g. `⟨..., by ...⟩`, `(by ...)` used as a subterm, etc.).
- It is OK to use `by ...` as the *top-level proof* of a `lemma` / `theorem`.
- If a term construction requires a proof obligation, introduce a **separate named lemma** and reference it.

3) Definitions must be proof-free
- Inside a `def` / `abbrev` body, do not use `by ...`.
- If a definition body must be a placeholder, use `:= sorry` (never `by sorry`).

4) No axiom
- Never introduce `axiom`.

5) Docstrings are required
- Every new helper declaration must have its own docstring immediately above it: `/-- ... -/`

5.1) Label must be preserved in docstrings
- The orchestrator provides a `label` for the current textbook entry.
- Do not remove it from existing docstrings.
- If you introduce any helper declarations dedicated to proving this entry:
  - Include the `label` in their docstrings as well, but **do not** make the helper docstring start with the raw `label`.
  - Recommended helper-docstring template: `/-- Helper for <label>: ... -/`
  - Only the **main** theorem/lemma for this entry should have a docstring that starts with the `label` (to avoid accidental “multiple decls per label” conventions).

6) Mathlib first
- Prefer existing mathlib lemmas/definitions.
- Avoid re‑defining standard structures; prove equivalences or provide instances/lemmas instead.

7) Imports and module paths
- Do not introduce inconsistent imports.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

8) Dependency-order policy (strong default in prompts)
- Build the proof only from `dependencies` (from item metadata), their transitive prerequisites, and mathlib.
- Default rule: do **not** import or rely on declarations that are later than the current target (later JSON items / later textual order in file).
- In particular, for per-item infra files, do not solve an earlier item by importing a later-item module (e.g. proving `Infra:25:4` by importing `InvariantU`).
- If a later declaration is genuinely unavoidable, state the exact declaration and concrete reason explicitly in feedback/notes so orchestrator logs can track the exception.
- Do not “skip missing prerequisites” by jumping to later theorems; request re-plan and ask for the prerequisite to be proved in the correct dependency order.

---

## B. Proof workflow and stability (codex-friendly)

1) Prove, do not refactor
- Keep statements intact unless a minimal change is required for correctness/type‑checking.
- Keep edits local to the targeted label/declaration.

1.1) Preserve mathematical meaning
- If the statement is mathematically sound (i.e. “the problem is not wrong”), do not change its meaning:
  - Do not weaken/strengthen assumptions or conclusions.
  - Do not change quantifiers/binders or switch to a different (non-equivalent) formulation just to make the proof easier.
- Only adjust a statement when it is genuinely inconsistent/ill-typed relative to the intended meaning; in that case keep the change minimal and explain the reason in your feedback/notes.

1.1.1) Target vs helper statements
- The restrictions in 1.1 apply to the **target textbook declaration** you are proving (the theorem/lemma/def corresponding to the current label/content).
- For **helper** declarations that you introduce (or previously introduced) to support the proof:
  - You may revise their statements as needed to make the proof go through (including adding/removing hypotheses), as long as the helper statements remain **mathematically correct** and preferably **general/reusable**.
  - Do not use helper-statement edits to “smuggle in” extra assumptions that effectively strengthen the target theorem; the target theorem’s statement must stay faithful to the intended book meaning.
  - If you discover a helper statement is **mathematically false / missing assumptions**, do not try to force a proof. Instead, **restate the helper to a correct version** (typically by adding the missing hypotheses or weakening the conclusion) and update all downstream call sites accordingly.
    - Do **not** treat this as a “bad statement” unless the **target textbook declaration itself** is false/unprovable as written.
    - If you cannot complete the repair in this attempt, keep the file compiling and request re-plan with: (i) the corrected helper statement, (ii) the list of call-site changes, and (iii) a brief reason why the old helper was false.

1.2) Universe mismatch exception (Lean-technical, meaning-preserving)
- If a proof is blocked because the *statement itself* does not type-check due to a **universe/implicit-binder mismatch**, you may adjust the **declaration header/signature** in a way that preserves the intended mathematical meaning.
- Allowed header adjustments include (non-exhaustive):
  - Change `Type*` / `Sort*` binders to `Type u` / `Sort u` to align universes with other parameters.
  - Add `universe u v ...` declarations and use them in binder types.
  - Align index types in covers/families: `{ι : Type u}` vs `{ι : Type*}` when `Y : Type u`.
  - Make implicit universe arguments explicit when needed (e.g. `.{u}`) without changing the proposition.
- Not allowed:
  - Any change that weakens/strengthens assumptions or conclusions, changes the quantified mathematical content, or “patches” by adding extra assumptions.
  - Switching to a different (non-equivalent) formulation just to make the proof easier.

2) Use helper lemmas
- If the proof is long or brittle, introduce a small set of reusable helper lemmas with good names and docstrings.
- Avoid deeply nested `have` chains; keep the main proof flat and readable.
  - **Naming (required):** any helper `lemma`/`def`/`abbrev` you introduce must be named according to its mathematical meaning (not `helper1`, `tmp`, `h1`, `lemma_1_2`, etc.).
  - **Reusability (required):** prefer helper lemmas that are as general as reasonable (so later proofs can reuse them), not overly specialized to a single line of the current proof.
  - **Long‑range progress (required):** unless you hit a concrete Lean blocker, each attempt should implement the proof skeleton and prove multiple key helper lemmas in the same pass (avoid tiny 1–2 line edits that don’t materially advance the proof).
  - **Agent A substantial progress rule (required):** every Agent A attempt must produce material proof progress (e.g., fewer `sorry`, solved key subgoals, or proved helper lemmas), not cosmetic/no-op edits.
  - **Only exception:** if the target statement is mathematically wrong/unprovable as written, stop forcing local edits and report it as `failed_bad_statement` with a concrete reason.
  - If you must leave a helper lemma as `:= sorry` during a re-plan request, ensure the *statement* is mathematically correct and still reasonably general; do not invent false lemmas to unblock.

3) Prefer stable tactics
- Prefer deterministic tactics/steps (`simp`, `rw`, `constructor`, `refine`, `calc`, `linarith`/`nlinarith` when appropriate).
- Avoid relying on “suggestion” tactics/macros (e.g. `simp?`, `exact?`) in final code.

4) Compilation discipline
- The orchestrator checks with `lake env lean <file>`.
- Do **not** run `lake build`.
- Warnings discipline:
  - Do not silence lints/warnings via `set_option` or disabling linters.
  - If asked to clean non-`sorry` warnings, fix them by adjusting code (unused args/vars, simplifying `simp`, etc.).

---

## C. Multi‑agent protocol (C plans → A proves → B fixes)

When a planning/fallback protocol is in use, follow these contracts:

1) **Agent C plan block**
- Agent C outputs exactly one JSON plan wrapped by:
  - `<<<AGENT_C_PLAN>>>`
  - `<<<END_AGENT_C_PLAN>>>`

2) **Agent A feedback block**
- Agent A must end with exactly one JSON feedback block wrapped by:
  - `<<<AGENT_A_FEEDBACK>>>`
  - `<<<END_AGENT_A_FEEDBACK>>>`
- `status="needs_replan"`:
  - You are blocked structurally; leave only small, well‑scoped `sorry`.
  - The file must still compile (no Lean errors besides explicit `sorry`).
  - Be specific about blockers and what lemmas are needed.
- `status="failed_bad_statement"`:
  - Use this only when the target statement itself is mathematically false/inconsistent as written.
  - Provide a concrete mathematical reason (do not use this for ordinary proof difficulty).
- `status="ok"`:
  - Structure is stable; **no `sorry` remain** in the targeted work.
  - Any remaining issues should be low‑level fixups (imports/typos/tactics) for Agent B.

3) **Agent B**
- Agent B only does low‑level fixes (imports/typos/local tactic tweaks), not re‑planning.

---

## D. Tooling expectations

- Prefer using Lean LSP tooling (if available) for diagnostics/goals/completions.
- Do not run `lake build`.
- **Mandatory before finishing (Agent A and Agent B):** after you edit the target file, you must run:
  - `lake env lean <target_file>`
  and only finish when there are **no Lean errors** (warnings are OK unless explicitly asked to clean them).
  If errors remain, you must attempt to fix them yourself before handing off.
- The orchestrator validates with `lake env lean <file>`, but do not rely on the orchestrator to discover basic errors for you.
