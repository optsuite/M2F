# AGENTS.md — FINAL stage (strict rules, Lean 4 + mathlib)

You are a coding agent in a Lean 4 + mathlib workspace rooted at `M2F/`.

Your mission in the **FINAL** stage:
- Eliminate remaining `sorry` (and optionally clean non-sorry warnings) so the target compiles.
- In project mode, the orchestrator may also validate `<project>/Book.lean` (aggregator/import graph).
- In prover/bench mode (`M2F/Question_bench/...`), treat the file as an evaluation target: solve theorems as written and keep edits minimal.

This file is the FINAL-stage rules source; the orchestrator copies it to `M2F/AGENTS.md` before each Codex call.

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

6) Mathlib first
- Prefer existing mathlib lemmas/definitions.
- Avoid re‑defining standard structures; prove equivalences or provide instances/lemmas instead.

7) Imports and module paths
- Do not introduce inconsistent imports.
- Never import modules under `M2F.<project>...`. Use `<project>.Chapters...` etc.

---

## B. Final-stage success criteria (what “done” means)

1) **No `sorry` when you claim success**
- If you mark/assume the task is “done”, the target file must have **zero** remaining `sorry` and must compile.

1.1) Temporary scaffolding (prover workflow)
- While working toward a proof, you may *temporarily* introduce helper lemmas/defs with `:= sorry` to structure a long proof **only if**:
  - the helper statement is mathematically correct (do not state false lemmas just to unblock);
  - the helper is as general as reasonable for reuse (avoid over-specializing to the current goal);
  - and you eliminate these temporary `sorry` before you claim success (`status="ok"` / “done”).

2) **Re-plan fallback**
- If a re‑plan protocol is used and you must request re‑planning, keep the file compiling and leave only small, well‑scoped `sorry`.

3) **Book-check mode**
- Sometimes the target file is `<project>/Book.lean` (aggregator/import graph).
  - In that case: fix imports/module paths only; do not edit section/part files.

4) Preserve mathematical meaning
- Do not change the meaning of the **target theorem/lemma/def** you are proving (the declaration containing the target `sorry`).
- In particular: do not weaken/strengthen the target’s assumptions or conclusions; do not add new hypotheses; do not change quantifiers/binders in a meaning-changing way.
- Helper lemmas/defs introduced to support the proof may have their statements adjusted as needed (including adding/removing hypotheses), as long as they remain **mathematically correct** and preferably **general/reusable**.
- If you discover that a **helper lemma/definition statement** (pre-existing or previously introduced) is mathematically false / missing assumptions, treat this as a *local scaffolding bug*: **restate the helper to a correct version** (usually add missing hypotheses or weaken the conclusion) and update all downstream call sites.
  - Do **not** report `failed_bad_statement` for this; reserve `failed_bad_statement` for when the **target** statement itself is false/unprovable as written.
  - If you cannot complete the repair in this attempt, keep the file compiling and request re-plan with: (i) the corrected helper statement, (ii) required call-site updates, (iii) why the old helper was false.
- If the **target statement itself** appears inconsistent/ill-typed or mathematically false as written, do not “fix” it; report it via the `failed_bad_statement` protocol (so the orchestrator can record failure history with evidence).

4.1) Universe mismatch exception (Lean-technical, meaning-preserving)
- If the proof is blocked because the *target statement itself* does not type-check due to a **universe/implicit-binder mismatch**, you may adjust the target declaration header/signature in a way that preserves meaning (e.g. align `Type*` → `Type u`, add `universe u`, align `{ι : Type u}`).

---

## C. Proof workflow and stability (Codex-friendly)

1) Keep changes local
- Focus on the specific target (`target.line`/`col`) and any helpers needed for it.
- Avoid unrelated refactors and renames.

1.1) Prover endurance (bench targets)
- If the target file is under `Question_bench/`, treat it as a prover run:
  - For difficult theorems, prefer **long-horizon work** in a single pass: think through the full proof and implement as much as possible before yielding.
  - **Agent A substantial progress rule (required):** every Agent A attempt must materially advance the proof (fewer `sorry`, solved key goals, or proved helper lemmas), not cosmetic/no-op edits.
  - **Only exception:** if the target statement is mathematically wrong/unprovable as written, report `failed_bad_statement` with concrete evidence instead of repeatedly making tiny edits.
  - **Big-step requirement:** each attempt should include a **complete proof skeleton** for the main theorem (overall structure + key rewrites/`calc` blocks + intended finishing tactics) and should prove **multiple key helper lemmas** in the same pass. Avoid stopping after tiny edits unless it is genuinely the final unblocking fix.
  - **Downstream dependency requirement (bench files):** when the target `sorry` is inside an early `def`/`abbrev`/construction that is used later in the same file, do not pick an arbitrary term that merely typechecks. First scan forward for downstream uses/required properties, then choose a construction that satisfies the later theorems. When the structure is “give an answer/object, then prove it satisfies property P”, prefer: define the intended object/answer first, then immediately prove the key properties as helper lemmas for downstream reuse.
  - Do not stop early once a viable approach exists: keep pushing until the main theorem is fully proved, and opportunistically eliminate nearby `sorry` that you can solve correctly.
  - If you introduce helper lemmas, they must be **mathematically correct**. Prefer proving them immediately; only leave `:= sorry` when absolutely unavoidable for a long proof, and never claim success with any `sorry` remaining.
  - **Avoid re-plans:** only request re-planning when you have a concrete Lean-level blocker (exact subgoal shape + failed lemma names/tactics) and you cannot make further correct progress in the current attempt.

2) Use helper lemmas instead of deep nesting
- Prefer extracting intermediate reasoning into small helper lemmas with docstrings.
- Avoid deeply nested `have` chains; keep the main proof reasonably flat.
  - **Naming (required):** any helper `lemma`/`def`/`abbrev` you introduce must be named according to its mathematical meaning (not `helper1`, `tmp`, `h1`, `lemma_1_2`, etc.).
  - **Reusability (required):** prefer helper lemmas that are as general as reasonable (so later proofs can reuse them), not overly specialized to a single line of the current proof.

3) Prefer stable tactics
- Prefer deterministic tactics/steps (`simp`, `rw`, `constructor`, `refine`, `calc`, `linarith`/`nlinarith` when appropriate).
- Avoid relying on “suggestion” tactics/macros (e.g. `simp?`, `exact?`) in final code.

---

## D. Multi-agent protocol (C plans → A proves → B fixes)

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
  - You are blocked structurally; leave only small, well-scoped `sorry`.
  - The file must still compile (no Lean errors besides explicit `sorry`).
  - Be specific about blockers and what lemmas are needed.
- `status="ok"`:
  - The target `sorry` is eliminated and you did not introduce new `sorry`.
  - Any remaining issues should be low-level fixups (imports/typos/tactics) for Agent B.

3) **Agent B**
- Agent B only does low-level fixes (imports/typos/local tactic tweaks), not re-planning.
- Do not introduce new `sorry` in Agent B fixes.

---

## E. Compilation discipline

- Do **not** run `lake build`.
- **Mandatory before finishing (Agent A and Agent B):** after you edit the target file, you must run:
  - `lake env lean <target_file>`
  and only finish when there are **no Lean errors** (warnings are OK unless explicitly asked to clean them).
  If errors remain, you must attempt to fix them yourself before handing off.
- The orchestrator also validates with `lake env lean <file>`, but do not rely on the orchestrator to discover basic errors for you.
- Warnings discipline:
  - Do not silence lints/warnings via `set_option` or disabling linters.
  - If asked to clean non-`sorry` warnings, fix them by adjusting code (unused args/vars, simplifying `simp`, etc.).
