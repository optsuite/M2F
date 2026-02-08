
-- BEGIN AUTO-IMPORTS (managed by orchestrator)
import tao_analysis2_formal.Chapters.Chap01
import tao_analysis2_formal.Chapters.Chap02
-- END AUTO-IMPORTS

/-
`tao_analysis2_formal/` is a per-project workspace under the `M2F/` Lean workspace.

When you run pipelines with `--project tao_analysis2_formal` (or `FORMAL_PROJECT=tao_analysis2_formal`),
the orchestrator writes chapter section files under:

- `tao_analysis2_formal/Chapters/ChapXX/sectionYY.lean`
- (bench is global) `Question_bench/...`

This file is an optional aggregation module for that workspace.

Tip: keep this file minimal; add imports only after the corresponding files exist.
-/

-- Example (uncomment when created):
-- import tao_analysis2_formal.Chapters.Chap01.section01
