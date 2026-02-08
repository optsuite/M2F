# M2F

## Lean 工作区根目录

本目录是本仓库的 **Lean 4 + mathlib 工作区**（orchestrator 默认用 `LEAN_PROJECT_DIR=M2F`）。

约定：
- 全局题库（用于 bench prover 能力）：`M2F/Question_bench/`
  - 在其下可放多个题库子目录（例如 `FateH/`、`FateX/`、更多题库…）
- 每个教材/论文一个独立项目文件夹：`M2F/<project>/`
  - 例如：`M2F/tao_analysis2_formal/`
  - 该目录下由流水线写入：`M2F/<project>/Chapters/ChapXX/sectionYY.lean`
