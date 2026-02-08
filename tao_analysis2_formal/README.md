# tao_analysis2_formal（项目工作区）

这是一个“形式化项目”工作区目录。

当你使用：
- `./scripts/run_statement_pipeline.sh --project tao_analysis2_formal ...`
- `./scripts/run_proof_pipeline.sh --project tao_analysis2_formal ...`
- `./scripts/run_final_pipeline.sh --project tao_analysis2_formal ...`

系统会把本项目相关的 Lean 文件写入到本目录下，典型位置：
- `M2F/tao_analysis2_formal/Chapters/ChapXX/sectionYY.lean`

题库目录是全局共享的（不随项目改变）：
- `M2F/Question_bench/...`（你可以在其下放多个题库子目录）

数据建议放到：
- `data/tao_analysis2_formal/`

日志会写到：
- `log/tao_analysis2_formal/`
