# M2F: Automated Formalization of Mathematical Literature at Scale

M2F (Math-to-Formal) is a Lean-oriented framework for translating textbook- and paper-level mathematics into verifier-accepted formal projects at scale.

![M2F Overview](figs/M2F_overview.png)

## Abstract

M2F targets a core bottleneck in machine-assisted mathematics: scaling from isolated theorem proving to document-level formalization.  
The framework decouples formalization into two stages. Stage 1 compiles informal statements into declaration skeletons and repairs structural issues. Stage 2 keeps statement signatures fixed and focuses on closing proof gaps. This separation improves stability, debuggability, and end-to-end verifier pass rates.

## At a Glance

| Item | Value |
|---|---|
| Long-document corpus scale | **479 pages** |
| Generated Lean project size | **153,853 LoC** |
| Benchmark | **FATE-H (100 problems)** |
| Fully automatic performance | **96% PSR** |
| With light supervision (+31 declaration lemma map) | **97% PSR** |
| Stage 2 on matched statements (long-document setting) | **100% PSR** |

## Method

### Stage 1: Statement Compilation

- Generates Lean declaration skeletons from informal mathematical text.
- Repairs namespace/type/signature consistency issues for project-level validity.
- Allows temporary proof holes to maximize structural coverage before proof repair.

### Stage 2: Proof Repair

- Freezes statement signatures to avoid target drift.
- Iteratively closes proof holes using verifier feedback.
- Optimizes pass rates under fixed declarations for reliable end-to-end checking.

## Experimental Scope

- **Cross-prover benchmark:** FATE-H for direct comparability of pass rates.
- **Long-document setting:** large mathematical sources translated into executable Lean projects.
- **Metrics:** Pass Success Rate (PSR), verifier-call efficiency, and cost-normalized verification behavior.

## Result Highlights

### System Pipeline

![M2F Pipeline](figs/M2F_pipeline.png)

### Main Performance Charts

| FATE-H across provers (PSR) | FATE-H per-problem length and outcome |
|---|---|
| ![FATE-H PSR](figs/fateh_psr_bar_v4.png) | ![FATE-H Length](figs/fateh_loc_bar_log_2col_en.png) |

### Additional Analyses

| Alignment analysis | Proof-flow example |
|---|---|
| ![Convex Alignment](figs/convex_alignment_updated.png) | ![Proof Flowchart](figs/flowchart_theorem1_1.png) |

## Key Takeaways

- A staged compilation-repair design is effective for scaling formalization beyond isolated theorem tasks.
- M2F reaches strong fully automatic performance while maintaining compatibility with light supervision.
- Document-level formalization can achieve high verifier pass rates with controlled, reproducible workflows.
