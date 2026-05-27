# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a **Lean 4** project for **CS 294-268: Proving TCS and Math Theorems in Lean** (UC Berkeley, Spring 2026). It contains problem set exercises and a final project.

- **Toolchain**: `leanprover/lean4:v4.27.0` (managed via `elan`)
- **Dependency**: Mathlib v4.27.0 (from `leanprover-community/mathlib4`)
- **Build system**: Lake

## Build Commands

```bash
# Build the root project (pset1 exercises)
lake build

# Build the nested NPReductions project
cd YangshuoZou_NPReductions && lake build
```

The first `lake build` will download Mathlib — expect it to take several minutes.

## Project Structure

### Root project: `pset1`

- **`exercises/Pset1.lean`** — Library entry point; imports `Pset1.Basic`
- **`exercises/Basic.lean`** — Problem Set 1: logic, tactics, induction on Nat and List, calc proofs, case splits
- **`exercises/pset2.lean`** — Problem Set 2: structured proofs, DFA definitions and correctness
- **`exercises/pset3.lean`** — Problem Set 3: graph theory (proper colorings, pigeonhole principle, walks, reachability)

Students fill in `sorry`s with proofs. Each task specifies which tactics to use (e.g., `intro`, `apply`, `cases`, `induction`, `simp`, `rw`, `calc`).

### Nested project: `YangshuoZou_NPReductions/`

A separate Lake project formalizing NP-completeness reductions:

| File | Content |
|------|---------|
| `NPReductions/SATTo3SAT.lean` | SAT → 3-SAT Tseitin encoding, completeness + soundness |
| `NPReductions/ThreeSATToClique.lean` | 3-SAT → Clique conflict graph reduction |
| `NPReductions/ThreeNAESATTo3Coloring.lean` | 3-NAE-SAT → 3-Coloring (authored by course staff) |

This project has its own `lakefile.toml` and `lake-manifest.json`. It uses the same toolchain and Mathlib version as the root project.

## Editing Workflow

The expected workflow is to open the project root in VS Code with the **Lean 4 extension** installed. Lean provides inline goal display, error diagnostics, and tactic state in the infoview. Edit the `.lean` files and rebuild with `lake build` to verify correctness.

## Lean Configuration

From `lakefile.toml`:
- `relaxedAutoImplicit = false` — explicit binder annotations required
- `maxSynthPendingDepth = 3` — conservative typeclass search depth
- `weak.linter.mathlibStandardSet = true` — linter for set-like notation
