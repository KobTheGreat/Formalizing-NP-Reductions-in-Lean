# Formalising NP-Completeness Reductions in Lean 4

**CS 294 · UC Berkeley · Spring 2026 · Final Project**

**Author:** Yangshuo Zou

## Overview

This project formalises the classical chain of NP-completeness reductions in Lean 4
with Mathlib:

1. **SAT → 3-SAT** — via the Tseitin-style chain encoding with auxiliary variables.
2. **3-SAT → Clique** — via the conflict graph construction.

Both reductions are proved in both directions (completeness and soundness),
yielding full equivalence theorems with no `sorry`.

## File Structure

| File | Description | Author |
|------|-------------|--------|
| `NPReductions/SATTo3SAT.lean` | SAT → 3-SAT encoding and equivalence proof | Yangshuo Zou |
| `NPReductions/ThreeSATToClique.lean` | 3-SAT → Clique reduction and equivalence proof | Yangshuo Zou |
| `NPReductions/ThreeNAESATTo3Coloring.lean` | 3-NAE-SAT → 3-Coloring and 3-SAT → 3-Coloring | Course staff (see below) |

## Main Results

### SAT → 3-SAT (`SATTo3SAT.lean`)

- `SAT_to_3SAT_completeness`: if a CNF formula is satisfiable, its 3-CNF encoding is satisfiable.
- `SAT_to_3SAT_soundness`: if the 3-CNF encoding is satisfiable, the original formula is satisfiable.
- `SAT_to_3SAT_equivalence`: the conjunction of the two above.

### 3-SAT → Clique (`ThreeSATToClique.lean`)

- `ThreeSAT_to_Clique_completeness`: a satisfiable 3-CNF formula yields an m-clique in its conflict graph.
- `ThreeSAT_to_Clique_soundness`: an m-clique in the conflict graph yields a satisfying assignment.
- `ThreeSAT_to_Clique_equivalence`: the conjunction of the two above.

## Attribution

The file `NPReductions/ThreeNAESATTo3Coloring.lean` was authored by the course
staff of CS 294-268 "Proving TCS and Math Theorems in Lean" (UC Berkeley,
Spring 2026, lecturer: Venkatesan Guruswami). It is included here as required
supplementary material and was not written by the project author. The Subset
Sum → Partition section from the original lecture file has been omitted as it
is outside this project's scope. This file was developed against Mathlib v4.28.0; 
the rest of the project uses the toolchain specified in `lean-toolchain` (Lean 4.27).

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib. See `lean-toolchain` and `lake-manifest.json` for
exact versions.
