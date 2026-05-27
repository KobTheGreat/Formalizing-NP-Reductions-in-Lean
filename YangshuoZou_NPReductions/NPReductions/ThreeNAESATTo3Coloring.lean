/-
Copyright (c) 2026 UC Berkeley CS 294. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CS 294-268 course staff (UC Berkeley, Spring 2026)
         Lecturer: Venkatesan Guruswami

This file was authored by the course instructors and TA as lecture material.
It is included here as supplementary context for the SAT → 3-SAT → Clique
reductions formalised in the companion files.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Formalisations of NAE-SAT → 3-Coloring and 3-SAT → 3-Coloring

This file contains two reductions formalised by the CS 294 course staff:
1. **NAE-SAT → 3-Coloring** (`NAEtoColorReduction`)
2. **3-SAT → 3-Coloring** (`SATtoColorReduction`)

These serve as reference examples for the student-authored reductions in
`SATTo3SAT.lean` and `ThreeSATToClique.lean`.
-/


/-!

# NAE-SAT and 3-COLORING

## NAE-SAT
The **Not-All-Equal Satisfiability** problem asks: Given a set Boolean variables
`x_1, ..., x_n`, and a set of "clauses" `C_1, ... , C_m`, where each clause
is a triple of variables, does there exist a Boolean assigment such that
the variables in each clause `C_i` do not all get the same value.

## 3-COLORING
The **3-COLORING** problem asks: Given a graph, does there exists a `3`-coloring
such that no two vertices that share an edge get the same color.

## Reduction from NAE-SAT to 3-COLORING

Given a NAE-SAT instance over variables `x_1, ... , x_n` and clauses
`C_1, ... , C_m`, we create an instance of 3-COLORING over a graph over the
following vertices:
* A "ground" node `⊥`
* A "variable" node `x_i`
* Three "clause" nodes `c_{j,1}`, `c_{j,2}`, `c_{j,3}`.

The edges over this graph are defined as follows:
* The ground vertex `⊥` is connected to each variable vertex `x_i`.
* For a clause `c_r` containing variables `x_i`, `x_j` and `x_k`, we connect
  * `x_i`, `x_j`, `x_k` to `c_{r, 1}`, `c_{r, 2}`, `c_{r, 3}` respectively.
  * `c_{r, 1}`, `c_{r, 2}` and `c_{r,3}` are all interconnected.

This is visualized below:
        ⊥
        |
  +-----+-----+
  |     |     |
 x_1   x_2   x_3
  |     |     |
 c_1---c_2---c_3
  |           |
  +-----------+

**Proof Sketch.**

_Completeness:_

Given an assignment for the NAE-SAT instance, we construct a 3-coloring of the
reduction graph as follows:
* The ground node is colored `0`.
* If a variable `x_i` is assigned `true`, then the corresponding variable node
  is colored `1`; otherwise, it is colored `2`.
* For each clause `C_r = (x_i, x_j, x_k)`, the clause nodes `c_{r,1}`,
  `c_{r,2}`, and `c_{r,3}` are colored based on the truth assignments of
  `x_i`, `x_j`, and `x_k` such that they are all colored differently. This is
  always possible since not all literals in the clause have the same value.

_Soundness:_

Given a 3-coloring of the reduction graph, we construct an assignment for the
NAE-SAT instance as follows:
* If a variable node `x_i` is colored `1`, then the corresponding variable
  `x_i` is assigned `true`; otherwise, it is assigned `false`.
Since the clause nodes are connected in a triangle, they must have different
colors. Also, each clause node is connected to the corresponding variable node,
so the variables in each clause cannot all have the same value.

-/

namespace NAEtoColor

/-- A Not-All-Equal Clause -/
structure NAEclause (V : Type) where
  v0 : V
  v1 : V
  v2 : V

/-- Evaluate a Not-All-Equal clause -/
def SatisfiesClause {V : Type} (assign : V → Bool) (c : NAEclause V) : Bool :=
  (
    assign c.v0 ≠ assign c.v1 ||
    assign c.v0 ≠ assign c.v2 ||
    assign c.v1 ≠ assign c.v2
  )

/-- A NAE-SAT instance is a list of NAE clauses. -/
abbrev NAESat3 (V : Type) := List (NAEclause V)

/-- Returns `true` if the assignment satisfies all clauses. -/
def SatisfiesNAE3 {V : Type} (assign : V → Bool) (f : NAESat3 V) : Bool :=
  f.all (SatisfiesClause assign)

/-- The satisfiability property for a NAE-SAT instance. -/
noncomputable def IsSatisfiable {V : Type} (f : NAESat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesNAE3 assign f = true

-- Some examples to test definitions:
namespace NAE_SAT_Example

def nae_sat_eg : NAESat3 (Fin 5) := [⟨0, 1, 2⟩, ⟨0, 1, 3⟩, ⟨0, 2, 4⟩]

def assign_eg := ![true, true, false, false, false]

#eval SatisfiesClause assign_eg nae_sat_eg[2]
#eval SatisfiesNAE3 assign_eg nae_sat_eg

example : IsSatisfiable nae_sat_eg := ⟨assign_eg, rfl⟩
  -- Equivalent to `by use ex_assign_1; rfl`

end NAE_SAT_Example

/-- A simple graph is 3-colorable if there exists a valid 3-coloring.

Equivalently, a valid 3-coloring is equivalent to a graph homomorphism from
the given simple graph to the 3-Clique.
-/
def Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))

/-- Vertex set for reduction from NAE-SAT to 3-COLORING.
We map the input variables to output vertices using an inductive type.
This cleanly separates the three kinds of vertices without any integer indexing:
• groundNode  – 1 ground node, who color is 0 (assume True = 1, False = 2).
• varNode     – 1 node per variable.
• clauseNode  – 3 internal nodes per clause that encode the NAE constraint.
-/
inductive OutputVertex (V : Type)
| groundNode                                 -- ground vertex colored "neutral"
| varNode (v : V)                            -- one node per variable
| clauseNode (c : NAEclause V) (idx : Fin 3) -- 3 nodes per clause

/-- Edge relation for reduction from NAE-SAT to 3-COLORING.

The edges over this graph are defined as follows:
* The ground vertex `⊥` is connected to each variable vertex `x_i`.
* For a clause `c_r` containing variables `x_i`, `x_j` and `x_k`, we connect
  * `x_i`, `x_j`, `x_k` to `c_{r, 1}`, `c_{r, 2}`, `c_{r, 3}` respectively.
  * `c_{r, 1}`, `c_{r, 2}` and `c_{r,3}` are all interconnected.

This is visualized below:
        ⊥
        |
  +-----+-----+
  |     |     |
 x_1   x_2   x_3
  |     |     |
 c_1---c_2---c_3
  |           |
  +-----------+
-/
def EdgeRelation {V : Type} (clauses : NAESat3 V) (u v: OutputVertex V) : Prop :=
  match u, v with
  -- Connect ground vertex with every variable node.
  | .groundNode, .varNode _ => True
  | .varNode _, .groundNode => True

  -- Connect variable node to corresponding clause nodes.
  | .varNode v, .clauseNode c i =>
    (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)
  | .clauseNode c i, .varNode v =>
    (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)

  -- Connect clause gadgets to each other
  | .clauseNode c1 i, .clauseNode c2 j => c1 = c2 ∧ c1 ∈ clauses ∧ i ≠ j

  -- If a pair of vertices doesn't match any of the above patterns, there is no edge.
  | _, _ => False

/-- Simple graph for reduction from NAE-SAT to 3-Coloring.

We symmetrize EdgeRelation manually so proof of symmetry becomes trivial.
A SimpleGraph also requires irreflexivity (no self-loops), enforced by `u ≠ v`,
so we encode that in adjacency as well.
-/
def ReductionGraph {V : Type} (f : NAESat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Coloring of clause nodes obtained via reduction from NAE-SAT.

Given the boolean values of the three literals in a clause, assigns colors to
the three internal clause-gadget nodes.
We do not assume that the clause is in the NAE-SAT instance.
If the variables do not satisfy the Not-All-Equal clause, we color everything 0.
This is a valid coloring since there are no edges between clause nodes in that
case, and all variable nodes are colored either 1 or 2.
-/
private def clauseNodeColor (a b c : Bool) (k : Fin 3) : Fin 3 :=
  match a, b, c with
  | true,  true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | true,  false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | false, true,  true  => match k with | 0 => 1 | 1 => 0 | 2 => 2
  | true,  false, false => match k with | 0 => 2 | 1 => 0 | 2 => 1
  | false, true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | false, false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | _,     _,     _     => 0  -- (non-NAE cases have no clause-clause edges)

/-- Coloring of entire simple graph obtained via reduction from NAE-SAT.
Coloring constructed from NAE-SAT assignment.
  • groundNode      ↦  0
  • varNode v       ↦  1 if assign v = true, else 2
  • clauseNode c k  ↦  clauseNodeColor (assign values of the 3 variables)
-/
private def naeColoring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .groundNode => 0
  | .varNode v => if assign v then 1 else 2
  | .clauseNode c k => clauseNodeColor (assign c.v0) (assign c.v1) (assign c.v2) k

/-- Completeness of reduction from NAE-SAT to 3-Coloring. -/
lemma NAEtoColorCompleteness {V : Type} (f : NAESat3 V) :
  IsSatisfiable f → Is3Colorable (ReductionGraph f) := by
  intro ⟨assign, hsat⟩
  refine ⟨⟨naeColoring assign, ?_⟩⟩
  intro u v hadj
  simp only [SimpleGraph.top_adj]
  obtain ⟨hne, hedge⟩ := hadj
  -- Prove for any directed edge; then handle both directions
  suffices ∀ {a b : OutputVertex V}, EdgeRelation f a b →
              naeColoring assign a ≠ naeColoring assign b by
    rcases hedge with h | h'
    · exact this h
    · exact fun heq => this h' heq.symm
  intro a b h
  match a, b with
  -- There are 6 cases to match:
  -- 1. Ground node : Ground node (no edge)
  | .groundNode, .groundNode => exact False.elim h
  -- 2. Ground node : Var node
  | .groundNode, .varNode v | .varNode v, .groundNode =>
      simp only [naeColoring]
      cases assign v <;> simp
  -- 3. Ground node : Clause node (no edge)
  | .groundNode, .clauseNode _ _ | .clauseNode _ _, .groundNode =>
    exact False.elim h
  -- 4. Var node : Var node (no edge)
  | .varNode v, .varNode w => exact False.elim h
  -- 5. Var node : Clause node
  | .varNode v, .clauseNode c k | .clauseNode c k, .varNode v =>
    simp only [EdgeRelation] at h
    simp only [naeColoring]
    -- After rcases, k is substituted to 0, 1, or 2 by the rfl
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (cases assign c.v0 <;> cases assign c.v1 <;> cases assign c.v2 <;>
       simp [clauseNodeColor])
  -- 6. Clause node : Clause node
  | .clauseNode c1 i, .clauseNode c2 j =>
    obtain ⟨rfl, hcIn, hij⟩ := h
    simp only [naeColoring]
    have hNAE : SatisfiesClause assign c1 = true :=
      List.all_eq_true.mp hsat c1 hcIn
    -- Case-split on both indices and all boolean assignments.
    -- Diagonal (i=j): hij gives contradiction. Non-diagonal non-NAE: hNAE gives contradiction.
    fin_cases i <;> fin_cases j <;>
      cases h0 : assign c1.v0 <;> cases h1 : assign c1.v1 <;> cases h2 : assign c1.v2 <;>
      simp_all [clauseNodeColor, SatisfiesClause]

/-- Soundness of reduction from NAE-SAT to 3-Coloring. -/
lemma NAEtoColorSoundness {V : Type} (f : NAESat3 V) :
  Is3Colorable (ReductionGraph f) → IsSatisfiable f := by
  intro ⟨⟨col, hcol⟩⟩
  simp only [SimpleGraph.top_adj] at hcol
  have colNe : ∀ {u v : OutputVertex V},
      u ≠ v → (EdgeRelation f u v ∨ EdgeRelation f v u) → col u ≠ col v :=
    fun hne hedge => hcol ⟨hne, hedge⟩
  -- Variables differ from ground
  have hVG : ∀ v : V, col (.varNode v) ≠ col .groundNode := fun v =>
    colNe (by simp) (Or.inl trivial)
  -- Clause nodes in same clause are pairwise distinct (triangle)
  have hCC : ∀ (c : NAEclause V), c ∈ f → ∀ (i j : Fin 3), i ≠ j →
      col (.clauseNode c i) ≠ col (.clauseNode c j) := fun c hcIn i j hij =>
    colNe (by simp [hij]) (Or.inl ⟨rfl, hcIn, hij⟩)
  -- Each clause node differs from its variable (using tactic to unfold EdgeRelation)
  have hVC0 : ∀ c : NAEclause V, col (.clauseNode c 0) ≠ col (.varNode c.v0) := fun c =>
    Ne.symm (colNe (by simp) (by left; left; exact ⟨rfl, rfl⟩))
  have hVC1 : ∀ c : NAEclause V, col (.clauseNode c 1) ≠ col (.varNode c.v1) := fun c =>
    Ne.symm (colNe (by simp) (by left; right; left; exact ⟨rfl, rfl⟩))
  have hVC2 : ∀ c : NAEclause V, col (.clauseNode c 2) ≠ col (.varNode c.v2) := fun c =>
    Ne.symm (colNe (by simp) (by left; right; right; exact ⟨rfl, rfl⟩))
  -- Define: True color = groundColor + 1 (mod 3); assign v = True iff varNode has that color
  let cTrue : Fin 3 := col .groundNode + 1
  let assign v := decide (col (.varNode v) = cTrue)
  refine ⟨assign, ?_⟩
  simp only [SatisfiesNAE3, List.all_eq_true]
  intro c hcIn
  by_contra hFalse
  -- NAE violated → all three variables have the same boolean assignment value
  have hSatF : SatisfiesClause assign c = false := by
    rcases Bool.eq_false_or_eq_true (SatisfiesClause assign c) with h | h
    · exact absurd h hFalse  -- h : ... = true, hFalse : ¬... = true → absurd
    · exact h                -- h : ... = false
  simp only [SatisfiesClause] at hSatF
  -- Extract: all three assign values are equal
  have hall : assign c.v0 = assign c.v1 ∧ assign c.v0 = assign c.v2 := by
    constructor <;>
      (cases h0 : assign c.v0 <;> cases h1 : assign c.v1 <;> cases h2 : assign c.v2 <;>
       simp_all)
  obtain ⟨h01, h02⟩ := hall
  -- In both cases (all true / all false), all three varNodes have the same Fin 3 color
  have hSameColor : col (.varNode c.v0) = col (.varNode c.v1) ∧
                    col (.varNode c.v0) = col (.varNode c.v2) := by
    cases hb : assign c.v0 with
    | true =>
      -- All true: all varNodes have color cTrue → directly equal
      have ht0 : col (.varNode c.v0) = cTrue := of_decide_eq_true hb
      have ht1 : col (.varNode c.v1) = cTrue := of_decide_eq_true (h01.symm.trans hb)
      have ht2 : col (.varNode c.v2) = cTrue := of_decide_eq_true (h02.symm.trans hb)
      exact ⟨ht0.trans ht1.symm, ht0.trans ht2.symm⟩
    | false =>
      -- All false: varNodes ≠ cTrue and ≠ ground → unique remaining color in Fin 3
      have hf0 : col (.varNode c.v0) ≠ cTrue := of_decide_eq_false hb
      have hf1 : col (.varNode c.v1) ≠ cTrue := of_decide_eq_false (h01.symm.trans hb)
      have hf2 : col (.varNode c.v2) ≠ cTrue := of_decide_eq_false (h02.symm.trans hb)
      have hg0 := hVG c.v0; have hg1 := hVG c.v1; have hg2 := hVG c.v2
      -- cTrue ≠ groundNode color (adding 1 in Fin 3 is always a change)
      have hcTneG : cTrue.val ≠ (col .groundNode).val := by
        intro heq
        have hlt := (col .groundNode).isLt
        have := Fin.val_add (col .groundNode) (1 : Fin 3)
        simp only [Fin.val_one] at this
        omega
      -- omega: three constraints (< 3, ≠ g, ≠ ct, ct ≠ g) uniquely pin the value
      constructor
      · apply Fin.ext
        have := (col .groundNode).isLt
        have := (col (.varNode c.v0)).isLt
        have := (col (.varNode c.v1)).isLt
        have := fun h => hg0 (Fin.ext h); have := fun h => hg1 (Fin.ext h)
        have := fun h => hf0 (Fin.ext h); have := fun h => hf1 (Fin.ext h)
        omega
      · apply Fin.ext
        have := (col .groundNode).isLt
        have := (col (.varNode c.v0)).isLt
        have := (col (.varNode c.v2)).isLt
        have := fun h => hg0 (Fin.ext h); have := fun h => hg2 (Fin.ext h)
        have := fun h => hf0 (Fin.ext h); have := fun h => hf2 (Fin.ext h)
        omega
  -- Now derive contradiction: 3 distinct clauseNode colors can't all avoid one var color
  obtain ⟨hcol01, hcol02⟩ := hSameColor
  have hVC0c := hVC0 c
  have hVC1c : col (.clauseNode c 1) ≠ col (.varNode c.v0) :=
    fun h => hVC1 c (h.trans hcol01)
  have hVC2c : col (.clauseNode c 2) ≠ col (.varNode c.v0) :=
    fun h => hVC2 c (h.trans hcol02)
  -- Three distinct Fin 3 values all ≠ x is impossible (pigeonhole)
  have cn0 := (col (.clauseNode c 0)).isLt
  have cn1 := (col (.clauseNode c 1)).isLt
  have cn2 := (col (.clauseNode c 2)).isLt
  have cvx := (col (.varNode c.v0)).isLt
  have ne01 : (col (.clauseNode c 0)).val ≠ (col (.clauseNode c 1)).val :=
    fun h => hCC c hcIn 0 1 (by decide) (Fin.ext h)
  have ne02 : (col (.clauseNode c 0)).val ≠ (col (.clauseNode c 2)).val :=
    fun h => hCC c hcIn 0 2 (by decide) (Fin.ext h)
  have ne12 : (col (.clauseNode c 1)).val ≠ (col (.clauseNode c 2)).val :=
    fun h => hCC c hcIn 1 2 (by decide) (Fin.ext h)
  have nex0 : (col (.clauseNode c 0)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC0c (Fin.ext h)
  have nex1 : (col (.clauseNode c 1)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC1c (Fin.ext h)
  have nex2 : (col (.clauseNode c 2)).val ≠ (col (.varNode c.v0)).val :=
    fun h => hVC2c (Fin.ext h)
  omega

/-- Main reduction theorem from NAE-SAT to 3-Coloring. -/
theorem NAEtoColorReduction {V : Type} (f : NAESat3 V) :
  IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (NAEtoColorCompleteness f) (NAEtoColorSoundness f)

end NAEtoColor


/-!

# 3-SAT and 3-COLORING

## 3-SAT
The **3-SAT** problem asks: given a set of Boolean variables `x_1, ..., x_n` and
a set of clauses `C_1, ..., C_m`, where each clause is a disjunction of exactly
three literals (a variable or its negation), does there exist a Boolean assignment
that satisfies all clauses?

## Reduction from 3-SAT to 3-COLORING

Given a 3-SAT instance over variables `x_1, ..., x_n` and clauses `C_1, ..., C_m`,
we create an instance of 3-COLORING over the following vertices:
* A "palette" triangle with nodes `Base=0`, `True=1`, `False=2` (all pairwise connected).
* A "literal" node for each literal `x_i` and `¬x_i`.
* Six "clause gadget" nodes per clause that encode the OR constraint.

The edges are:
* All palette nodes are pairwise connected (triangle fixing color semantics).
* `Base` is connected to every literal node.
* `pos(x)` is connected to `neg(x)` (forcing them to get opposite truth colors).
* Internal clause gadget edges (nodes 0–2 and 3–5 form triangles) plus
  connections to the clause's three literals.
* Gadget node 5 is connected to `Base` and `False`, forcing it to receive color
  `True` whenever the clause is satisfied.

**Proof Sketch.**

_Completeness (SAT → Colorable):_
Given a satisfying assignment, color the palette nodes by their index, literal
nodes by their truth value, and clause gadgets by `clauseGadgetColor`. The
definition of `clauseGadgetColor` guarantees node 5 gets color T=1, and all
gadget internal edges get distinct colors.

_Soundness (Colorable → SAT):_
Given a valid 3-coloring, define `assign v := (col(pos v) = col(palette 1))`.
If some clause had all three literals false under this assignment, all three
literal nodes would have the same color (≠ T, ≠ Base), which forces a
contradiction via the gadget's internal edge structure (omega on Fin 3 values).
-/

namespace SATtoColor

inductive Literal (V : Type)
| pos (v : V)
| neg (v : V)

structure Clause (V : Type) where
  l1 : Literal V
  l2 : Literal V
  l3 : Literal V

def SatisfiesLiteral {V : Type} (assign : V → Bool) : Literal V → Bool
  | Literal.pos v => assign v
  | Literal.neg v => !(assign v)

def SatisfiesClause {V : Type} (assign : V → Bool) (c : Clause V) : Bool :=
  SatisfiesLiteral assign c.l1 || SatisfiesLiteral assign c.l2 || SatisfiesLiteral assign c.l3

abbrev Sat3 (V : Type) := List (Clause V)

def SatisfiesSat3 {V : Type} (assign : V → Bool) (f : Sat3 V) : Bool :=
  f.all (SatisfiesClause assign)

noncomputable def IsSatisfiable {V : Type} (f : Sat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesSat3 assign f = true

-- Some examples to test definitions:
namespace SAT3_Example

def sat3_inst : Sat3 (Fin 4) := [
  ⟨Literal.pos 0, Literal.neg 1, Literal.neg 2⟩,
  ⟨Literal.neg 0, Literal.pos 1, Literal.neg 2⟩,
  ⟨Literal.neg 0, Literal.neg 1, Literal.neg 3⟩
]

def ex_assign_1 := ![true, true, false, false]

#eval SatisfiesClause ex_assign_1 sat3_inst[2]
#eval SatisfiesSat3 ex_assign_1 sat3_inst

example : IsSatisfiable sat3_inst := ⟨ex_assign_1, rfl⟩

end SAT3_Example

/-- Vertex set for reduction from 3-SAT to 3-COLORING.
• palette     – the special triangle fixing color semantics (Base=0, T=1, F=2).
• literalNode – one node per literal (pos and neg are separate nodes).
• clauseGadget – six internal nodes per clause encoding the OR constraint.
-/
inductive OutputVertex (V : Type)
| palette (p : Fin 3)
| literalNode (l : Literal V)
| clauseGadget (c : Clause V) (idx : Fin 6)

/-- A simple graph is 3-colorable if there exists a valid 3-coloring. -/
def Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))

/-- Edge relation for reduction from 3-SAT to 3-COLORING. -/
def EdgeRelation {V : Type} (clauses : Sat3 V) (u v: OutputVertex V) : Prop :=
  match u, v with
  | .palette i, .palette j => i ≠ j
  | .palette 0, .literalNode _ => True
  | .literalNode _, .palette 0 => True
  | .literalNode (.pos x), .literalNode (.neg y) => x = y
  | .literalNode (.neg x), .literalNode (.pos y) => x = y
  | .clauseGadget c1 i, .clauseGadget c2 j =>
      c1 = c2 ∧ c1 ∈ clauses ∧ (
        (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨
        (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5) ∨
        (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 2) ∨
        (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 3) ∨ (i = 5 ∧ j = 4)
      )
  | .literalNode z, .clauseGadget c i =>
      ((z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4))
  | .clauseGadget c i, .literalNode z =>
      ((z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4))
  | .clauseGadget _ 5, .palette 0 => True
  | .palette 0, .clauseGadget _ 5 => True
  | .clauseGadget _ 5, .palette 2 => True
  | .palette 2, .clauseGadget _ 5 => True
  | _, _ => False

/-- Simple graph for reduction from 3-SAT to 3-Coloring. -/
def ReductionGraph {V : Type} (f : Sat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Coloring of clause gadget nodes given the boolean values of the three literals. -/
private def clauseGadgetColor (a b c3 : Bool) (k : Fin 6) : Fin 3 :=
  let ff3 := !a && !b && !c3
  let ff  := !a && !b
  match k with
  | ⟨5, _⟩ => 1
  | ⟨4, _⟩ => if ff3 then 0 else if ff then 2 else 0
  | ⟨3, _⟩ => if ff3 then 0 else if ff then 0 else 2
  | ⟨2, _⟩ => if ff3 then 0 else if ff then 2 else 1
  | ⟨1, _⟩ => if ff3 then 0 else if ff then 1 else if !b then 0 else 2
  | ⟨0, _⟩ => if ff3 then 0 else if ff then 0 else if !a then 0 else if !b then 2 else 0

/-- Coloring constructed from a satisfying assignment. -/
private def sat3Coloring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .palette p => p
  | .literalNode (.pos v) => if assign v then 1 else 2
  | .literalNode (.neg v) => if assign v then 2 else 1
  | .clauseGadget c k =>
      clauseGadgetColor (SatisfiesLiteral assign c.l1)
                        (SatisfiesLiteral assign c.l2)
                        (SatisfiesLiteral assign c.l3) k

private lemma sat3Coloring_litNode {V : Type} (assign : V → Bool) (l : Literal V) :
    sat3Coloring assign (.literalNode l) = if SatisfiesLiteral assign l then 1 else 2 := by
  match l with
  | .pos v => simp [sat3Coloring, SatisfiesLiteral]
  | .neg v =>
    show (if assign v then (2 : Fin 3) else 1) = if !assign v then 1 else 2
    match assign v with | true => rfl | false => rfl

/-- Completeness of reduction from 3-SAT to 3-Coloring. -/
lemma SATtoColorCompleteness {V : Type} (f : Sat3 V) :
  IsSatisfiable f → Is3Colorable (ReductionGraph f) := by
  intro ⟨assign, hsat⟩
  refine ⟨⟨sat3Coloring assign, ?_⟩⟩
  intro u v hadj
  simp only [SimpleGraph.top_adj]
  obtain ⟨hne, hedge⟩ := hadj
  suffices key : ∀ {a b : OutputVertex V}, EdgeRelation f a b →
                   sat3Coloring assign a ≠ sat3Coloring assign b by
    rcases hedge with h | h
    · exact key h
    · exact fun heq => key h heq.symm
  intro a b h
  unfold EdgeRelation at h
  match a, b with
  | .palette i, .palette j =>
    simp only [sat3Coloring]; exact h
  | .palette 0, .literalNode l =>
    rw [sat3Coloring_litNode]; simp only [sat3Coloring]
    cases SatisfiesLiteral assign l <;> simp
  | .literalNode l, .palette 0 =>
    rw [sat3Coloring_litNode]; simp only [sat3Coloring]
    cases SatisfiesLiteral assign l <;> simp
  | .literalNode (.pos x), .literalNode (.neg y) =>
    simp only [sat3Coloring]; subst h
    cases assign x <;> simp
  | .literalNode (.neg x), .literalNode (.pos y) =>
    simp only [sat3Coloring]; subst h
    cases assign x <;> simp
  | .clauseGadget _ 5, .palette 0 =>
    simp [sat3Coloring, clauseGadgetColor]
  | .palette 0, .clauseGadget _ 5 =>
    simp [sat3Coloring, clauseGadgetColor]
  | .clauseGadget _ 5, .palette 2 =>
    simp [sat3Coloring, clauseGadgetColor]
  | .palette 2, .clauseGadget _ 5 =>
    simp [sat3Coloring, clauseGadgetColor]
  | .literalNode z, .clauseGadget c k =>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals (
      rw [sat3Coloring_litNode]; simp only [sat3Coloring]
      cases hA : SatisfiesLiteral assign c.l1 <;>
      cases hB : SatisfiesLiteral assign c.l2 <;>
      cases hC : SatisfiesLiteral assign c.l3 <;>
      simp [clauseGadgetColor])
  | .clauseGadget c k, .literalNode z =>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals (
      rw [sat3Coloring_litNode]; simp only [sat3Coloring]
      cases hA : SatisfiesLiteral assign c.l1 <;>
      cases hB : SatisfiesLiteral assign c.l2 <;>
      cases hC : SatisfiesLiteral assign c.l3 <;>
      simp [clauseGadgetColor])
  | .clauseGadget c1 i, .clauseGadget c2 j =>
    obtain ⟨rfl, hcIn, hidx⟩ := h
    simp only [sat3Coloring]
    have hClauseTrue : SatisfiesClause assign c1 = true :=
      List.all_eq_true.mp hsat c1 hcIn
    rcases hidx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                     ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals (
      cases hA : SatisfiesLiteral assign c1.l1 <;>
      cases hB : SatisfiesLiteral assign c1.l2 <;>
      cases hC : SatisfiesLiteral assign c1.l3 <;>
      simp_all [clauseGadgetColor, SatisfiesClause])
  | .palette 1, .literalNode _
  | .palette 2, .literalNode _
  | .literalNode _, .palette 1
  | .literalNode _, .palette 2
  | .literalNode (.pos _), .literalNode (.pos _)
  | .literalNode (.neg _), .literalNode (.neg _) => exact False.elim h
  | .palette p, .clauseGadget c k =>
      fin_cases p <;> fin_cases k <;> simp_all [EdgeRelation, sat3Coloring, clauseGadgetColor]
  | .clauseGadget c k, .palette p =>
      fin_cases p <;> fin_cases k <;> simp_all [EdgeRelation, sat3Coloring, clauseGadgetColor]

/-- Soundness of reduction from 3-SAT to 3-Coloring. -/
lemma SATtoColorSoundness {V : Type} (f : Sat3 V) :
  Is3Colorable (ReductionGraph f) → IsSatisfiable f := by
  intro ⟨⟨col, hcol⟩⟩
  simp only [SimpleGraph.top_adj] at hcol
  have colNe : ∀ {u v : OutputVertex V},
      u ≠ v → (EdgeRelation f u v ∨ EdgeRelation f v u) → col u ≠ col v :=
    fun hne hedge => hcol ⟨hne, hedge⟩
  have hP01 : col (.palette 0) ≠ col (.palette 1) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hP02 : col (.palette 0) ≠ col (.palette 2) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hP12 : col (.palette 1) ≠ col (.palette 2) := colNe (by simp) (Or.inl (by simp [EdgeRelation]))
  have hLB : ∀ l : Literal V, col (.literalNode l) ≠ col (.palette 0) := fun l =>
    colNe (by simp) (Or.inr trivial)
  have hPN : ∀ x : V, col (.literalNode (.pos x)) ≠ col (.literalNode (.neg x)) := fun x =>
    colNe (by simp) (Or.inl rfl)
  have hG5B : ∀ c' : Clause V, col (.clauseGadget c' 5) ≠ col (.palette 0) := fun c' =>
    colNe (by simp) (Or.inl trivial)
  have hG5F : ∀ c' : Clause V, col (.clauseGadget c' 5) ≠ col (.palette 2) := fun c' =>
    colNe (by simp) (Or.inl trivial)
  let assign := fun v : V => decide (col (.literalNode (.pos v)) = col (.palette 1))
  have hLFT : ∀ l : Literal V, SatisfiesLiteral assign l = false →
      col (.literalNode l) ≠ col (.palette 1) := by
    intro l hl
    cases l with
    | pos v =>
      simp only [SatisfiesLiteral] at hl
      exact of_decide_eq_false hl
    | neg v =>
      simp only [SatisfiesLiteral] at hl
      have hav : col (.literalNode (.pos v)) = col (.palette 1) := by
        apply of_decide_eq_true
        cases h : assign v
        · exfalso; simp [h] at hl
        · exact h
      intro hcontra
      exact hPN v (hav.trans hcontra.symm)
  refine ⟨assign, ?_⟩
  simp only [SatisfiesSat3, List.all_eq_true]
  intro c hcIn
  by_contra hFalse
  have hSatF : SatisfiesClause assign c = false := by
    cases h : SatisfiesClause assign c with
    | true => exact absurd h hFalse
    | false => rfl
  simp only [SatisfiesClause] at hSatF
  have hl1F : SatisfiesLiteral assign c.l1 = false := by
    cases h : SatisfiesLiteral assign c.l1 <;> simp_all
  have hl2F : SatisfiesLiteral assign c.l2 = false := by
    cases h : SatisfiesLiteral assign c.l2 <;> simp_all
  have hl3F : SatisfiesLiteral assign c.l3 = false := by
    cases h : SatisfiesLiteral assign c.l3 <;> simp_all
  have hL1neT := hLFT c.l1 hl1F
  have hL2neT := hLFT c.l2 hl2F
  have hL3neT := hLFT c.l3 hl3F
  have hG5T : col (.clauseGadget c 5) = col (.palette 1) := by
    apply Fin.ext
    have i0 := (col (.clauseGadget c 5)).isLt
    have i1 := (col (.palette 0)).isLt
    have i2 := (col (.palette 1)).isLt
    have i3 := (col (.palette 2)).isLt
    have h1 : (col (.clauseGadget c 5)).val ≠ (col (.palette 0)).val := fun h => hG5B c (Fin.ext h)
    have h2 : (col (.clauseGadget c 5)).val ≠ (col (.palette 2)).val := fun h => hG5F c (Fin.ext h)
    have h3 : (col (.palette 0)).val ≠ (col (.palette 1)).val := fun h => hP01 (Fin.ext h)
    have h4 : (col (.palette 0)).val ≠ (col (.palette 2)).val := fun h => hP02 (Fin.ext h)
    have h5 : (col (.palette 1)).val ≠ (col (.palette 2)).val := fun h => hP12 (Fin.ext h)
    omega
  have hG01 : col (.clauseGadget c 0) ≠ col (.clauseGadget c 1) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inl ⟨rfl, rfl⟩⟩)
  have hG02 : col (.clauseGadget c 0) ≠ col (.clauseGadget c 2) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
  have hG12 : col (.clauseGadget c 1) ≠ col (.clauseGadget c 2) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
  have hG23 : col (.clauseGadget c 2) ≠ col (.clauseGadget c 3) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩)
  have hG34 : col (.clauseGadget c 3) ≠ col (.clauseGadget c 4) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)
  have hG35 : col (.clauseGadget c 3) ≠ col (.clauseGadget c 5) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩)
  have hG45 : col (.clauseGadget c 4) ≠ col (.clauseGadget c 5) :=
    colNe (by simp) (Or.inl ⟨rfl, hcIn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩)
  have hL1G0 : col (.literalNode c.l1) ≠ col (.clauseGadget c 0) :=
    colNe (by simp) (Or.inl (Or.inl ⟨rfl, rfl⟩))
  have hL2G1 : col (.literalNode c.l2) ≠ col (.clauseGadget c 1) :=
    colNe (by simp) (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hL3G4 : col (.literalNode c.l3) ≠ col (.clauseGadget c 4) :=
    colNe (by simp) (Or.inl (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  have vp0 := (col (.palette 0)).isLt;       have vp1 := (col (.palette 1)).isLt
  have vp2 := (col (.palette 2)).isLt
  have vg0 := (col (.clauseGadget c 0)).isLt; have vg1 := (col (.clauseGadget c 1)).isLt
  have vg2 := (col (.clauseGadget c 2)).isLt; have vg3 := (col (.clauseGadget c 3)).isLt
  have vg4 := (col (.clauseGadget c 4)).isLt; have vg5 := (col (.clauseGadget c 5)).isLt
  have vl1 := (col (.literalNode c.l1)).isLt; have vl2 := (col (.literalNode c.l2)).isLt
  have vl3 := (col (.literalNode c.l3)).isLt
  have hp01 : (col (.palette 0)).val ≠ (col (.palette 1)).val := fun h => hP01 (Fin.ext h)
  have hp02 : (col (.palette 0)).val ≠ (col (.palette 2)).val := fun h => hP02 (Fin.ext h)
  have hp12 : (col (.palette 1)).val ≠ (col (.palette 2)).val := fun h => hP12 (Fin.ext h)
  have hl1b : (col (.literalNode c.l1)).val ≠ (col (.palette 0)).val := fun h => hLB c.l1 (Fin.ext h)
  have hl2b : (col (.literalNode c.l2)).val ≠ (col (.palette 0)).val := fun h => hLB c.l2 (Fin.ext h)
  have hl3b : (col (.literalNode c.l3)).val ≠ (col (.palette 0)).val := fun h => hLB c.l3 (Fin.ext h)
  have hl1t : (col (.literalNode c.l1)).val ≠ (col (.palette 1)).val := fun h => hL1neT (Fin.ext h)
  have hl2t : (col (.literalNode c.l2)).val ≠ (col (.palette 1)).val := fun h => hL2neT (Fin.ext h)
  have hl3t : (col (.literalNode c.l3)).val ≠ (col (.palette 1)).val := fun h => hL3neT (Fin.ext h)
  have hl1g0 : (col (.literalNode c.l1)).val ≠ (col (.clauseGadget c 0)).val := fun h => hL1G0 (Fin.ext h)
  have hl2g1 : (col (.literalNode c.l2)).val ≠ (col (.clauseGadget c 1)).val := fun h => hL2G1 (Fin.ext h)
  have hl3g4 : (col (.literalNode c.l3)).val ≠ (col (.clauseGadget c 4)).val := fun h => hL3G4 (Fin.ext h)
  have hg01 : (col (.clauseGadget c 0)).val ≠ (col (.clauseGadget c 1)).val := fun h => hG01 (Fin.ext h)
  have hg02 : (col (.clauseGadget c 0)).val ≠ (col (.clauseGadget c 2)).val := fun h => hG02 (Fin.ext h)
  have hg12 : (col (.clauseGadget c 1)).val ≠ (col (.clauseGadget c 2)).val := fun h => hG12 (Fin.ext h)
  have hg23 : (col (.clauseGadget c 2)).val ≠ (col (.clauseGadget c 3)).val := fun h => hG23 (Fin.ext h)
  have hg34 : (col (.clauseGadget c 3)).val ≠ (col (.clauseGadget c 4)).val := fun h => hG34 (Fin.ext h)
  have hg35 : (col (.clauseGadget c 3)).val ≠ (col (.clauseGadget c 5)).val := fun h => hG35 (Fin.ext h)
  have hg45 : (col (.clauseGadget c 4)).val ≠ (col (.clauseGadget c 5)).val := fun h => hG45 (Fin.ext h)
  have hg5t : (col (.clauseGadget c 5)).val = (col (.palette 1)).val := congrArg Fin.val hG5T
  omega

/-- Main theorem: 3-SAT is satisfiable iff the reduction graph is 3-colorable. -/
theorem SATtoColorReduction {V : Type} (f : Sat3 V) :
  IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (SATtoColorCompleteness f) (SATtoColorSoundness f)

end SATtoColor
