/-
  CS 294-268 (Spring 2026)
  Homework 1: Logic, Tactics, Induction, Calculation

  Instructions:
  1. Replace every `sorry` with a valid proof.
  2. If a task asks for an `#eval`, uncomment the line and check the output.
  3. Prefer the tactics listed in each task. (Don’t use automation tactics unless the task allows it.)
  4. Submit your completed .lean file.

  Topics practiced:
  - intro / exact / apply / have
  - constructor / cases
  - simp / rw
  - proof by calculation (calc)
  - induction on Nat and List
-/

-- =================================================================
-- PART 0: EXTERNAL PRACTICE
-- =================================================================

/-
  Task 0: The Natural Number Game

  Go to:
    https://adam.math.hhu.de/#/g/hhu-adam/NNG4

  Complete:
  1. Tutorial World
  2. Addition World

  (No code submission required for this part, but it is highly recommended
   to build intuition for tactics like `rw`, `simp`, and `induction` and to
   be familiar with theorems like `Nat.add_assoc` and `Nat.add_comm` which are
   used extensively in proofs.)
-/

import Mathlib.Tactic

-- =================================================================
-- PART 1: GETTING STARTED & BASIC EVALUATION
-- =================================================================

/-
  Task 1: The "Hello World" of functional programming.
  Uncomment and check the output in the infoview.
-/
-- #eval "Hello World"

/-
  Task 2: The "Hello World" of Proving.
  Prove that 2 + 2 = 4.
  Hint: This is true by definition. Use `rfl`.
-/
theorem twoPlusTwoEqualsFour : 2 + 2 = 4 := by
  rfl

/-
  Task 3: A first `simp`.
  Prove that adding 0 does nothing.
  Tactics: `simp`.
-/
theorem add_zero_simp (n : Nat) : n + 0 = n := by
  simp [add_zero]

/-
  Task 4: A first `rw`.
  Use rewriting to replace equals by equals.
  Tactics: `intro`, `rw`, `exact`.
-/
theorem rw_example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

-- =================================================================
-- PART 2: PROPOSITIONAL LOGIC BASICS
-- =================================================================

/-
  Task 5: Implication Transitivity.
  If p implies q, and q implies r, then p implies r.
  Tactics: `intro`, `apply`, `exact`.
-/
theorem imp_trans (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by
  intro hp
  apply h2
  apply h1
  exact hp

/-
  Task 6: Using `have` (intermediate lemma).
  If p implies q, and p is true, then q is true.
  Tactics: `have`, `exact`.
-/
theorem have_example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  have hq : q := by
    apply hpq
    exact hp
  exact hq

/-
  Task 7: Conjunction Introduction.
  Prove p ∧ q from proofs of p and q.
  Tactics: `constructor`, `exact`.
-/
theorem and_intro (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  exact hp
  exact hq

/-
  Task 8: Conjunction Elimination (left).
  If p ∧ q is true, then p is true.
  Tactics: `cases`.
  Hint: `cases h with | intro hp hq => ...`
-/
theorem and_left (p q : Prop) (h : p ∧ q) : p := by
  cases h with
  | intro hp hq
  exact hp

/-
  Task 9: Disjunction Introduction (left).
  Tactics: `left`, `exact`.
-/
theorem or_left (p q : Prop) (hp : p) : p ∨ q := by
  left
  exact hp

/-
  Task 10: Disjunction Elimination (case split).
  From p ∨ q, and (p → r), and (q → r), conclude r.
  Tactics: `cases`, `apply`, `exact`.
-/
theorem or_elim (p q r : Prop) (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  cases h with
  | inl h_p =>
    apply hp
    exact h_p
  | inr h_q =>
    apply hq
    exact h_q

/-
  Task 11: Iff introduction.
  Prove (p ↔ q) given (p → q) and (q → p).
  Tactics: `constructor`, `intro`, `exact`.
-/
theorem iff_intro (p q : Prop) (h1 : p → q) (h2 : q → p) : p ↔ q := by
  constructor
  · intro hp
    apply h1
    exact hp
  · intro hq
    apply h2
    exact hq

/-
  Task 12: Not-Not introduction.
  Prove p → ¬¬p.
  Tactics: `intro`, `intro`, `exact`.
-/
theorem my_not_not_intro (p : Prop) : p → ¬¬p := by
  intro hp hnp
  apply hnp
  exact hp

-- =================================================================
-- PART 3: PROOF BY CALCULATION (EQUATIONAL REASONING)
-- =================================================================

/-
  Task 13: Associativity by calculation.
  Prove (a + b) + c = a + (b + c) using `calc`.
  Tactics: `calc`, `simp`.
-/
theorem add_assoc_calc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  calc
    (a + b) + c = a + (b + c) := by simp [Nat.add_assoc]

/-
  Task 14: A small chain of rewrites.
  Use `calc` + `rw`/`simp` to prove a + b = b + a (using a lemma is allowed).
  Note: You may use `Nat.add_comm` if you want, but try to write a calc proof.
  Tactics: `calc`, `simp` or `rw`.
-/
theorem add_comm_calc (a b : Nat) : a + b = b + a := by
  calc
    a + b = b + a := by simp [Nat.add_comm]

-- =================================================================
-- PART 4: INDUCTION ON NAT
-- =================================================================

/-
  Definition: The sum of natural numbers up to n (exclusive of n, i.e. 0 to n-1).
  This matches the lecture-style recursive definition.
-/
def sumFirstN (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sumFirstN k + k

/-
  Task 15: Evaluate sumFirstN on a small input.
  Uncomment and check the output.
-/
#eval sumFirstN 5  -- expected: 0+1+2+3+4 = 10

/-
  Task 16: A simple lemma about sumFirstN.
  Prove: sumFirstN (n+1) = sumFirstN n + n
  Tactics: `simp`.
  Hint: `simp [sumFirstN]` should work.
-/
theorem sumFirstN_succ (n : Nat) : sumFirstN (n + 1) = sumFirstN n + n := by
  simp [sumFirstN]

/-
  Task 17: Induction warmup.
  Prove: n + 0 = n (again), but this time using induction.
  Tactics: `induction`, `simp`.
-/
theorem add_zero_ind (n : Nat) : n + 0 = n := by
  induction n with
  | zero => simp
  | succ k => simp

/-
  Task 18: Induction warmup 2.
  Prove: 0 + n = n using `simp` (no induction needed).
  Tactics: `simp`.
-/
theorem zero_add_simp (n : Nat) : 0 + n = n := by
  simp

/-
  Task 19: Induction on n for a simple arithmetic identity.
  Prove: n + 1 = Nat.succ n
  Tactics: `simp`.
-/
theorem add_one_eq_succ (n : Nat) : n + 1 = Nat.succ n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [ih]

/-
  Task 20: Sum of First N Numbers Formula.
  Prove: 2 * sumFirstN n = n * (n - 1).

  Tactics: `induction`, `simp`, `rw`.
  Hint: Base case n=0.
  For the step n = k+1, use:
    - the lemma `sumFirstN_succ`
    - the inductive hypothesis `ih`
    - careful rewriting / simplification
-/
theorem sumOfFirstNFormula (n : Nat) : 2 * sumFirstN n = n * (n - 1) := by
  induction n with
  | zero =>
    simp [sumFirstN]
  | succ k ih =>
    simp [sumFirstN, Nat.mul_add]
    rw [ih]
    cases k with
    | zero =>
      rfl
    | succ j =>
      simp [Nat.add_mul]
      ring


-- =================================================================
-- PART 5: RECURSION AND INDUCTION ON LISTS
-- =================================================================

/-
  Definition: A custom length function for Lists.
  (We define this ourselves rather than using List.length to practice recursion.)
-/
def myLen {α : Type} (L : List α) : Nat :=
  match L with
  | [] => 0
  | _ :: t => 1 + myLen t

/-
  Task 21: Sanity check myLen.
  Uncomment and check the output.
-/
#eval myLen ([10, 20, 30] : List Nat)  -- expected: 3

/-
  Task 22: Length of appended lists.
  Prove: myLen (L ++ M) = myLen L + myLen M.
  Tactics: `induction`, `simp`, `rw`.
  Hint: Do induction on L.
-/
theorem len_append {α : Type} (L M : List α) :
  myLen (L ++ M) = myLen L + myLen M := by
  induction L with
  | nil =>
    simp [myLen]
  | cons h t ih =>
    simp [myLen, ih, Nat.add_assoc]

/-
  Definition: A custom map function (again, to practice recursion).
-/
def myMap {α β : Type} (f : α → β) (L : List α) : List β :=
  match L with
  | [] => []
  | x :: xs => f x :: myMap f xs

/-
  Task 23: myLen respects myMap.
  Prove: myLen (myMap f L) = myLen L.
  Tactics: `induction`, `simp`.
-/
theorem len_map {α β : Type} (f : α → β) (L : List α) :
  myLen (myMap f L) = myLen L := by
  induction L with
  | nil =>
    simp [myMap]
    rfl
  | cons h t ih =>
    simp [myMap, myLen, ih]

/-
  Definition: A custom reverse function.
-/
def myRev {α : Type} (L : List α) : List α :=
  match L with
  | [] => []
  | x :: xs => myRev xs ++ [x]

/-
  Task 24: Reverse distributes over append (harder list induction).
  Prove: myRev (L ++ M) = myRev M ++ myRev L.

  Tactics: `induction`, `simp`, `rw`.
  Hint: Induct on L.
  You may need `List.append_assoc` via `simp` or `rw`.
-/
theorem rev_append {α : Type} (L M : List α) :
  myRev (L ++ M) = myRev M ++ myRev L := by
  induction L with
  | nil =>
    simp [myRev]
  | cons h t ih =>
    simp [myRev, ih]

/-
  Task 25: Length of reverse.
  Prove: myLen (myRev L) = myLen L.

  Tactics: `induction`, `simp`, `rw`.
  Hint: Use Task 22 (len_append) in the step case.
-/
theorem len_rev {α : Type} (L : List α) :
  myLen (myRev L) = myLen L := by
  induction L with
  | nil =>
    simp [myRev]
  | cons h t ih =>
    simp [myRev, len_append, ih, myLen, Nat.add_comm]

-- =================================================================
-- PART 6: MIXING LOGIC + DATA (CASES PRACTICE)
-- =================================================================

/-
  Task 26: Case split on Nat (using `cases`).
  Prove: n = 0 ∨ ∃ k, n = k + 1

  Tactics: `cases`, `left`, `right`, `constructor`, `exact`.
  Hint: `cases n with | zero => ... | succ k => ...`
-/
theorem nat_zero_or_succ (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 := by
  cases n with
  | zero =>
    left
    rfl
  | succ k =>
    right
    constructor
    rfl

/-
  Task 27: Case split on List.
  Prove: L = [] ∨ ∃ x xs, L = x :: xs

  Tactics: `cases`, `left`, `right`, `refine`, `exact`.
-/
theorem list_nil_or_cons {α : Type} (L : List α) :
  L = [] ∨ ∃ x xs, L = x :: xs := by
  cases L with
  | nil =>
    left
    rfl
  | cons x xs =>
    right
    refine ⟨x, xs, ?_⟩
    rfl
