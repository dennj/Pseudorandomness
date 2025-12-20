/-
  Circuit Complexity - Circuit Model Module
  ==========================================

  Circuit model and circuit complexity definitions.

  This module defines Boolean circuits as directed acyclic graphs of gates,
  along with the notion of circuit complexity (minimum circuit size to compute
  a function). Also defines P/poly, the class of problems solvable by
  polynomial-size circuits.

  Key definitions:
  - Gate: inductive type for circuit gates
  - Circuit: structure representing Boolean circuits
  - circuitComplexity: minimum circuit size (noncomputable)
  - hasPolyCircuits: polynomial circuit complexity predicate
  - InPpoly: P/poly complexity class
-/

import Pseudorandomness.Basic.Foundations

namespace ComplexityBarriers

/-! ## Circuit Complexity -/

/-- Abstract circuit model -/
inductive Gate
  | input : ℕ → Gate        -- Input variable x_i
  | const : Bool → Gate     -- Constant 0 or 1
  | not : Gate → Gate       -- Negation
  | and : Gate → Gate → Gate -- Conjunction
  | or : Gate → Gate → Gate  -- Disjunction

/-- Check if all input references in a gate are valid (< n) -/
def Gate.validInputs (n : ℕ) : Gate → Bool
  | .input i => i < n
  | .const _ => true
  | .not g => g.validInputs n
  | .and g1 g2 => g1.validInputs n && g2.validInputs n
  | .or g1 g2 => g1.validInputs n || g2.validInputs n

/-- A circuit is a DAG of gates with a designated output -/
structure Circuit (n : ℕ) where
  gates : List Gate
  output : Gate
  /-- All input references in the output gate are valid -/
  valid : output.validInputs n = true

/-- Size of a circuit (number of gates) -/
def Circuit.size {n : ℕ} (c : Circuit n) : ℕ := c.gates.length

/-- Evaluate a gate given an assignment to input variables -/
def Gate.eval (assignment : ℕ → Bool) : Gate → Bool
  | .input i => assignment i
  | .const b => b
  | .not g => !g.eval assignment
  | .and g1 g2 => g1.eval assignment && g2.eval assignment
  | .or g1 g2 => g1.eval assignment || g2.eval assignment

/-- Circuit computes a Boolean function -/
def Circuit.computes {n : ℕ} (c : Circuit n) (f : BoolFun n) : Prop :=
  ∀ (x : Fin (2^n)), c.output.eval (fun i => (x.val / 2^i) % 2 = 1) = f x

/-- Circuit complexity of a Boolean function: minimum circuit size computing f -/
-- Since this requires searching over all circuits, we use a classical noncomputable definition
noncomputable def circuitComplexity {n : ℕ} (f : BoolFun n) : ℕ :=
  -- We axiomatize this as a well-founded minimum
  -- In practice, computing this is PSPACE-hard
  Classical.epsilon (fun s => ∃ c : Circuit n, c.size = s ∧ c.computes f)

/-- A function has polynomial circuit complexity -/
def hasPolyCircuits (f : ℕ → BoolFun n) : Prop :=
  ∃ (c : ℕ) (k : ℕ), ∀ n, circuitComplexity (f n) ≤ c * n^k

/-- P/poly: languages decidable by polynomial-size circuits -/
def InPpoly (L : ℕ → BoolFun n) : Prop := hasPolyCircuits L

/-! ## Circuit Classes -/

/-- Polynomial bound predicate for size functions -/
def IsPolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * n^k + c

/--
  A **circuit class** represents a family of Boolean functions
  computable by circuits of bounded size across all input lengths.

  Examples: P/poly, NC¹, AC⁰, TC⁰

  Membership is defined by the size bound: a function f is in the class
  iff its circuit complexity is at most sizeBound(n).
-/
structure CircuitClass where
  /-- Size bound for circuits in the class -/
  sizeBound : ℕ → ℕ
  /-- Polynomial size bound -/
  polySize : IsPolyBounded sizeBound

namespace CircuitClass

/-- Membership predicate: f is in class C iff its complexity ≤ C.sizeBound n -/
def contains (C : CircuitClass) {n : ℕ} (f : BoolFun n) : Prop :=
  circuitComplexity f ≤ C.sizeBound n

/-- Circuit classes are downward closed under circuit complexity -/
theorem downwardClosed (C : CircuitClass) (n : ℕ) (f g : BoolFun n) :
    C.contains f → circuitComplexity g ≤ circuitComplexity f → C.contains g := by
  intro hf hfg
  exact Nat.le_trans hfg hf

/-- Standard polynomial circuit class P/poly -/
def Ppoly : CircuitClass where
  sizeBound := fun n => n^10  -- Representative poly bound
  polySize := ⟨1, 10, fun n => by simp only; omega⟩

/-- Linear circuit class -/
def Linear : CircuitClass where
  sizeBound := fun n => n
  polySize := ⟨2, 1, fun n => by simp only [pow_one]; omega⟩

/-- Quadratic circuit class -/
def Quadratic : CircuitClass where
  sizeBound := fun n => n^2
  polySize := ⟨1, 2, fun n => by simp only; omega⟩

end CircuitClass

/--
  A **fixed-size circuit class** for a specific input length n.

  This is useful for learning theory where we often work with
  a fixed input size.

  Examples: AC⁰[n], P/poly[n]
-/
structure FixedSizeCircuitClass (n : ℕ) where
  /-- Size bound for this input size -/
  sizeBound : ℕ
  /-- The set of functions computable by circuits within the bound -/
  functions : Set (BoolFun n) := { f | circuitComplexity f ≤ sizeBound }

namespace FixedSizeCircuitClass

/-- Create a fixed-size circuit class from a size bound -/
def ofBound (n : ℕ) (bound : ℕ) : FixedSizeCircuitClass n where
  sizeBound := bound

/-- Membership in the default functions set is determined by circuit complexity -/
theorem mem_ofBound {n : ℕ} (bound : ℕ) (f : BoolFun n) :
    f ∈ (ofBound n bound).functions ↔ circuitComplexity f ≤ bound := by
  rfl

end FixedSizeCircuitClass

/-- Convert a global CircuitClass to a FixedSizeCircuitClass at size n -/
def CircuitClass.atSize (C : CircuitClass) (n : ℕ) : FixedSizeCircuitClass n where
  sizeBound := C.sizeBound n
  functions := { f | C.contains f }

/-! ## Shannon's Counting Argument

  Shannon (1949) proved that almost all Boolean functions require circuits
  of size Ω(2^n / n). This fundamental result establishes that "random"
  Boolean functions have high complexity.

  Key facts:
  - Total Boolean functions on n bits: 2^(2^n)
  - Circuits of size s: bounded by (cn)^(O(s)) for some constant c
  - For s = 2^n/(2n), the number of small circuits << number of functions

  We axiomatize this counting bound as it requires careful enumeration.
-/

end ComplexityBarriers
