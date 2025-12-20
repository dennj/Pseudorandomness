/-
  Complexity Classes - Computational Model Module
  ================================================

  Computational model, polynomial time, and complexity class definitions.

  This module defines the computational model for polynomial time computation,
  including polynomial bounds, computation states, step functions, and the
  formal definitions of P and NP complexity classes.

  Key definitions:
  - PolyBound: polynomial time bound structure
  - ComputationState: state of a computation
  - StepFunction: one-step transition function
  - PolyTimeComputable: polynomial-time computable functions
  - NPVerifier: verifier for NP languages
  - InNP: NP complexity class membership
-/

import Pseudorandomness.Basic.Foundations
import Pseudorandomness.Basic.Circuits
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log

namespace ComplexityBarriers

/--
  A polynomial time bound: time(n) ≤ c * n^k for some constants c, k.
  This represents the class of polynomial functions.
-/
structure PolyBound where
  /-- Coefficient in the polynomial bound -/
  c : ℕ
  /-- Exponent in the polynomial bound -/
  k : ℕ
  /-- The bound is positive -/
  c_pos : c > 0 := by decide

/-- Evaluate the polynomial bound at input size n -/
def PolyBound.eval (p : PolyBound) (n : ℕ) : ℕ := p.c * n^p.k + p.c

/-! ## Computational Model for Polynomial Time -/

/--
  A computation state for a simple RAM-like model.
  This is an abstract model where:
  - state: The internal state of the computation (polymorphic)
  - steps: Number of computation steps taken so far
-/
structure ComputationState (σ : Type) where
  state : σ
  steps : ℕ

/--
  A step function that advances computation by one step.
  Returns `none` if computation has halted, `some newState` otherwise.
-/
def StepFunction (σ : Type) := σ → Option σ

/--
  Run a computation for at most `fuel` steps.
  Returns the final state and number of steps taken.
-/
def runComputation {σ : Type} (step : StepFunction σ) (initial : σ) (fuel : ℕ) : ComputationState σ :=
  match fuel with
  | 0 => ⟨initial, 0⟩
  | fuel' + 1 =>
    match step initial with
    | none => ⟨initial, 0⟩  -- Halted
    | some next =>
      let result := runComputation step next fuel'
      ⟨result.state, result.steps + 1⟩

/--
  A computation terminates within `bound` steps if running with that much fuel
  causes the step function to return `none` (halt) before exhausting fuel.
-/
def terminatesWithin {σ : Type} (step : StepFunction σ) (initial : σ) (bound : ℕ) : Prop :=
  ∃ k ≤ bound, ∃ s, (runComputation step initial k).state = s ∧ step s = none

/--
  A function f : α → β is computable in time T(n) if there exists:
  1. An encoding of inputs α into computation states
  2. A step function
  3. A decoding of final states into outputs β
  Such that for all inputs x of size n, the computation terminates in ≤ T(n) steps.
-/
structure PolyTimeComputable {α β : Type} (f : α → β) (inputSize : α → ℕ) where
  /-- Internal state type -/
  StateType : Type
  /-- Encode input into initial state -/
  encode : α → StateType
  /-- The step function -/
  step : StepFunction StateType
  /-- Decode final state into output -/
  decode : StateType → β
  /-- Polynomial time bound -/
  timeBound : PolyBound
  /-- The computation terminates within the time bound -/
  terminates : ∀ x, terminatesWithin step (encode x) (timeBound.eval (inputSize x))
  /-- The computation produces the correct result -/
  correct : ∀ x, ∀ k ≤ timeBound.eval (inputSize x),
    step (runComputation step (encode x) k).state = none →
    decode (runComputation step (encode x) k).state = f x

/--
  A verification function is polynomial-time if it's computable in polynomial time
  with respect to the input size.

  This is stated as an existential: there exists a polynomial bound such that
  for all input sizes, the verifier terminates within that bound.
-/
def IsPolyTimeVerifier (witnessLen : ℕ → ℕ)
    (verify : (inputSize : ℕ) → Fin (2^inputSize) → Fin (2^(witnessLen inputSize)) → Bool) : Prop :=
  ∃ (bound : PolyBound), ∀ (inputSize : ℕ),
    ∃ (σ : Type) (encode : Fin (2^inputSize) × Fin (2^(witnessLen inputSize)) → σ)
      (step : StepFunction σ) (decode : σ → Bool),
    ∀ (x : Fin (2^inputSize)) (w : Fin (2^(witnessLen inputSize))),
      terminatesWithin step (encode (x, w)) (bound.eval inputSize) ∧
      (∀ k ≤ bound.eval inputSize, step (runComputation step (encode (x, w)) k).state = none →
        decode (runComputation step (encode (x, w)) k).state = verify inputSize x w)

/--
  A verifier for an NP language.

  The verifier V takes:
  - n: the input size parameter
  - x: the input (encoded as Fin (2^n))
  - w: the witness (encoded as Fin (2^witnessLen n))

  And returns true iff the witness is valid for the input.
-/
structure NPVerifier (n : ℕ) where
  /-- Polynomial bound on witness length: |w| ≤ p(|x|) -/
  witnessLenBound : PolyBound
  /-- The verification function -/
  verify : (inputSize : ℕ) → Fin (2^inputSize) → Fin (2^(witnessLenBound.eval inputSize)) → Bool
  /-- Polynomial time bound -/
  timeBound : PolyBound
  /--
    The verifier runs in polynomial time.
    This asserts that `verify` is computable by some algorithm that terminates
    within `timeBound.eval(inputSize)` steps for all inputs.
  -/
  runsInPolyTime : IsPolyTimeVerifier witnessLenBound.eval verify

/--
  A language L : ℕ → BoolFun n is in NP if there exists a polynomial-time verifier
  such that:
  - Completeness: If L(x) = true, there exists a witness w such that V(x,w) = true
  - Soundness: If V(x,w) = true for some w, then L(x) = true

  The witness length and verification time are both polynomially bounded.
-/
structure InNP (L : ℕ → BoolFun n) where
  /-- The polynomial-time verifier -/
  verifier : NPVerifier n
  /--
    Completeness: For every accepting input, there exists a valid witness.
    L(x) = true → ∃ w, V(x, w) = true
  -/
  complete : ∀ (inputSize : ℕ) (x : Fin (2^inputSize)),
    (∀ (h : inputSize = n), L inputSize (Fin.cast (by rw [h]) x) = true) →
    ∃ w, verifier.verify inputSize x w = true
  /--
    Soundness: If there's a valid witness, the input is accepting.
    ∃ w, V(x, w) = true → L(x) = true
  -/
  sound : ∀ (inputSize : ℕ) (x : Fin (2^inputSize)) (w : Fin (2^(verifier.witnessLenBound.eval inputSize))),
    verifier.verify inputSize x w = true →
    ∀ (h : inputSize = n), L inputSize (Fin.cast (by rw [h]) x) = true

end ComplexityBarriers
