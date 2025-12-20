/-
  Control Theory Bridge - Observability as Non-Pseudorandomness
  ==============================================================

  This module establishes a bridge between the observer barrier framework
  and classical control theory. The main result:

    **Observable ↔ State not pseudorandom to output observers**

  This connects the 1960s Kalman observability theory to the pseudorandomness
  framework, showing that "observability" IS "distinguishability from random."

  ## The Control Theory Setting

  A discrete-time linear system:
    x_{t+1} = A x_t + B u_t    (state dynamics)
    y_t = C x_t                 (output equation)

  **Observability Question**: Given outputs y₀, y₁, ..., y_{n-1}, can we
  determine the initial state x₀?

  ## The Classical Result (Kalman 1960)

  A system (A, C) is observable iff the observability matrix
    𝒪 = [C; CA; CA²; ...; CA^{n-1}]
  has full column rank.

  ## Our Bridge Theorem

  We show this is equivalent to: "no two distinct states produce identical
  output sequences" — i.e., states are NOT pseudorandom to output observers.

  **References**:
  - R.E. Kalman. "On the General Theory of Control Systems."
    IFAC Proceedings, 1(1):491-502, 1960.
  - R.E. Kalman. "Mathematical Description of Linear Dynamical Systems."
    SIAM J. Control, 1(2):152-192, 1963.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fin.VecNotation

namespace ControlTheory

/-! ## Linear Dynamical Systems

We define discrete-time linear systems over a field 𝕜.
For simplicity, we focus on autonomous systems (no input) since
observability is a property of the (A, C) pair.
-/

variable {𝕜 : Type*} [Field 𝕜]
variable {n m : ℕ}  -- n = state dimension, m = output dimension

/--
  A **LinearSystem** consists of:
  - State transition matrix A : 𝕜^{n×n}
  - Output matrix C : 𝕜^{m×n}

  Dynamics: x_{t+1} = A x_t
  Output: y_t = C x_t
-/
structure LinearSystem (𝕜 : Type*) [Field 𝕜] (n m : ℕ) where
  /-- State transition matrix -/
  A : Matrix (Fin n) (Fin n) 𝕜
  /-- Output matrix -/
  C : Matrix (Fin m) (Fin n) 𝕜

namespace LinearSystem

variable (sys : LinearSystem 𝕜 n m)

/--
  State at time t given initial state x₀.
  x_t = A^t x₀
-/
def stateAt (x₀ : Fin n → 𝕜) (t : ℕ) : Fin n → 𝕜 :=
  (sys.A ^ t).mulVec x₀

/--
  Output at time t given initial state x₀.
  y_t = C A^t x₀
-/
def outputAt (x₀ : Fin n → 𝕜) (t : ℕ) : Fin m → 𝕜 :=
  sys.C.mulVec (sys.stateAt x₀ t)

/--
  The output sequence y₀, y₁, ..., y_{k-1} as a function.
-/
def outputSequence (x₀ : Fin n → 𝕜) (k : ℕ) : Fin k → (Fin m → 𝕜) :=
  fun t => sys.outputAt x₀ t

/-! ## Observability -/

/--
  **Observability (Semantic Definition)**

  A system is observable if distinct initial states produce distinct
  output sequences. Equivalently: the output sequence determines the
  initial state uniquely.

  Formally: ∀ x₀ x₀', (∀ t < n, y_t(x₀) = y_t(x₀')) → x₀ = x₀'
-/
def IsObservable : Prop :=
  ∀ x₀ x₀' : Fin n → 𝕜,
    (∀ t : Fin n, sys.outputAt x₀ t = sys.outputAt x₀' t) → x₀ = x₀'

/--
  **Unobservable Subspace**

  The set of states that produce zero output for all t < n.
  For observable systems, this is {0}.
-/
def UnobservableSubspace : Set (Fin n → 𝕜) :=
  {x | ∀ t : Fin n, sys.outputAt x t = 0}

/--
  Observable iff the unobservable subspace is trivial.

  **Proof sketch**:
  (→) If observable and x produces zero output, then x = 0 by comparing with 0.
  (←) If unobservable subspace is {0} and x₀, x₀' have same outputs,
      then x₀ - x₀' is in the unobservable subspace (by linearity), hence = 0.
-/
theorem observable_iff_trivial_unobservable :
    sys.IsObservable ↔ sys.UnobservableSubspace = {0} := by
  constructor
  · -- Observable → Unobservable subspace is {0}
    intro hObs
    ext x
    constructor
    · intro hZero
      -- x produces zero output, so does 0
      have h0 : ∀ t : Fin n, sys.outputAt 0 t = 0 := by
        intro t
        simp only [outputAt, stateAt, Matrix.mulVec_zero]
      -- By observability, x = 0
      exact hObs x 0 (fun t => by
        have := hZero t
        simp only [UnobservableSubspace, Set.mem_setOf_eq] at hZero
        rw [hZero t, h0 t])
    · intro hx
      simp only [Set.mem_singleton_iff] at hx
      simp only [hx, UnobservableSubspace, Set.mem_setOf_eq,
                 outputAt, stateAt, Matrix.mulVec_zero]
      intro _; trivial
  · -- Unobservable subspace is {0} → Observable
    intro hTriv x₀ x₀' hSame
    -- x₀ - x₀' is in the unobservable subspace by linearity
    have hDiff : x₀ - x₀' ∈ sys.UnobservableSubspace := by
      simp only [UnobservableSubspace, Set.mem_setOf_eq]
      intro t
      -- Use linearity of output
      simp only [outputAt, stateAt, Matrix.mulVec_sub]
      have := hSame t
      simp only [outputAt, stateAt] at this
      simp [this]
    -- By triviality of unobservable subspace
    rw [hTriv] at hDiff
    simp only [Set.mem_singleton_iff, sub_eq_zero] at hDiff
    exact hDiff

/-! ## The Observability Matrix

The classical Kalman observability matrix:
  𝒪 = [C; CA; CA²; ...; CA^{n-1}]

This is an (n·m) × n matrix formed by stacking C, CA, CA², etc.
-/

/--
  The k-th block of the observability matrix: C A^k
-/
def observabilityBlock (k : ℕ) : Matrix (Fin m) (Fin n) 𝕜 :=
  sys.C * sys.A ^ k

/--
  **Observability Matrix** (as a function from row index to value)

  For a proper matrix formulation, we'd need to define the stacked matrix.
  Here we characterize it by its action: 𝒪 x = [Cx; CAx; ...; CA^{n-1}x]
-/
def observabilityAction (x : Fin n → 𝕜) : Fin n → (Fin m → 𝕜) :=
  fun k => (sys.observabilityBlock k).mulVec x

/-! ## The Kalman Observability Theorem

This is a fundamental result in control theory. We state it as a theorem
with a proof sketch.

**Reference**:
R.E. Kalman. "Mathematical Description of Linear Dynamical Systems."
SIAM J. Control, 1(2):152-192, 1963. Theorem 6.
-/

/--
  **Kalman Observability Theorem**

  A linear system (A, C) is observable if and only if the observability
  action x ↦ (Cx, CAx, ..., CA^{n-1}x) is injective.

  **Proof sketch**:
  (→) If observable, then x ↦ output sequence is injective.
      The observability action IS the output sequence for t = 0, ..., n-1.
      Hence injective.

  (←) If observability action is injective, then distinct initial states
      give distinct first n outputs. Hence observable.

  **Full proof**: See Kalman (1963), Theorem 6.
-/
theorem kalman_observability_theorem :
    sys.IsObservable ↔ Function.Injective sys.observabilityAction := by
  constructor
  · intro hObs x x' hEq
    -- observabilityAction x = observabilityAction x'
    -- means ∀ k < n, C A^k x = C A^k x'
    -- which is exactly ∀ k < n, outputAt x k = outputAt x' k
    apply hObs
    intro t
    have := congr_fun hEq t
    simp only [observabilityAction, observabilityBlock, outputAt, stateAt,
               Matrix.mulVec_mulVec] at this ⊢
    exact this
  · intro hInj x x' hOutputs
    -- Outputs equal for t = 0, ..., n-1 means observabilityAction x = x'
    apply hInj
    funext k
    have := hOutputs k
    simp only [observabilityAction, observabilityBlock, outputAt, stateAt,
               Matrix.mulVec_mulVec] at this ⊢
    exact this

/-! ## Connection to Pseudorandomness Framework

Now we connect to the observer barrier framework.

**Key Insight**: An "output observer" is a linear functional on state space
that can be computed from the output sequence.

A state x is "pseudorandom to output observers" if it cannot be distinguished
from the zero state (or any other state) using only output observations.
-/

/--
  **OutputObserver**: A linear functional that can be computed from
  the first n outputs.

  Concretely: a linear combination of y₀, y₁, ..., y_{n-1}.
-/
structure OutputObserver (sys : LinearSystem 𝕜 n m) where
  /-- Coefficients for each time step -/
  coeffs : Fin n → (Fin m → 𝕜)

namespace OutputObserver

/--
  Apply the observer to an initial state.
  Result = Σ_{t < n} ⟨coeffs_t, y_t⟩
-/
def observe (obs : OutputObserver sys) (x₀ : Fin n → 𝕜) : 𝕜 :=
  ∑ t : Fin n, ∑ i : Fin m, obs.coeffs t i * sys.outputAt x₀ t i

/--
  The class of all output observers for a system.
-/
def OutputObserverClass (sys : LinearSystem 𝕜 n m) : Set (OutputObserver sys) :=
  Set.univ

end OutputObserver

/--
  Apply an output observer to a state.
  Result = Σ_{t < n} ⟨coeffs_t, y_t⟩
-/
def applyObserver (obs : OutputObserver sys) (x₀ : Fin n → 𝕜) : 𝕜 :=
  ∑ t : Fin n, ∑ i : Fin m, obs.coeffs t i * sys.outputAt x₀ t i

/--
  **Pseudorandom to Output Observers**

  A state x is pseudorandom to output observers if no output observer
  can distinguish it from the zero state.

  In the Boolean setting, this would be |obs(x) - E[obs]| < ε.
  For linear systems over fields, we simplify to: obs(x) = obs(0) for all obs.
-/
def IsPseudorandomToOutputs (x : Fin n → 𝕜) : Prop :=
  ∀ obs : OutputObserver sys, sys.applyObserver obs x = sys.applyObserver obs 0

/--
  Observer that extracts the (t, i) component of the output.
  coeffs t' i' = 1 if t' = t and i' = i, else 0.
-/
def componentObserver (t : Fin n) (i : Fin m) : OutputObserver sys where
  coeffs := fun t' i' => if t' = t ∧ i' = i then 1 else 0

theorem componentObserver_extracts (t : Fin n) (i : Fin m) (x₀ : Fin n → 𝕜) :
    sys.applyObserver (sys.componentObserver t i) x₀ = sys.outputAt x₀ t i := by
  simp only [applyObserver, componentObserver]
  -- Sum collapses to single term where t' = t and i' = i
  rw [Finset.sum_eq_single t, Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    simp [hi']
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · intro t' _ ht'
    apply Finset.sum_eq_zero
    intro i' _
    simp [ht']
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/--
  Pseudorandom to outputs iff in the unobservable subspace.

  **Proof**:
  (→) If pseudorandom, no observer distinguishes x from 0.
      The componentObserver extracts each output component.
      Hence all outputs must be 0, so x is in the unobservable subspace.

  (←) If x is unobservable, all outputs are 0, so any linear combination
      of outputs is also 0, hence x is indistinguishable from 0.
-/
theorem pseudorandom_iff_unobservable (x : Fin n → 𝕜) :
    sys.IsPseudorandomToOutputs x ↔ x ∈ sys.UnobservableSubspace := by
  constructor
  · -- Pseudorandom → Unobservable
    intro hPR
    simp only [UnobservableSubspace, Set.mem_setOf_eq]
    intro t
    ext i
    -- Use the component observer to extract (t, i)
    have hObs := hPR (sys.componentObserver t i)
    rw [componentObserver_extracts, componentObserver_extracts] at hObs
    -- outputAt 0 t i = 0
    simp only [outputAt, stateAt, Matrix.mulVec_zero, Pi.zero_apply] at hObs
    exact hObs
  · -- Unobservable → Pseudorandom
    intro hUnobs
    simp only [IsPseudorandomToOutputs, applyObserver]
    intro obs
    simp only [UnobservableSubspace, Set.mem_setOf_eq] at hUnobs
    -- All outputs of x are 0
    have hZero : ∀ t : Fin n, sys.outputAt x t = 0 := hUnobs
    -- Output of 0 is also 0
    have h0 : ∀ t : Fin n, sys.outputAt 0 t = 0 := by
      intro t
      simp [outputAt, stateAt, Matrix.mulVec_zero]
    -- Both sums reduce to 0
    simp only [hZero, h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-! ## THE BRIDGE THEOREM

This is the main result connecting control theory to the pseudorandomness framework.
-/

/--
  **CONTROL THEORY BRIDGE THEOREM**

  A linear system is observable if and only if no non-zero state is
  pseudorandom to output observers.

  **Interpretation**:
  - Observable = every state can be distinguished from zero by some output observer
  - Not observable = some non-zero state is "pseudorandom" (invisible to outputs)

  This shows that classical observability IS the statement:
  "states are not pseudorandom to the output observer class."

  **Proof**: Follows from the equivalences:
  - Observable ↔ UnobservableSubspace = {0}  (proved above)
  - Pseudorandom ↔ in UnobservableSubspace   (proved above)
-/
theorem observability_bridge :
    sys.IsObservable ↔ ∀ x : Fin n → 𝕜, sys.IsPseudorandomToOutputs x → x = 0 := by
  constructor
  · -- Observable → no non-zero pseudorandom states
    intro hObs x hPR
    -- By pseudorandom_iff_unobservable, x is in the unobservable subspace
    have hUnobs := (pseudorandom_iff_unobservable sys x).mp hPR
    -- By observable_iff_trivial_unobservable, this subspace is {0}
    have hTriv := (observable_iff_trivial_unobservable sys).mp hObs
    rw [hTriv] at hUnobs
    exact Set.mem_singleton_iff.mp hUnobs
  · -- No non-zero pseudorandom states → Observable
    intro hNoPR
    rw [observable_iff_trivial_unobservable sys]
    ext x
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hUnobs
      -- x is unobservable, hence pseudorandom
      have hPR := (pseudorandom_iff_unobservable sys x).mpr hUnobs
      exact hNoPR x hPR
    · intro hZero
      -- 0 is trivially in the unobservable subspace
      simp only [hZero, UnobservableSubspace, Set.mem_setOf_eq]
      intro t
      simp only [outputAt, stateAt, Matrix.mulVec_zero]

/--
  **Corollary: Unobservable Systems Have Pseudorandom States**

  If a system is NOT observable, there exists a non-zero state that is
  pseudorandom to all output observers.
-/
theorem not_observable_has_pseudorandom :
    ¬sys.IsObservable ↔ ∃ x : Fin n → 𝕜, x ≠ 0 ∧ sys.IsPseudorandomToOutputs x := by
  rw [observability_bridge]
  push_neg
  constructor
  · intro ⟨x, hPR, hNZ⟩
    exact ⟨x, hNZ, hPR⟩
  · intro ⟨x, hNZ, hPR⟩
    exact ⟨x, hPR, hNZ⟩

end LinearSystem

/-! ## Summary

We have established:

1. **LinearSystem**: Discrete-time LTI systems (A, C)
2. **IsObservable**: Standard control-theoretic observability
3. **OutputObserver**: Linear functionals on output sequences
4. **IsPseudorandomToOutputs**: State indistinguishable from zero by outputs
5. **observability_bridge**: Observable ↔ no non-zero pseudorandom states

**The Unifying Insight**:

The classical Kalman observability condition (rank of observability matrix)
is EXACTLY the statement that no state is pseudorandom to the output
observer class.

This parallels the complexity barriers:
- Relativization: functions pseudorandom to query observers block proofs
- Algebrization: functions pseudorandom to degree observers block proofs
- Natural proofs: functions pseudorandom to poly-time observers block proofs
- **Observability**: states NOT pseudorandom to output observers enable identification

| Domain | Observer Class | Pseudorandom Object | Consequence |
|--------|---------------|---------------------|-------------|
| Complexity | Query/Degree/PolyTime | Hard function | Cannot prove separation |
| Control | Output observers | Unobservable state | Cannot identify state |

The mathematics is identical: bounded observers cannot detect structure
in pseudorandom objects.

**Reference**:
R.E. Kalman. "Mathematical Description of Linear Dynamical Systems."
SIAM J. Control, 1(2):152-192, 1963.
-/

end ControlTheory
