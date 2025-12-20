/-
  Algebrization Barrier - Derived from Observer Barrier
  =======================================================

  This module derives the algebrization barrier as a DIRECT COROLLARY
  of the general observer barrier theorem. No additional axioms needed.

  **The Algebrization Barrier (Aaronson-Wigderson, 2009)**:
  Even if we extend oracles to their low-degree algebraic extensions,
  there exist "algebrizing" oracles for both P = NP and P ≠ NP.
  This means techniques that only use low-degree polynomial queries
  cannot resolve P vs NP.

  **As Observer Barrier**:
  The algebrization barrier IS the observer barrier instantiated to
  DegreeBoundedObservers. The AW theorem establishes that degree-pseudorandom
  functions exist; our theorem shows this implies the barrier.

  **Reference**:
  S. Aaronson, A. Wigderson.
  "Algebrization: A New Barrier in Complexity Theory"
  ACM Transactions on Computation Theory, 1(1):2, 2009.
  DOI: 10.1145/1490270.1490272
-/

import Pseudorandomness.Core.ObserverBarrier
import Pseudorandomness.ObserverClasses.Hierarchy
import Pseudorandomness.BarrierInstances.Relativization

namespace Pseudorandomness

/-! ## Algebrization Barrier - Direct Corollary of Observer Barrier

The algebrization barrier requires NO additional axioms. It is simply
the observer barrier theorem instantiated to DegreeBoundedObservers.

**What AW (2009) establishes**: Degree-pseudorandom functions exist.
**What we prove here**: IF such functions exist, THEN the barrier holds.

The combination gives the full algebrization barrier.
-/

/--
  **Definition**: A proof technique is algebrizing if its observer
  class is contained in some degree-bounded class.
-/
def ProofTechnique.IsAlgebrizing {n : ℕ} (T : ProofTechnique n) : Prop :=
  ∃ d, T.isOBounded (DegreeBoundedObservers n d)

/--
  **ALGEBRIZATION BARRIER (Direct Corollary of Observer Barrier)**

  IF there exists a function pseudorandom to degree-d observers,
  THEN no degree-d-bounded technique can distinguish it.

  This is the observer_barrier theorem with O = DegreeBoundedObservers.
  No additional axioms - pure instantiation.
-/
theorem algebrization_barrier {n : ℕ} (d : ℕ)
    (f : BoolFun n) (hPR : IsPseudorandomTo f (DegreeBoundedObservers n d)) :
    ∀ T : ProofTechnique n, T.isOBounded (DegreeBoundedObservers n d) →
    ¬(T.certifiesSeparation ∧
      ∃ obs ∈ T.observerClass, |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound) :=
  observer_barrier (DegreeBoundedObservers n d) f hPR

/--
  **Algebrization Barrier (Universal Form)**

  IF for every d there exists a function pseudorandom to degree-d observers,
  THEN every algebrizing technique is blocked by some function.
-/
theorem algebrization_barrier_universal {n : ℕ}
    (hPR : ∀ d, ∃ f : BoolFun n, IsPseudorandomTo f (DegreeBoundedObservers n d)) :
    ∀ T : ProofTechnique n, T.IsAlgebrizing →
      ∃ f : BoolFun n, ¬(T.certifiesSeparation ∧ ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  intro T ⟨d, hBounded⟩
  obtain ⟨f, hPRf⟩ := hPR d
  use f
  intro ⟨_, obs, hObs, hDist⟩
  have hSmall := hPRf obs (hBounded hObs)
  exact absurd hSmall (not_lt.mpr hDist)

/--
  **Algebrization Barrier (Conditional on Specific d)**

  The clean form: for a specific d, if f is PR to DegreeBounded(d),
  then any technique bounded by DegreeBounded(d) cannot distinguish f.
-/
theorem algebrization_barrier_at_d {n d : ℕ}
    (f : BoolFun n) (hPR : IsPseudorandomTo f (DegreeBoundedObservers n d))
    (T : ProofTechnique n) (hBounded : T.isOBounded (DegreeBoundedObservers n d)) :
    ¬(T.certifiesSeparation ∧ ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  intro ⟨_, obs, hObs, hDist⟩
  have hSmall := hPR obs (hBounded hObs)
  exact absurd hSmall (not_lt.mpr hDist)

/--
  **What the algebrization barrier says**:

  For any degree bound d:
    (∃ f pseudorandom to degree-d) → (degree-d techniques blocked on f)

  This is a THEOREM, not dependent on any axiom.
  The AW paper establishes the antecedent; we prove the implication.
-/
theorem algebrization_barrier_implication (n d : ℕ) :
    (∃ f : BoolFun n, IsPseudorandomTo f (DegreeBoundedObservers n d)) →
    (∃ f : BoolFun n, ∀ T : ProofTechnique n, T.isOBounded (DegreeBoundedObservers n d) →
      ∀ obs ∈ T.observerClass, ¬Distinguishes obs f) := by
  intro ⟨f, hPR⟩
  use f
  intro T hBounded obs hObs hDist
  have hSmall := hPR obs (hBounded hObs)
  exact absurd hSmall (not_lt.mpr hDist)

/-! ## Relationship to Relativization -/

/--
  **Algebrization strictly extends relativization**

  Every relativizing technique is also algebrizing.
  (Query complexity ≤ algebraic degree in natural encodings)

  Note: Uses `query_subset_degree` which gives QueryBounded(q) ⊆ DegreeBounded(q+1).
-/
theorem relativizing_implies_algebrizing {n : ℕ} (T : ProofTechnique n)
    (hRel : T.IsRelativizing) : T.IsAlgebrizing := by
  obtain ⟨q, hBounded⟩ := hRel
  use q + 1
  exact ProofTechnique.isOBounded_trans hBounded (query_subset_degree n q)

end Pseudorandomness
