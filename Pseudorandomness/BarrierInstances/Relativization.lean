/-
  Relativization Barrier - Derived from Observer Barrier
  ========================================================

  This module derives the relativization barrier as a DIRECT COROLLARY
  of the general observer barrier theorem. No additional axioms needed.

  **The Relativization Barrier (Baker-Gill-Solovay, 1975)**:
  There exist oracles A, B such that P^A = NP^A but P^B ≠ NP^B.
  This means any proof that only uses oracle queries cannot
  resolve P vs NP.

  **As Observer Barrier**:
  The relativization barrier IS the observer barrier instantiated to
  QueryBoundedObservers. The BGS theorem establishes that query-pseudorandom
  functions exist; our theorem shows this implies the barrier.

  **Reference**:
  T. Baker, J. Gill, R. Solovay.
  "Relativizations of the P =? NP Question"
  SIAM Journal on Computing, 4(4):431-442, 1975.
  DOI: 10.1137/0204037
-/

import Pseudorandomness.Core.ObserverBarrier
import Pseudorandomness.ObserverClasses.QueryBounded

namespace Pseudorandomness

/-! ## Relativization Barrier - Direct Corollary of Observer Barrier

The relativization barrier requires NO additional axioms. It is simply
the observer barrier theorem instantiated to QueryBoundedObservers.

**What BGS (1975) establishes**: Query-pseudorandom functions exist.
**What we prove here**: IF such functions exist, THEN the barrier holds.

The combination gives the full relativization barrier.
-/

/--
  **Definition**: A proof technique is relativizing if its observer
  class is contained in some query-bounded class.
-/
def ProofTechnique.IsRelativizing {n : ℕ} (T : ProofTechnique n) : Prop :=
  ∃ q, T.isOBounded (QueryBoundedObservers n q)

/--
  **RELATIVIZATION BARRIER (Direct Corollary of Observer Barrier)**

  IF there exists a function pseudorandom to q-query observers,
  THEN no q-query-bounded technique can distinguish it.

  This is the observer_barrier theorem with O = QueryBoundedObservers.
  No additional axioms - pure instantiation.
-/
theorem relativization_barrier {n : ℕ} (q : ℕ)
    (f : BoolFun n) (hPR : IsPseudorandomTo f (QueryBoundedObservers n q)) :
    ∀ T : ProofTechnique n, T.isOBounded (QueryBoundedObservers n q) →
    ¬(T.certifiesSeparation ∧
      ∃ obs ∈ T.observerClass, |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound) :=
  observer_barrier (QueryBoundedObservers n q) f hPR

/--
  **Relativization Barrier (Universal Form)**

  IF for every q there exists a function pseudorandom to q-query observers,
  THEN every relativizing technique is blocked by some function.

  Note: This requires pseudorandomness for ALL query bounds, not just one.
-/
theorem relativization_barrier_universal {n : ℕ}
    (hPR : ∀ q, ∃ f : BoolFun n, IsPseudorandomTo f (QueryBoundedObservers n q)) :
    ∀ T : ProofTechnique n, T.IsRelativizing →
      ∃ f : BoolFun n, ¬(T.certifiesSeparation ∧ ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  intro T ⟨q, hBounded⟩
  obtain ⟨f, hPRf⟩ := hPR q
  use f
  intro ⟨_, obs, hObs, hDist⟩
  have hSmall := hPRf obs (hBounded hObs)
  exact absurd hSmall (not_lt.mpr hDist)

/--
  **Relativization Barrier (Conditional on Specific q)**

  The clean form: for a specific q, if f is PR to QueryBounded(q),
  then any technique bounded by QueryBounded(q) cannot distinguish f.
-/
theorem relativization_barrier_at_q {n q : ℕ}
    (f : BoolFun n) (hPR : IsPseudorandomTo f (QueryBoundedObservers n q))
    (T : ProofTechnique n) (hBounded : T.isOBounded (QueryBoundedObservers n q)) :
    ¬(T.certifiesSeparation ∧ ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  intro ⟨_, obs, hObs, hDist⟩
  have hSmall := hPR obs (hBounded hObs)
  exact absurd hSmall (not_lt.mpr hDist)

/--
  **What the relativization barrier says**:

  For any query bound q:
    (∃ f pseudorandom to q-query) → (q-query techniques blocked on f)

  This is a THEOREM, not dependent on any axiom.
  The BGS paper establishes the antecedent; we prove the implication.
-/
theorem relativization_barrier_implication (n q : ℕ) :
    (∃ f : BoolFun n, IsPseudorandomTo f (QueryBoundedObservers n q)) →
    (∃ f : BoolFun n, ∀ T : ProofTechnique n, T.isOBounded (QueryBoundedObservers n q) →
      ∀ obs ∈ T.observerClass, ¬Distinguishes obs f) := by
  intro ⟨f, hPR⟩
  use f
  intro T hBounded obs hObs hDist
  have hSmall := hPR obs (hBounded hObs)
  exact absurd hSmall (not_lt.mpr hDist)

end Pseudorandomness
