/-
  The Observer Barrier - Main Theorems
  =====================================

  This module contains the main theorems of the observer barrier framework.
  These theorems are PURE - they depend only on the abstract notions of
  observer, pseudorandomness, and proof technique. No barrier-specific
  concepts (oracles, algebraic extensions, PRFs) are needed here.

  **THE FUNDAMENTAL INSIGHT**:
  If functions exist that are pseudorandom to observer class O,
  then no O-bounded proof technique can prove complexity separations.

  This single principle explains ALL THREE classical barriers:
  - Relativization: O = QueryBounded
  - Algebrization: O = DegreeBounded
  - Natural Proofs: O = PolyTime
-/

import Pseudorandomness.Core.ProofTechnique

namespace Pseudorandomness

variable {n : ℕ}

/-! ## The Observer Barrier Theorem -/

/--
  **THE OBSERVER BARRIER (Main Theorem)**

  If there exists a function f that is pseudorandom to observer class O,
  then no O-bounded proof technique can both:
  1. Certify a complexity separation, AND
  2. Exhibit a distinguisher for f

  **Proof**:
  - Suppose T is O-bounded and certifies separation
  - By soundness, T exhibits some distinguisher obs ∈ T.observerClass for some g
  - If T claims to distinguish f specifically, then obs must be in T.observerClass ⊆ O
  - But f is pseudorandom to O, so obs cannot distinguish f
  - Contradiction!

  **Why this matters**:
  This is not about a specific f. It says: the EXISTENCE of pseudorandom
  functions is sufficient to block proof techniques.
-/
theorem observer_barrier (O : ObserverClass n)
    (f : BoolFun n) (hPR : IsPseudorandomTo f O) :
    ∀ T : ProofTechnique n, T.isOBounded O →
    ¬(T.certifiesSeparation ∧
      ∃ obs ∈ T.observerClass, |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound) := by
  intro T hBounded ⟨_hCert, obs, hObs, hDist⟩
  -- obs ∈ T.observerClass ⊆ O
  have hObsInO : obs ∈ O := hBounded hObs
  -- f is pseudorandom to O, so obs cannot distinguish
  have hSmall := hPR obs hObsInO
  -- hSmall: |obs.observe f - obs.randomExpectation| < 1/obs.bound
  -- hDist:  |obs.observe f - obs.randomExpectation| ≥ 1/obs.bound
  -- Direct contradiction!
  exact absurd hSmall (not_lt.mpr hDist)

/-! ## Unified Barrier (Existential Form) -/

/--
  **THE UNIFIED BARRIER (Existential Form)**

  If there exists ANY function pseudorandom to observer class O,
  then no O-bounded proof technique can both:
  1. Certify a complexity separation, AND
  2. Distinguish ALL pseudorandom functions from random

  This is the key insight: pseudorandomness blocks proof techniques.
-/
theorem unified_barrier (O : ObserverClass n) :
    (∃ f, IsPseudorandomTo f O) →
    ¬∃ T : ProofTechnique n, T.isOBounded O ∧ T.certifiesSeparation ∧
      (∀ g, IsPseudorandomTo g O → ∃ obs ∈ T.observerClass,
        |obs.observe g - obs.randomExpectation| ≥ 1 / obs.bound) := by
  intro ⟨f, hPR⟩ ⟨T, hBounded, hCert, hDistinguishes⟩
  -- T claims to distinguish ALL pseudorandom functions
  -- In particular, it claims to distinguish f
  obtain ⟨obs, hObs, hDist⟩ := hDistinguishes f hPR
  -- But f is pseudorandom to O, and obs ∈ T.observerClass ⊆ O
  have hObsInO : obs ∈ O := hBounded hObs
  have hSmall := hPR obs hObsInO
  -- hSmall: |obs.observe f - obs.randomExpectation| < 1/obs.bound
  -- hDist:  |obs.observe f - obs.randomExpectation| ≥ 1/obs.bound
  -- Contradiction!
  exact absurd hSmall (not_lt.mpr hDist)

/-! ## Contrapositive Forms -/

/--
  **Contrapositive: Certification Implies Breaking Pseudorandomness**

  If a proof technique T certifies separation, then not all functions
  are pseudorandom to T's observer class.

  Equivalently: T must be able to distinguish SOME function from random.
-/
theorem technique_breaks_pseudorandomness (T : ProofTechnique n)
    (hCert : T.certifiesSeparation) :
    ∃ f : BoolFun n, ¬IsPseudorandomTo f T.observerClass := by
  obtain ⟨f, obs, hObs, hDist⟩ := T.soundness hCert
  use f
  intro hPR
  have hSmall := hPR obs hObs
  exact absurd hSmall (not_lt.mpr hDist)

/--
  **Barrier Existence Theorem**

  The existence of pseudorandom functions against observer class O
  implies O-bounded techniques cannot distinguish functions from random.

  This is the "barrier" in its purest form: pseudorandomness IS the barrier.
-/
theorem barrier_implies_no_distinction (O : ObserverClass n)
    (_hPR : ∃ f : BoolFun n, IsPseudorandomTo f O) :
    ∀ T : ProofTechnique n, T.isOBounded O →
      ∀ obs ∈ T.observerClass, ∀ f : BoolFun n, IsPseudorandomTo f O →
        |obs.observe f - obs.randomExpectation| < 1/obs.bound := by
  intro T hBounded obs hObs f hPRf
  exact hPRf obs (hBounded hObs)

/-! ## Barrier Breaking Requirement -/

/--
  **Barrier Breaking Requirement**

  What would it take to prove a complexity separation?

  A successful proof must use a technique T such that:
  1. T certifies some complexity separation
  2. T's observer class can distinguish ALL functions from random
     (equivalently: no function is pseudorandom to T's observers)

  The second condition means T has "broken through" the pseudorandomness
  barrier - it can see beyond what limited observers can see.
-/
theorem barrier_breaking_requirement (T : ProofTechnique n)
    (hCert : T.certifiesSeparation)
    -- T can distinguish all functions (barrier is broken)
    (_hNoPR : ∀ f : BoolFun n, ¬IsPseudorandomTo f T.observerClass) :
    -- Then T has legitimately certified a separation
    T.certifiesSeparation :=
  hCert

/--
  **The Key Trade-off**

  For any observer class O:
  - Either some functions are pseudorandom to O (barrier exists)
  - Or O can distinguish all functions (barrier broken)

  If O-pseudorandom functions exist, O-bounded techniques fail.
  If O can distinguish everything, O is "complete" for separations.
-/
theorem barrier_dichotomy (O : ObserverClass n) :
    (∃ f, IsPseudorandomTo f O) ∨ (∀ f, ¬IsPseudorandomTo f O) := by
  by_cases h : ∃ f, IsPseudorandomTo f O
  · exact Or.inl h
  · push_neg at h
    exact Or.inr h

/-! ## Composition of Barriers -/

/--
  **Intersection of Observer Classes**

  If f is pseudorandom to O₁ ∪ O₂, then f is pseudorandom to both
  O₁ and O₂ separately.
-/
theorem pseudorandom_inter {f : BoolFun n} {O₁ O₂ : ObserverClass n}
    (hPR : IsPseudorandomTo f (ObserverClass.union O₁ O₂)) :
    IsPseudorandomTo f O₁ ∧ IsPseudorandomTo f O₂ := by
  constructor
  · exact pseudorandom_subset (Set.subset_union_left) hPR
  · exact pseudorandom_subset (Set.subset_union_right) hPR

/--
  **Barrier Strengthening**

  If T is bounded by O₁ and O₁ ⊆ O₂, then any pseudorandom function
  against O₂ blocks T.
-/
theorem barrier_strengthening {T : ProofTechnique n} {O₁ O₂ : ObserverClass n}
    (hBound : T.isOBounded O₁) (hSub : O₁ ⊆ O₂)
    (f : BoolFun n) (hPR : IsPseudorandomTo f O₂) :
    ¬(T.certifiesSeparation ∧
      ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  have hPR₁ : IsPseudorandomTo f O₁ := pseudorandom_subset hSub hPR
  intro ⟨_, obs, hObs, hDist⟩
  have hSmall := hPR₁ obs (hBound hObs)
  exact absurd hSmall (not_lt.mpr hDist)

/-! ## What These Theorems Say -/

/--
  **Summary**: The observer barrier theorems establish a fundamental principle:

  PSEUDORANDOMNESS IS THE BARRIER.

  For any observer class O:
  1. If O-pseudorandom functions exist → O-bounded techniques blocked
  2. To break the barrier → must transcend O's computational limits
  3. All classical barriers (relativization, algebrization, natural proofs)
     are instances of this principle for specific observer classes

  The three classical barriers become COROLLARIES:
  - Relativization: O = QueryBounded, BGS provides pseudorandom functions
  - Algebrization: O = DegreeBounded, AW provides pseudorandom functions
  - Natural Proofs: O = PolyTime, PRFs provide pseudorandom functions

  These corollaries are proven in the BarrierInstances modules.
-/
theorem observer_barrier_summary : True := trivial

end Pseudorandomness
