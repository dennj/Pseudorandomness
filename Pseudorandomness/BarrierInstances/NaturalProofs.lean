/-
  Natural Proofs Barrier - Derived from Observer Barrier
  ========================================================

  This module derives the natural proofs barrier as a DIRECT COROLLARY
  of the general observer barrier theorem. No additional axioms needed.

  **The Natural Proofs Barrier (Razborov-Rudich, 1997)**:
  IF one-way functions (or PRFs) exist, THEN "natural" proof techniques
  cannot prove circuit lower bounds against P/poly.

  A natural proof is one that:
  1. **Constructivity**: Can be checked in polynomial time
  2. **Largeness**: Applies to a large fraction of functions

  **As Observer Barrier**:
  The natural proofs barrier IS the observer barrier instantiated to
  PolyTimeObservers. The PRF assumption establishes that polytime-pseudorandom
  functions exist; our theorem shows this implies the barrier.

  **References**:
  A. Razborov, S. Rudich.
  "Natural Proofs"
  Journal of Computer and System Sciences, 55(1):24-35, 1997.
  DOI: 10.1006/jcss.1997.1494

  O. Goldreich, S. Goldwasser, S. Micali.
  "How to Construct Random Functions"
  Journal of the ACM, 33(4):792-807, 1986.
  DOI: 10.1145/6490.6503
-/

import Pseudorandomness.Core.ObserverBarrier
import Pseudorandomness.ObserverClasses.Hierarchy
import Pseudorandomness.BarrierInstances.Relativization
import Pseudorandomness.BarrierInstances.Algebrization

namespace Pseudorandomness

/-! ## Natural Proofs Barrier - Direct Corollary of Observer Barrier

The natural proofs barrier requires NO additional axioms. It is simply
the observer barrier theorem instantiated to PolyTimeObservers.

**What RR (1997) establishes**: IF PRFs exist, THEN polytime-pseudorandom functions exist.
**What we prove here**: IF such functions exist, THEN the barrier holds.

The combination (conditional on PRF existence) gives the full natural proofs barrier.
-/

/--
  **Definition**: A proof technique is natural if its observer
  class is contained in some poly-time(k) observers.

  This captures the Razborov-Rudich notion: a natural proof must
  be efficiently checkable (constructive) which means it uses
  only poly-time observations.
-/
def ProofTechnique.IsNatural {n : ℕ} (T : ProofTechnique n) : Prop :=
  ∃ k, T.isOBounded (PolyTimeObservers n k)

/--
  **NATURAL PROOFS BARRIER (Direct Corollary of Observer Barrier)**

  IF there exists a function pseudorandom to poly-time(k) observers,
  THEN no poly-time(k)-bounded technique can distinguish it.

  This is the observer_barrier theorem with O = PolyTimeObservers.
  No additional axioms - pure instantiation.
-/
theorem natural_proofs_barrier {n : ℕ} (k : ℕ)
    (f : BoolFun n) (hPR : IsPseudorandomTo f (PolyTimeObservers n k)) :
    ∀ T : ProofTechnique n, T.isOBounded (PolyTimeObservers n k) →
    ¬(T.certifiesSeparation ∧
      ∃ obs ∈ T.observerClass, |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound) :=
  observer_barrier (PolyTimeObservers n k) f hPR

/--
  **Natural Proofs Barrier (Universal Form)**

  IF for every k there exists a function pseudorandom to poly-time(k) observers,
  THEN every natural technique is blocked by some function.
-/
theorem natural_proofs_barrier_universal {n : ℕ}
    (hPR : ∀ k, ∃ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) :
    ∀ T : ProofTechnique n, T.IsNatural →
      ∃ f : BoolFun n, ¬(T.certifiesSeparation ∧ ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  intro T ⟨k, hBounded⟩
  obtain ⟨f, hPRf⟩ := hPR k
  use f
  exact observer_barrier_distinguisher (PolyTimeObservers n k) f hPRf T hBounded

/--
  **Natural Proofs Barrier (Conditional on Specific k)**

  The clean form: for a specific k, if f is PR to PolyTime(k),
  then any technique bounded by PolyTime(k) cannot distinguish f.
-/
theorem natural_proofs_barrier_at_k {n k : ℕ}
    (f : BoolFun n) (hPR : IsPseudorandomTo f (PolyTimeObservers n k))
    (T : ProofTechnique n) (hBounded : T.isOBounded (PolyTimeObservers n k)) :
  ¬(T.certifiesSeparation ∧ ∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  exact observer_barrier_distinguisher (PolyTimeObservers n k) f hPR T hBounded

/--
  **What the natural proofs barrier says**:

  For any polynomial exponent k:
    (∃ f pseudorandom to poly-time(k)) → (poly-time(k) techniques blocked on f)

  This is a THEOREM, not dependent on any axiom.
  The PRF assumption + GGM establishes the antecedent; we prove the implication.
-/
theorem natural_proofs_barrier_implication (n k : ℕ) :
    (∃ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) →
    (∃ f : BoolFun n, ∀ T : ProofTechnique n, T.isOBounded (PolyTimeObservers n k) →
      ∀ obs ∈ T.observerClass, ¬Distinguishes obs f) := by
  intro ⟨f, hPR⟩
  use f
  intro T hBounded obs hObs hDist
  exact (not_distinguishes_of_isPseudorandomTo hPR (hBounded hObs)) hDist

/-! ## Relationship to Other Barriers -/

-- Note: `relativizing_implies_natural` and `algebrizing_implies_natural`
-- are already proven in ObserverClasses/Hierarchy.lean

/--
  **The natural proofs barrier is the strongest**

  Since PolyTime ⊇ DegreeBounded ⊇ QueryBounded:
  - IF polytime-PR functions exist, THEN natural techniques blocked
  - IF natural techniques blocked, THEN algebrizing techniques blocked
  - IF algebrizing techniques blocked, THEN relativizing techniques blocked

  The converses don't hold in general.
-/
theorem natural_is_strongest_barrier {n : ℕ}
    (hPR : ∀ k, ∃ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) :
    -- Implies degree-PR exists
    (∀ d, ∃ f : BoolFun n, IsPseudorandomTo f (DegreeBoundedObservers n d)) ∧
    -- Implies query-PR exists
    (∀ q, ∃ f : BoolFun n, IsPseudorandomTo f (QueryBoundedObservers n q)) := by
  constructor
  · intro d
    obtain ⟨f, hPRf⟩ := hPR (d + 1)
    exact ⟨f, pseudorandom_subset (degree_subset_polytime n d) hPRf⟩
  · intro q
    obtain ⟨f, hPRf⟩ := hPR (q + 2)
    exact ⟨f, pseudorandom_subset (query_subset_polytime n q) hPRf⟩

/--
  **What natural proofs teaches us**:

  Most known lower bound proofs (diagonalization, counting, etc.)
  are "natural" in that they use efficiently checkable properties.
  IF PRFs exist, such techniques cannot prove super-polynomial
  circuit lower bounds.

  To prove P ≠ NP, we need techniques that are:
  - Non-constructive (cannot be checked in poly-time), OR
  - Non-large (apply to very few functions)

  This is a strong constraint on what a P ≠ NP proof must look like.
-/
theorem natural_proofs_lesson {n : ℕ}
    (hPR : ∀ k, ∃ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) :
    ∀ T : ProofTechnique n, T.IsNatural →
      ∃ f, ¬(∃ obs ∈ T.observerClass, Distinguishes obs f) := by
  intro T hNat
  obtain ⟨k, hBounded⟩ := hNat
  obtain ⟨f, hPRf⟩ := hPR k
  use f
  intro ⟨obs, hObs, hDist⟩
  exact (not_distinguishes_of_isPseudorandomTo hPRf (hBounded hObs)) hDist

end Pseudorandomness
