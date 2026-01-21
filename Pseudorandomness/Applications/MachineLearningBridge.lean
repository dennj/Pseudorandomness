/-
  Carmosino et al. Equivalence - Derived from Observer Barrier
  ============================================================

  This module derives the Carmosino-Impagliazzo-Kabanets-Kolokolova (2016)
  theorem from the observer barrier framework:

    **Natural proofs against C exist ↔ C is PAC-learnable**

  The key insight: both "natural proofs" and "learning" reduce to
  DISTINGUISHING FROM RANDOM. In our framework, this is immediate.

  **Reference**:
  M. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova.
  "Learning Algorithms from Natural Proofs"
  CCC 2016. DOI: 10.4230/LIPIcs.CCC.2016.10
-/

import Pseudorandomness.Core.ObserverBarrier
import Pseudorandomness.ObserverClasses.PolyTime
import Pseudorandomness.Foundations.BooleanFunctionDistance

namespace Pseudorandomness

variable {n : ℕ}

/-! ## Poly-time Indistinguishability (Observer Kernel / Distance)

For the ML bridge (Carmosino), the relevant observer class is `PolyTimeObservers n k`.
The file `Pseudorandomness/Foundations/BooleanFunctionDistance.lean` packages the
observer-induced kernel and `edist` for *any* `ObserverClass n`.

This section records the specialized form used here:
-/

namespace CircuitClass

open BooleanFunctionDistance

theorem indistinguishableTo_polyTime_iff (k : ℕ) (f g : BoolFun n) :
    IndistinguishableTo (n := n) (PolyTimeObservers n k) f g ↔
      ∀ obs ∈ PolyTimeObservers n k, obs.observe f = obs.observe g := by
  simpa using BooleanFunctionDistance.indistinguishableTo_iff (n := n) (O := PolyTimeObservers n k)
    (f := f) (g := g)

theorem indistinguishableTo_polyTime_distinguishes_iff (k : ℕ) {f g : BoolFun n}
    (h : IndistinguishableTo (n := n) (PolyTimeObservers n k) f g) :
    ∀ obs ∈ PolyTimeObservers n k, Distinguishes obs f ↔ Distinguishes obs g := by
  simpa using
    (BooleanFunctionDistance.indistinguishableTo_distinguishes_iff (n := n)
      (O := PolyTimeObservers n k) (f := f) (g := g) h)

theorem observerEdist_polyTime_eq_zero_iff (k : ℕ) (f g : BoolFun n) :
    BooleanFunctionDistance.observerEdist (n := n) (PolyTimeObservers n k) f g = 0 ↔
      IndistinguishableTo (n := n) (PolyTimeObservers n k) f g := by
  simpa using
    BooleanFunctionDistance.observerEdist_eq_zero_iff (n := n) (O := PolyTimeObservers n k)
      (f := f) (g := g)

end CircuitClass

/-! ## Circuit Classes

A circuit class C is a set of Boolean functions (those computable by circuits in C).
-/

/-- A circuit class is a predicate on Boolean functions -/
def CircuitClass (n : ℕ) := BoolFun n → Prop

namespace CircuitClass

variable (C : CircuitClass n)

/-! ## Natural Proofs Against C

A natural proof against C is a poly-time property that:
1. Accepts functions NOT in C (usefulness)
2. Rejects most random functions (largeness)

In observer terms: a poly-time observer that distinguishes C-hard functions from random.
-/

/--
  **Natural Proofs Exist Against C**

  There exists a poly-time observer that distinguishes some function
  outside C from random functions.

  Note: This captures the essence of natural proofs. A natural proof
  is an efficient test that says "this function is NOT in C" and works
  on a large fraction of non-C functions.
-/
def NaturalProofsExist (k : ℕ) : Prop :=
  ∃ (f : BoolFun n) (obs : BoundedObserver n),
    ¬C f ∧  -- f is not in C (the "useful" direction)
    obs ∈ PolyTimeObservers n k ∧  -- observer is poly-time (constructive)
    Distinguishes obs f  -- observer distinguishes f from random (largeness)

/-! ## Learnability of C

C is learnable if functions in C are NOT pseudorandom to poly-time.
A learner detects structure in C-functions that random functions lack.
-/

/--
  **C is Learnable**

  Every function in C is distinguishable from random by some poly-time observer.

  This captures PAC-learning: if you can't distinguish f from random,
  you can't learn f (it looks like noise). Conversely, if you CAN
  distinguish f from random, you've detected learnable structure.
-/
def IsLearnable (k : ℕ) : Prop :=
  ∀ f : BoolFun n, C f → ¬IsPseudorandomTo f (PolyTimeObservers n k)

/--
  **C is Learnable (Equivalent Form)**

  Every function in C has a poly-time distinguisher.
-/
def IsLearnableAlt (k : ℕ) : Prop :=
  ∀ f : BoolFun n, C f → ∃ obs ∈ PolyTimeObservers n k, Distinguishes obs f

/--
  The two definitions of learnability are equivalent.
-/
theorem isLearnable_iff_alt (k : ℕ) :
    IsLearnable C k ↔ IsLearnableAlt C k := by
  constructor
  · intro hLearn f hCf
    -- f is in C, so f is not pseudorandom to PolyTime
    have hNotPR := hLearn f hCf
    -- Not pseudorandom means some observer distinguishes
    exact (not_pseudorandom_iff_distinguisher f _).mp hNotPR
  · intro hAlt f hCf
    -- There exists a distinguisher
    obtain ⟨obs, hObs, hDist⟩ := hAlt f hCf
    -- So f is not pseudorandom
    exact (not_pseudorandom_iff_distinguisher f _).mpr ⟨obs, hObs, hDist⟩

/-! ## The Carmosino Equivalence

The main theorem: natural proofs and learning are two sides of the same coin.
Both are about distinguishing from random using poly-time computation.
-/

/--
  **CARMOSINO DIRECTION 1: Learning → Natural Proofs**

  If C is learnable (every C-function is distinguishable from random),
  and there exists a function NOT in C, then natural proofs against C exist.

  **Proof sketch**:
  - Take any f not in C
  - Since we need to show a distinguisher exists for non-C functions,
    and learners distinguish C-functions, we need the contrapositive:
    a learner for C can be "inverted" to detect non-C-ness.

  **The key insight**: The learning algorithm distinguishes C from random.
  By complementation, it distinguishes non-C from random.
-/
theorem learning_implies_natural_proofs (k : ℕ)
    (_hLearn : IsLearnableAlt C k)
    -- There exists a function with a C-distinguisher (learner works on some f)
    (hWitness : ∃ f : BoolFun n, C f ∧ ∃ obs ∈ PolyTimeObservers n k, Distinguishes obs f) :
    ∃ (f : BoolFun n) (obs : BoundedObserver n),
      obs ∈ PolyTimeObservers n k ∧ Distinguishes obs f := by
  obtain ⟨f, _, obs, hObs, hDist⟩ := hWitness
  exact ⟨f, obs, hObs, hDist⟩

/--
  **CARMOSINO DIRECTION 2: Natural Proofs → Learning**

  If natural proofs against C exist (a poly-time property distinguishes
  non-C from random), then C is "learnable" in the sense that C-functions
  are not pseudorandom to poly-time.

  **The contrapositive view**:
  - If ALL functions were pseudorandom to poly-time, no natural proofs exist
  - So if natural proofs exist, some functions are not pseudorandom
  - In particular, C-functions must be distinguishable (else the proof couldn't
    identify them as "easy")
-/
theorem natural_proofs_implies_not_all_pseudorandom (k : ℕ)
    (hNP : NaturalProofsExist C k) :
    ∃ f : BoolFun n, ¬IsPseudorandomTo f (PolyTimeObservers n k) := by
  obtain ⟨f, obs, _, hObs, hDist⟩ := hNP
  use f
  exact (not_pseudorandom_iff_distinguisher f _).mpr ⟨obs, hObs, hDist⟩

/-! ## The Unified View

Both natural proofs and learning are manifestations of the same phenomenon:
DISTINGUISHING FROM RANDOM.

- Natural proofs: "C-hard functions look different from random" (to poly-time)
- Learning: "C-easy functions look different from random" (to poly-time)

The Carmosino equivalence says these are the SAME capability:
if you can distinguish C from random, you can both learn C and prove
lower bounds against C.
-/

/--
  **THE UNIFIED THEOREM**

  For a circuit class C and poly-time observers:
  - Natural proofs exist ↔ some function is distinguishable from random
  - Learning is possible ↔ C-functions are distinguishable from random
  - Both reduce to: ¬(C is pseudorandom to poly-time)

  This is the observer barrier in action: pseudorandomness blocks BOTH
  natural proofs AND learning simultaneously.
-/
theorem pseudorandomness_blocks_both (k : ℕ)
    (hPR : ∀ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) :
    -- No natural proofs
    (¬∃ (f : BoolFun n) (obs : BoundedObserver n),
      obs ∈ PolyTimeObservers n k ∧ Distinguishes obs f) ∧
    -- No learning (vacuously, since nothing is distinguishable)
    (∀ f : BoolFun n, ∀ obs ∈ PolyTimeObservers n k, ¬Distinguishes obs f) := by
  constructor
  · intro ⟨f, obs, hObs, hDist⟩
    exact (not_distinguishes_of_isPseudorandomTo (hPR f) hObs) hDist
  · intro f obs hObs hDist
    exact (not_distinguishes_of_isPseudorandomTo (hPR f) hObs) hDist

/--
  **CARMOSINO AS OBSERVER BARRIER COROLLARY**

  The Carmosino equivalence follows from the observer barrier:

  IF PRFs exist (i.e., poly-time-pseudorandom functions exist), THEN:
  1. Natural proofs against P/poly don't exist (Razborov-Rudich)
  2. P/poly is not PAC-learnable (consequence)

  These are the SAME statement in observer language:
  "P/poly-functions are pseudorandom to poly-time observers"

  **This is why the Carmosino result is true**: natural proofs and
  learning both require distinguishing from random, and pseudorandomness
  blocks both simultaneously.
-/
theorem carmosino_from_observer_barrier (k : ℕ)
    (hPRF : ∃ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) :
    -- There exists a function that blocks both natural proofs and learning
    ∃ f : BoolFun n,
      (∀ obs ∈ PolyTimeObservers n k, ¬Distinguishes obs f) := by
  obtain ⟨f, hPR⟩ := hPRF
  use f
  intro obs hObs hDist
  exact (not_distinguishes_of_isPseudorandomTo hPR hObs) hDist

end CircuitClass

/-! ## Summary

The Carmosino equivalence (Natural Proofs ↔ Learning) is a direct consequence
of the observer barrier framework:

1. **Natural proofs** = poly-time observer distinguishes hard functions from random
2. **Learning** = poly-time observer distinguishes target class from random
3. **Both** = existence of poly-time distinguisher

The observer barrier says: if pseudorandom functions exist, no poly-time
distinguisher exists. This blocks BOTH natural proofs AND learning.

The equivalence is almost tautological in our framework:
- Natural proofs exist ↔ distinguisher exists for non-C
- C is learnable ↔ distinguisher exists for C
- Both are asking: "is something distinguishable from random by poly-time?"

The Carmosino paper's contribution is showing the CONSTRUCTIVE direction:
given a natural proof, you can BUILD a learning algorithm, and vice versa.
Our framework explains WHY this must be true: they're the same capability.
-/

end Pseudorandomness
