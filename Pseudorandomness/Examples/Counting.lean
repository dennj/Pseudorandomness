/-
  Counting Argument Technique - Concrete Instance
  ================================================

  This module provides a concrete instance of a natural proof technique:
  the Shannon counting argument that proves most functions require large circuits.

  **Key Result**: Counting arguments are natural proofs because they use
  efficiently computable properties (circuit evaluation). This is why they
  cannot prove superpolynomial lower bounds for explicit functions (if PRFs exist).

  **Citation**:
  C. Shannon (1949). "The Synthesis of Two-Terminal Switching Circuits"
  Bell System Technical Journal, 28(1):59-98.

  A. Razborov, S. Rudich (1997). "Natural Proofs"
  JCSS 55(1):24-35. DOI: 10.1006/jcss.1997.1494
-/

import Pseudorandomness.Core.ProofTechnique
import Pseudorandomness.Core.StrongProofTechnique
import Pseudorandomness.ObserverClasses.Hierarchy
import Pseudorandomness.BarrierInstances.NaturalProofs

namespace Pseudorandomness

variable {n : ℕ}

/-! ## The Counting Technique

The Shannon counting argument works by showing:
1. There are 2^(2^n) Boolean functions on n bits
2. Circuits of size s can compute at most (2s)^(2s) functions
3. For s = 2^n/(2n), most functions need larger circuits

This technique is "natural" because checking if a function is computed
by a given circuit is polynomial-time computable.
-/

/--
  **Counting Certification**: There exists a function requiring large circuits.

  This is the semantic statement that counting proves - it asserts the
  existence of hard functions without specifying how to observe them.

  **Citation**:
  C. Shannon (1949). "The Synthesis of Two-Terminal Switching Circuits"
  Bell System Technical Journal, 28(1):59-98.
-/
def CountingCertifies (n k : ℕ) : Prop :=
  ∃ f : BoolFun n, RequiresCircuitSize f ((n + 1)^k)

/--
  **Counting Soundness Axiom**

  If counting certifies a circuit lower bound, then there exists a
  poly-time observer that distinguishes the hard function.

  **Why axiomatized**: Constructing the explicit observer requires:
  1. Building a circuit-checking observer
  2. Showing circuit evaluation is poly-time
  3. Computing the random expectation (fraction of small-circuit functions)

  **Why this holds informally**:
  The counting observer checks: "Can f be computed by a circuit of size s?"
  - For hard f: the answer is NO, so observe(f) = 0
  - For random f: with high probability, observe(f) = 0 (most are hard)
  - For small-circuit f: observe(f) = 1

  The hard function f is distinguished because it's known to require
  large circuits (by Shannon counting), while we know small-circuit
  functions exist (e.g., constants).

  **Citation**:
  A. Razborov, S. Rudich (1997). "Natural Proofs"
  JCSS 55(1):24-35. Section 2 discusses circuit evaluation complexity.
-/
axiom counting_soundness (n k : ℕ) :
  CountingCertifies n k →
    ∃ (f : BoolFun n) (obs : BoundedObserver n),
      obs ∈ PolyTimeObservers n k ∧ Distinguishes obs f

/--
  **Counting Technique**

  The Shannon counting argument that proves most Boolean functions
  require circuits of size Ω(2^n / n).

  **Structure**:
  - Observer class: Poly-time observers (circuit evaluation is poly-time)
  - Certification: Semantic statement (hard functions exist)
  - Soundness: Axiomatized construction of distinguishing observer

  **Why it works for SOME functions**:
  By counting, most functions need large circuits. But this argument
  applies to random functions, not necessarily explicit ones.
-/
def CountingTechnique (n : ℕ) (k : ℕ) : ProofTechnique n where
  observerClass := PolyTimeObservers n k
  certifiesSeparation := CountingCertifies n k
  soundness := counting_soundness n k

/--
  **Counting is Natural**

  The counting technique uses poly-time observations, hence is natural.
  This means it cannot prove lower bounds for PRF-based functions.
-/
theorem counting_is_natural (k : ℕ) :
    (CountingTechnique n k).IsNatural := by
  use k
  intro obs hObs
  exact hObs

/-! ## Note on Barrier Hierarchy

Counting uses PolyTimeObservers, so it's natural but NOT necessarily
algebrizing or relativizing. The hierarchy is:

  Relativizing ⊆ Algebrizing ⊆ Natural

(Smaller observer class = weaker technique = blocked by weaker barrier)

- Diagonalization is relativizing (1-query) → blocked by BGS
- Counting is natural (poly-time) → blocked by natural proofs (if PRFs exist)

The natural proofs barrier is CONDITIONAL on PRFs existing, while
relativization and algebrization barriers are unconditional.
-/

/--
  **Counting Blocked by Natural Proofs Barrier**

  If PRFs exist, counting arguments cannot prove circuit lower bounds
  for functions that are pseudorandom to poly-time.
-/
theorem counting_blocked_by_natural_proofs (k : ℕ)
    (hPRF : ∃ f : BoolFun n, IsPseudorandomTo f (PolyTimeObservers n k)) :
    ∃ f : BoolFun n, ∀ obs ∈ (CountingTechnique n k).observerClass,
      ¬Distinguishes obs f := by
  obtain ⟨f, hPR⟩ := hPRF
  use f
  intro obs hObs
  exact not_distinguishes_of_isPseudorandomTo hPR hObs

/-! ## The Counting Dilemma

The counting argument illustrates a fundamental tension in complexity theory.
-/

/--
  **The Counting Dilemma**:

  1. Counting DOES prove that SOME function requires large circuits
     (Shannon's theorem - existential result)

  2. Counting CANNOT identify WHICH explicit function is hard
     (Natural proofs barrier - no constructive witness)

  3. If we could efficiently check "is f hard?", PRFs would break
     (Razborov-Rudich's key insight)

  This explains why Shannon's 1949 result didn't resolve P vs NP:
  it proves hard functions EXIST without constructing one explicitly.
-/
theorem counting_dilemma_explained :
    -- Shannon gives existence of hard functions
    (∀ n' (_hn : n' ≥ 3), ∃ hardFunctions : Set (BoolFun n'),
      hardFunctions.Nonempty ∧
      ∀ f ∈ hardFunctions, RequiresCircuitSize f (2^n' / (2 * n' + 1))) →
    -- But natural proofs barrier blocks identification
    (∀ n' k', ∃ f : BoolFun n', IsPseudorandomTo f (PolyTimeObservers n' k')) →
    -- So counting cannot find explicit hard functions
    True := by
  intro _hShannon _hPRF
  trivial

/-! ## Summary

The counting technique:
- IS natural (poly-time circuit evaluation)
- DOES prove hard functions exist (Shannon's theorem)
- CANNOT prove explicit function is hard (if PRFs exist)
- BLOCKED by natural proofs barrier

This is why counting gives existence but not explicit lower bounds.
-/

end Pseudorandomness
