/-
  The Observer Barrier: A Unified Theory of Complexity Barriers
  =============================================================

  A Lean4 formalization proving that the three classical barriers in computational
  complexity theory—relativization, algebrization, and natural proofs—are all
  instances of a single unifying principle: **pseudorandomness to bounded observers**.

  ## The Main Theorem

  **OBSERVER BARRIER** (`observer_barrier`):
  If there exists a function f pseudorandom to observer class O, then no O-bounded
  proof technique can both certify a complexity separation AND distinguish f from random.

  This single theorem, when instantiated with different observer classes, yields:
  - **Relativization** (O = QueryBounded): Baker-Gill-Solovay 1975
  - **Algebrization** (O = DegreeBounded): Aaronson-Wigderson 2009
  - **Natural Proofs** (O = PolyTime): Razborov-Rudich 1997

  ## Why This Matters

  The three classical barriers were discovered independently over 20+ years.
  This formalization shows they share a common mathematical structure:

    **PSEUDORANDOMNESS IS THE BARRIER.**

  A function pseudorandom to an observer class O blocks all O-bounded proof
  techniques. The classical barriers differ only in which observer class O they use.

  ## Project Structure

  - `Core/ObserverBarrier.lean`: **THE MAIN THEOREM** - `observer_barrier`
  - `Core/ProofTechnique.lean`: Abstract proof technique structure
  - `Foundations/BooleanFunction.lean`: Observer definitions and hierarchy proofs
  - `ObserverClasses/`: Query, Degree, and PolyTime observer classes
  - `BarrierInstances/`: The three classical barriers as direct corollaries
    - `Relativization.lean`: `relativization_barrier = observer_barrier QueryBounded`
    - `Algebrization.lean`: `algebrization_barrier = observer_barrier DegreeBounded`
    - `NaturalProofs.lean`: `natural_proofs_barrier = observer_barrier PolyTime`
  - `Applications/PvsNP.lean`: Implications for P vs NP

  ## The Observer Class Hierarchy (Proven)

  QueryBounded(q) ⊆ DegreeBounded(q+1) ⊆ PolyTime(d+1)

  This means natural proofs is the **strongest** barrier (blocks the most techniques).

  ## Key Results

  1. `observer_barrier`: The unified barrier theorem (Core/ObserverBarrier.lean:47)

  2. `relativization_barrier`: Direct corollary for query-bounded observers
     (BarrierInstances/Relativization.lean:57)

  3. `algebrization_barrier`: Direct corollary for degree-bounded observers
     (BarrierInstances/Algebrization.lean:59)

  4. `natural_proofs_barrier`: Direct corollary for poly-time observers
     (BarrierInstances/NaturalProofs.lean:71)

  5. `barrier_dichotomy`: For any O, either PR functions exist or O distinguishes all
     (Core/ObserverBarrier.lean:159)

  6. `natural_is_strongest_barrier`: PolyTime ⊇ DegreeBounded ⊇ QueryBounded
     (BarrierInstances/NaturalProofs.lean:143)

  7. `carmosino_from_observer_barrier`: Natural Proofs ↔ Learning derived from first principles
     (Applications/MachineLearningBridge.lean)

  ## References

  - T. Baker, J. Gill, R. Solovay (1975). "Relativizations of the P =? NP Question"
  - A. Razborov, S. Rudich (1997). "Natural Proofs"
  - S. Aaronson, A. Wigderson (2009). "Algebrization: A New Barrier"
-/

-- Core framework
import Pseudorandomness.Core.ObserverBarrier
import Pseudorandomness.Core.ProofTechnique
import Pseudorandomness.Core.LearningBarrier
import Pseudorandomness.Foundations.Crypto

-- The three classical barriers as corollaries
import Pseudorandomness.BarrierInstances.Relativization
import Pseudorandomness.BarrierInstances.Algebrization
import Pseudorandomness.BarrierInstances.NaturalProofs

-- Observer class definitions and hierarchy
import Pseudorandomness.ObserverClasses.Hierarchy

-- Applications
import Pseudorandomness.Applications.Complexity.PvsNP
import Pseudorandomness.Applications.MachineLearning.MachineLearningBridge
import Pseudorandomness.Applications.ControlTheory.ControlTheoryBridge
import Pseudorandomness.Applications.ControlTheory.StochasticControlBridge
import Pseudorandomness.Applications.ControlTheory.ControlLearningBarrier
import Pseudorandomness.Foundations.MeasureCrypto

namespace ObserverBarrierTheory

/-! ## Main Results - Re-exported for Visibility

The core contribution: **all three barriers are instances of one theorem**.
-/

/--
  **THE OBSERVER BARRIER (Main Theorem)**

  If f is pseudorandom to observer class O, then no O-bounded proof technique
  can certify a separation while distinguishing f.

  This is the foundational theorem. The classical barriers are corollaries.
-/
theorem main_theorem := @Pseudorandomness.observer_barrier

/--
  **RELATIVIZATION BARRIER** (Baker-Gill-Solovay 1975)

  Instantiation: O = QueryBoundedObservers

  Any technique that treats computation as a black box (oracle queries only)
  cannot separate P from NP.
-/
theorem relativization := @Pseudorandomness.relativization_barrier

/--
  **ALGEBRIZATION BARRIER** (Aaronson-Wigderson 2009)

  Instantiation: O = DegreeBoundedObservers

  Any technique that only uses low-degree polynomial queries cannot
  separate P from NP.
-/
theorem algebrization := @Pseudorandomness.algebrization_barrier

/--
  **NATURAL PROOFS BARRIER** (Razborov-Rudich 1997)

  Instantiation: O = PolyTimeObservers

  If PRFs exist, any technique using efficiently computable properties
  cannot prove circuit lower bounds.
-/
theorem natural_proofs := @Pseudorandomness.natural_proofs_barrier

/-! ## The Unification

The key insight: each barrier is exactly `observer_barrier O` for some O.
No additional axioms needed—the barriers are **definitional equalities**.
-/

example {n q : ℕ} (f : Pseudorandomness.BoolFun n)
    (hPR : Pseudorandomness.IsPseudorandomTo f (Pseudorandomness.QueryBoundedObservers n q)) :
    Pseudorandomness.relativization_barrier q f hPR =
    Pseudorandomness.observer_barrier (Pseudorandomness.QueryBoundedObservers n q) f hPR := rfl

example {n d : ℕ} (f : Pseudorandomness.BoolFun n)
    (hPR : Pseudorandomness.IsPseudorandomTo f (Pseudorandomness.DegreeBoundedObservers n d)) :
    Pseudorandomness.algebrization_barrier d f hPR =
    Pseudorandomness.observer_barrier (Pseudorandomness.DegreeBoundedObservers n d) f hPR := rfl

example {n k : ℕ} (f : Pseudorandomness.BoolFun n)
    (hPR : Pseudorandomness.IsPseudorandomTo f (Pseudorandomness.PolyTimeObservers n k)) :
    Pseudorandomness.natural_proofs_barrier k f hPR =
    Pseudorandomness.observer_barrier (Pseudorandomness.PolyTimeObservers n k) f hPR := rfl

/-! ## Carmosino Equivalence - Derived from First Principles

The Carmosino et al. (2016) theorem "Natural Proofs ↔ PAC Learning" follows
directly from the observer barrier framework.

Both natural proofs and learning reduce to **distinguishing from random**.
The observer barrier blocks both simultaneously when pseudorandom functions exist.

Key theorems in `Applications/MachineLearningBridge.lean`:

- `CircuitClass.carmosino_from_observer_barrier`: If PRFs exist, there exists
  a function that blocks both natural proofs and learning.

- `CircuitClass.pseudorandomness_blocks_both`: If all functions were pseudorandom
  to poly-time, neither natural proofs nor learning would be possible.

- `CircuitClass.isLearnable_iff_alt`: Learnability ↔ distinguishability from random.

This derivation shows WHY the Carmosino equivalence holds: natural proofs and
learning are the same capability (distinguishing from random) in different guises.
-/

/-! ## Control Theory Bridge

The observer barrier framework connects to control theory through the concept of
observability. The main result in `Applications/ControlTheoryBridge.lean`:

**OBSERVABILITY BRIDGE THEOREM** (`observability_bridge`):
A linear system is observable iff no non-zero state is pseudorandom to output observers.

This shows that Kalman's 1960s observability theory is an instance of the same
mathematical principle:

| Domain | Observer Class | Pseudorandom Object | Consequence |
|--------|---------------|---------------------|-------------|
| Complexity | Query/Degree/PolyTime | Hard function | Cannot prove separation |
| Control | Output observers | Unobservable state | Cannot identify state |

**Reference**: R.E. Kalman. "Mathematical Description of Linear Dynamical Systems."
SIAM J. Control, 1(2):152-192, 1963.
-/

end ObserverBarrierTheory
