/-
  Polynomial-Time Observers
  =========================

  This module re-exports the poly-time observer definitions from Pseudorandomness/Foundations.

  **Connection to Natural Proofs**:
  Poly-time observers capture the power of natural proof techniques.
  If PRFs exist, there are functions pseudorandom to all poly-time
  observers, blocking natural proofs.

  **PROVEN hierarchy (from Foundations)**:
  QueryBoundedObservers ⊆ DegreeBoundedObservers ⊆ PolyTimeObservers
-/

import Pseudorandomness.Foundations.BooleanFunction

-- Re-export from Foundations:
-- PolyTimeObservers, PolyTime.mono
-- These are all in the Pseudorandomness namespace

namespace Pseudorandomness

/-! ## Additional Poly-Time Properties -/

variable {n : ℕ}

/--
  All BoundedObservers are poly-time for some polynomial exponent.
  This follows from polynomial_evaluation_complexity: timeComplexity ≤ (n+1)^(algebraicDegree+1).
-/
theorem all_observers_polytime (obs : BoundedObserver n) :
    obs ∈ PolyTimeObservers n (obs.algebraicDegree + 1) := by
  exact polynomial_evaluation_complexity obs

end Pseudorandomness
