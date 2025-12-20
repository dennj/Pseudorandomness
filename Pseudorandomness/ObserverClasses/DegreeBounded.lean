/-
  Degree-Bounded Observers
  ========================

  This module re-exports the degree-bounded observer definitions from Pseudorandomness/Foundations.

  **Connection to Algebrization**:
  Degree-bounded observers capture the power of algebrizing techniques.
  Low-degree polynomial extensions can't distinguish random functions
  from structured ones (by Schwartz-Zippel type arguments).

  **PROVEN hierarchy (from Foundations)**:
  QueryBoundedObservers ⊆ DegreeBoundedObservers ⊆ PolyTimeObservers
-/

import Pseudorandomness.Foundations.BooleanFunction

-- Re-export from Foundations:
-- DegreeBoundedObservers, DegreeBounded.mono, degree_subset_polytime
-- These are all in the Pseudorandomness namespace

namespace Pseudorandomness

/-! ## Additional Degree-Bounded Properties -/

variable {n : ℕ}

/--
  Degree 0 means constant polynomials only - no dependence on input.
-/
theorem degree_zero_constant (obs : BoundedObserver n)
    (hD : obs ∈ DegreeBoundedObservers n 0) :
    obs.algebraicDegree = 0 := by
  exact Nat.le_zero.mp hD

end Pseudorandomness
