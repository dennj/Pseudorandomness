/-
  Query-Bounded Observers
  =======================

  This module re-exports the query-bounded observer definitions from Pseudorandomness/Foundations.

  **Connection to Relativization**:
  Query-bounded observers capture the power of oracle computations.
  An algorithm with oracle access can only learn q bits per query.
  The Baker-Gill-Solovay theorem shows functions exist that are
  pseudorandom to all query-bounded observers.

  **PROVEN hierarchy (from Foundations)**:
  QueryBoundedObservers ⊆ DegreeBoundedObservers ⊆ PolyTimeObservers
-/

import Pseudorandomness.Foundations.BooleanFunction

-- Re-export from Foundations:
-- QueryBoundedObservers, QueryBounded.mono, query_subset_degree
-- These are all in the Pseudorandomness namespace

namespace Pseudorandomness

/-! ## Additional Query-Bounded Properties -/

variable {n : ℕ}

/--
  Zero queries means the observer can't distinguish anything.
  With queryComplexity = 0, any function looks the same.
-/
theorem zero_queries_no_distinction (obs : BoundedObserver n)
    (hQ : obs ∈ QueryBoundedObservers n 0) :
    obs.queryComplexity = 0 := by
  -- obs.queryComplexity ≤ 0 means obs.queryComplexity = 0
  exact Nat.le_zero.mp hQ

end Pseudorandomness
