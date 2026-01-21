/-
  Pseudorandomness - Additional Theorems
  ======================================

  This module provides additional theorems about pseudorandomness.
  The core definition IsPseudorandomTo is in Pseudorandomness/Foundations/BooleanFunction.lean.
-/

import Pseudorandomness.Core.Observer

namespace Pseudorandomness

variable {n : ℕ}

/-! ## Additional Pseudorandomness Properties -/

/--
  Any function is pseudorandom to the empty observer class.
  (Vacuously true: no observers to distinguish.)
-/
theorem pseudorandom_to_empty (f : BoolFun n) :
    IsPseudorandomTo f ObserverClass.empty := by
  intro obs hObs
  exact absurd hObs (Set.notMem_empty obs)

/--
  If f is pseudorandom to both O₁ and O₂, then f is pseudorandom
  to their union.
-/
theorem pseudorandom_union {f : BoolFun n} {O₁ O₂ : ObserverClass n}
    (h₁ : IsPseudorandomTo f O₁) (h₂ : IsPseudorandomTo f O₂) :
    IsPseudorandomTo f (ObserverClass.union O₁ O₂) := by
  intro obs hObs
  cases hObs with
  | inl h => exact h₁ obs h
  | inr h => exact h₂ obs h

/--
  If some observer in O distinguishes f, then f is not pseudorandom to O.
-/
theorem distinguisher_breaks_pseudorandom {f : BoolFun n} {O : ObserverClass n}
    {obs : BoundedObserver n} (hObs : obs ∈ O) (hDist : Distinguishes obs f) :
    ¬IsPseudorandomTo f O := by
  intro hPR
  exact (not_distinguishes_of_isPseudorandomTo hPR hObs) hDist

end Pseudorandomness
