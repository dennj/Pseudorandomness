/-
  Proof Techniques and Soundness
  ==============================

  This module defines what it means for a proof technique to be
  "O-bounded" and establishes the soundness requirement that
  connects abstract certification to concrete distinguishing.
-/

import Pseudorandomness.Core.Pseudorandomness

namespace Pseudorandomness

variable {n : ℕ}

/-! ## Proof Techniques -/

/--
  A **ProofTechnique** represents a method for proving complexity separations.

  The key insight: any proof technique that establishes a separation must
  somehow distinguish the hard function from random/easy functions.
  This is captured by the soundness requirement.

  **Fields**:
  - `observerClass`: The class of observers that T can employ
  - `certifiesSeparation`: A proposition that T "certifies" some separation
  - `soundness`: If T certifies a separation, it must exhibit a distinguisher

  **The soundness axiom is crucial**: It says that certification is not
  vacuous—if T claims a separation, it must witness it by finding a function
  that some observer can distinguish from random.
-/
structure ProofTechnique (n : ℕ) where
  /-- The observers available to this technique -/
  observerClass : ObserverClass n
  /-- The technique certifies some complexity separation -/
  certifiesSeparation : Prop
  /-- Soundness: certification implies a witness distinguisher -/
  soundness : certifiesSeparation →
    ∃ (f : BoolFun n) (obs : BoundedObserver n),
      obs ∈ observerClass ∧
      |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound

namespace ProofTechnique

/-! ## O-Boundedness -/

/--
  A proof technique T is **O-bounded** if T's observer class is
  contained in O.

  This captures the idea that T can only use observers from O.
  For example:
  - Relativizing techniques are QueryBounded-bounded
  - Algebrizing techniques are DegreeBounded-bounded
  - Natural techniques are PolyTime-bounded
-/
def isOBounded (T : ProofTechnique n) (O : ObserverClass n) : Prop :=
  T.observerClass ⊆ O

/-- O-boundedness is transitive in the observer class -/
theorem isOBounded_trans {T : ProofTechnique n} {O₁ O₂ : ObserverClass n}
    (h₁ : T.isOBounded O₁) (h₂ : O₁ ⊆ O₂) : T.isOBounded O₂ :=
  ObserverClass.subset_trans h₁ h₂

/-- Any technique is bounded by the universal class -/
theorem isOBounded_univ (T : ProofTechnique n) :
    T.isOBounded ObserverClass.univ :=
  ObserverClass.subset_univ T.observerClass

/-! ## Properties of Proof Techniques -/

/--
  **Soundness reformulated**: If T certifies separation, then
  there exists a function that T can distinguish from random.
-/
theorem soundness_distinguished (T : ProofTechnique n)
    (hCert : T.certifiesSeparation) :
    ∃ f : BoolFun n, ∃ obs ∈ T.observerClass, Distinguishes obs f := by
  obtain ⟨f, obs, hObs, hDist⟩ := T.soundness hCert
  exact ⟨f, obs, hObs, hDist⟩

/--
  **Contrapositive soundness**: If all functions are pseudorandom to
  T's observer class, then T cannot certify separation.
-/
theorem no_certification_if_all_pseudorandom (T : ProofTechnique n)
    (hAll : ∀ f : BoolFun n, IsPseudorandomTo f T.observerClass) :
    ¬T.certifiesSeparation := by
  intro hCert
  obtain ⟨f, obs, hObs, hDist⟩ := T.soundness hCert
  have hSmall := hAll f obs hObs
  exact absurd hSmall (not_lt.mpr hDist)

end ProofTechnique

end Pseudorandomness
