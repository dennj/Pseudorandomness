import Pseudorandomness.Core.LearningBarrier
import Pseudorandomness.Foundations.MeasureCrypto

/-!
  ML Magnification Wrappers
  ========================

  `Core/LearningBarrier.lean` is domain-agnostic. This file provides ML-facing
  specializations that produce `LearningBarrier.Breaks` statements for common ensembles.

  The point is not to bake in external hardness assumptions (lattices, SVP, etc.);
  rather, we package the “learner advantage ⇒ break indistinguishability” step so that
  later reductions can magnify the break into stronger consequences.
-/

namespace Pseudorandomness

namespace MachineLearningMagnification

open Filter
open CryptoMeasure
open LearningGame
open LearningBarrier
open MeasureTheory

universe u v w

variable {A : ℕ → Type u} {S : ℕ → Type v} {T : ℕ → Type w}
variable [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (T n)]
variable [∀ n, Add (T n)]

variable (aDist : ∀ n, ProbabilityMeasure (A n))
variable (noise uniform : ∀ n, ProbabilityMeasure (T n))
variable (φ : ∀ n, A n → S n → T n) (s : ∀ n, S n)
variable (hMap : ∀ n,
  AEMeasurable (CLWE.sampleMap (A := A) (S := S) (T := T) φ s n)
    (ProbabilityMeasure.prod (aDist n) (noise n)))

variable {m : ℕ → ℕ}
variable {Hyp' : ℕ → Type*}

/--
CLWE specialization: if some learner in `tech` has a non-negligible success-gap between the CLWE
real ensemble and the random ensemble, then the induced distinguisher breaks `tech.D`-indistinguishability
of the i.i.d. sample ensembles.
-/
theorem breaks_clwe_of_successGap
    (tech :
      LearningBarrier.LearningTechnique
        (Example := fun n => CLWE.Sample (A := A) (T := T) n) (Hyp := Hyp') (m := m))
    {L : Learner (fun n => CLWE.Sample (A := A) (T := T) n) Hyp' m}
    (hL : L ∈ tech.learners)
    (hGap : ¬Negligible (fun n =>
      |successProb
          (X := CLWE.realEnsemble (A := A) (S := S) (T := T) aDist noise φ s hMap)
          (m := m) L tech.good n -
        successProb
          (X := CLWE.randomEnsemble (A := A) (T := T) aDist uniform)
          (m := m) L tech.good n|)) :
    LearningBarrier.Breaks (Example := fun n => CLWE.Sample (A := A) (T := T) n) (m := m) tech.D
      (iidSamplesEnsemble (CLWE.realEnsemble (A := A) (S := S) (T := T) aDist noise φ s hMap) m)
      (iidSamplesEnsemble (CLWE.randomEnsemble (A := A) (T := T) aDist uniform) m) := by
  simpa using
    (LearningBarrier.breaks_of_nonNegligible_successGap (tech := tech)
      (X := CLWE.realEnsemble (A := A) (S := S) (T := T) aDist noise φ s hMap)
      (Y := CLWE.randomEnsemble (A := A) (T := T) aDist uniform)
      (L := L) hL hGap)

end MachineLearningMagnification

end Pseudorandomness

