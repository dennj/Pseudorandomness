import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Pseudorandomness.Core.LearningBarrier

/-!
  Contrastive Learning Bridge for Control / Time Series
  ====================================================

  This file instantiates the domain-agnostic contrastive learning barrier/magnification results
  for *time-series style data*.

  Input: an ensemble of length-2 traces `Z` on observations `Obs` (think: consecutive outputs).
  We push `Z` forward to a positive-pair ensemble on `Obs × Obs`, and take negatives to be the
  product of marginals (shuffle baseline).

  Then we can apply:
  - `ContrastiveLearning.barrier_productOfMarginals`
  - `ContrastiveLearning.breaks_productOfMarginals_of_successGap`

  This is a clean formal interface for modern “CPC / InfoNCE”-style arguments in control:
  if consecutive outputs are pseudorandom (indistinguishable from independent marginals) to a
  class of estimators, then contrastive objectives cannot yield a non-negligible advantage.
-/

namespace Pseudorandomness

namespace ControlContrastive

open Filter
open MeasureTheory
open CryptoMeasure
open LearningGame
open LearningBarrier
open LearningBarrier.ContrastiveLearning

universe u v

variable {Obs : Type u} [MeasurableSpace Obs]

abbrev ObsFam : ℕ → Type u := fun _k => Obs

noncomputable instance : ∀ k, MeasurableSpace (ObsFam (Obs := Obs) k) := fun _ => inferInstance

abbrev Trace2 : Type u := Fin 2 → Obs

noncomputable instance : MeasurableSpace (Trace2 (Obs := Obs)) := inferInstance

def pairOfTrace : Trace2 (Obs := Obs) → (Obs × Obs) :=
  fun tr => (tr (0 : Fin 2), tr (1 : Fin 2))

theorem measurable_pairOfTrace : Measurable (pairOfTrace (Obs := Obs)) := by
  classical
  -- `Trace2` is a finite product; projection maps are measurable.
  simpa [pairOfTrace] using
    Measurable.prod (measurable_pi_apply (0 : Fin 2)) (measurable_pi_apply (1 : Fin 2))

noncomputable def positivePairs (Z : Ensemble (fun _k : ℕ => Trace2 (Obs := Obs))) :
    Ensemble (PairExample (X := ObsFam (Obs := Obs))) :=
  fun k =>
    ProbabilityMeasure.map (Z k) (measurable_pairOfTrace (Obs := Obs)).aemeasurable

variable {Hyp : ℕ → Type v} {m : ℕ → ℕ}

abbrev Technique :=
  LearningBarrier.LearningTechnique (Example := PairExample (X := ObsFam (Obs := Obs))) (Hyp := Hyp) (m := m)

/--
Barrier form: if positive pairs `positivePairs Z` are indistinguishable from shuffled negatives
`productOfMarginals (positivePairs Z)` for `tech.D`, then every learner in `tech` has only a negligible
success-gap.
-/
theorem barrier_tracePairs
    (tech : Technique (Obs := Obs) (Hyp := Hyp) (m := m))
    (Z : Ensemble (fun _k : ℕ => Trace2 (Obs := Obs)))
    (hInd : Indistinguishable tech.D
      (iidSamplesEnsemble (positivePairs (Obs := Obs) Z) m)
      (iidSamplesEnsemble (productOfMarginals (X := ObsFam (Obs := Obs)) (positivePairs (Obs := Obs) Z)) m)) :
    ∀ L ∈ tech.learners,
      Negligible (fun k =>
        |successProb (X := positivePairs (Obs := Obs) Z) (m := m) L tech.good k -
          successProb (X := productOfMarginals (X := ObsFam (Obs := Obs)) (positivePairs (Obs := Obs) Z))
            (m := m) L tech.good k|) := by
  -- direct reuse of the domain-agnostic theorem
  simpa [ContrastiveLearning.Technique, Technique] using
    (ContrastiveLearning.barrier_productOfMarginals (X := ObsFam (Obs := Obs)) (Hyp := Hyp) (m := m)
      (tech := tech) (J := positivePairs (Obs := Obs) Z) hInd)

/--
Magnification/break form: a non-negligible success-gap yields a break of indistinguishability.
-/
theorem breaks_tracePairs_of_successGap
    (tech : Technique (Obs := Obs) (Hyp := Hyp) (m := m))
    (Z : Ensemble (fun _k : ℕ => Trace2 (Obs := Obs)))
    {L : Learner (PairExample (X := ObsFam (Obs := Obs))) Hyp m} (hL : L ∈ tech.learners)
    (hGap : ¬Negligible (fun k =>
      |successProb (X := positivePairs (Obs := Obs) Z) (m := m) L tech.good k -
        successProb (X := productOfMarginals (X := ObsFam (Obs := Obs)) (positivePairs (Obs := Obs) Z))
          (m := m) L tech.good k|)) :
    Breaks (Example := PairExample (X := ObsFam (Obs := Obs))) (m := m) tech.D
      (iidSamplesEnsemble (positivePairs (Obs := Obs) Z) m)
      (iidSamplesEnsemble (productOfMarginals (X := ObsFam (Obs := Obs)) (positivePairs (Obs := Obs) Z)) m) := by
  simpa [ContrastiveLearning.Technique, Technique] using
    (ContrastiveLearning.breaks_productOfMarginals_of_successGap (X := ObsFam (Obs := Obs)) (Hyp := Hyp)
      (m := m) (tech := tech) (J := positivePairs (Obs := Obs) Z) (L := L) hL hGap)

end ControlContrastive

end Pseudorandomness
