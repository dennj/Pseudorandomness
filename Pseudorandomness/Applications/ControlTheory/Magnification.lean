import Pseudorandomness.Core.LearningBarrier
import Pseudorandomness.Applications.ControlTheory.StochasticControlBridge

/-!
  Control-Theory Magnification Wrappers
  ====================================

  `Core/LearningBarrier.lean` is domain-agnostic. This file provides control-theory-facing
  specializations for output-trace ensembles.

  The typical “magnification” use is:

  - show that a weak estimator advantage implies `Magnification.Breaks` for a distinguisher class `D`;
  - combine with a domain-specific reduction `Breaks → Consequence` (e.g. identifiability, security,
    or impossibility results) via `Magnification.magnify`.
-/

namespace Pseudorandomness

namespace ControlTheoryMagnification

open Filter
open CryptoMeasure
open LearningGame
open LearningBarrier
open MeasureTheory
open StochasticControl

variable {𝕜 : Type*} [Field 𝕜] [MeasurableSpace 𝕜]
variable {n m : ℕ}
variable (sys : ControlTheory.LinearSystem 𝕜 n m)

abbrev TraceExample : ℕ → Type _ :=
  fun _k => StochasticControl.Trace (𝕜 := 𝕜) (n := n) (m := m)

noncomputable instance : ∀ k, MeasurableSpace (TraceExample (𝕜 := 𝕜) (n := n) (m := m) k) :=
  fun _k => inferInstance

variable {mSamples : ℕ → ℕ}
variable {Hyp' : ℕ → Type*}

/--
Trace specialization: if some estimator in `tech` has a non-negligible success-gap between the
trace ensembles induced by two states `x₀,x₀'`, then it yields a distinguisher in `tech.D` that
breaks indistinguishability of the i.i.d. sample ensembles.
-/
theorem breaks_traces_of_successGap
    (tech :
      LearningBarrier.LearningTechnique
        (Example := TraceExample (𝕜 := 𝕜) (n := n) (m := m)) (Hyp := Hyp') (m := mSamples))
    {L : Learner (TraceExample (𝕜 := 𝕜) (n := n) (m := m)) Hyp' mSamples}
    (hL : L ∈ tech.learners)
    {x₀ x₀' : Fin n → 𝕜}
    (hGap : ¬Negligible (fun k =>
      |successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀) (m := mSamples) L tech.good k -
        successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀') (m := mSamples) L tech.good k|)) :
    LearningBarrier.Breaks (Example := TraceExample (𝕜 := 𝕜) (n := n) (m := m)) (m := mSamples) tech.D
      (iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀) mSamples)
      (iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀') mSamples) := by
  simpa [TraceExample] using
    (LearningBarrier.breaks_of_nonNegligible_successGap (tech := tech)
      (X := StochasticControl.traceEnsemble (sys := sys) x₀)
      (Y := StochasticControl.traceEnsemble (sys := sys) x₀')
      (L := L) hL hGap)

end ControlTheoryMagnification

end Pseudorandomness

