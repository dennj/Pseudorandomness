import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
  Minimal Neural Network Objects (ReLU)
  ===================================

  This file provides a small, concrete hypothesis class that we can use in
  ML-bridge statements: one-hidden-layer ReLU networks over `ℝ`.

  The development here is deliberately lightweight: we only define the objects and evaluation.
  Learning-theoretic notions (risk, empirical error, etc.) can be layered on top.
-/

namespace Pseudorandomness

namespace NeuralNet

open scoped BigOperators

/-- The ReLU activation `x ↦ max x 0`. -/
def relu (x : ℝ) : ℝ :=
  max x 0

theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := by
  simp [relu]

/--
A one-hidden-layer ReLU network with `width` hidden units and input dimension `d`.

We model it as a real-valued function `ℝ^d → ℝ`:

`x ↦ b₂ + ∑ i, w₂ i * relu (b₁ i + ∑ j, w₁ i j * x j)`.
-/
structure OneHiddenLayerReLU (d width : ℕ) where
  w1 : Fin width → Fin d → ℝ
  b1 : Fin width → ℝ
  w2 : Fin width → ℝ
  b2 : ℝ

namespace OneHiddenLayerReLU

variable {d width : ℕ}

def eval (net : OneHiddenLayerReLU d width) (x : Fin d → ℝ) : ℝ :=
  net.b2 +
    ∑ i : Fin width,
      net.w2 i *
        relu (net.b1 i + ∑ j : Fin d, net.w1 i j * x j)

end OneHiddenLayerReLU

end NeuralNet

end Pseudorandomness

