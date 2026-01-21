/-
  Observer-Induced Distances
  ==========================

  This module packages a basic, mathlib-friendly construction:

  Given a collection of "tests" / "observers" `T : Set (α → β)`, we get:
  - an indistinguishability relation on `α` (kernel of all tests),
  - and, when `β` is a seminormed additive commutative group, a canonical
    `PseudoEMetricSpace` structure on `α` by taking the `iSup` of test distances.

  This is a reusable object for instantiating the same pseudorandomness story
  across multiple domains (complexity, learning, control, number theory).
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.EMetricSpace.Basic

namespace Pseudorandomness

namespace ObserverDistance

/-! ### Turning observers into tests -/

def testsOf {ι α β : Type*} (O : Set ι) (eval : ι → α → β) : Set (α → β) :=
  Set.image eval O

/-! ### Kernel / indistinguishability -/

def AreIndistinguishable {α β : Type*} (T : Set (α → β)) (x y : α) : Prop :=
  ∀ t ∈ T, t x = t y

theorem areIndistinguishable_refl {α β : Type*} (T : Set (α → β)) (x : α) :
    AreIndistinguishable T x x := by
  intro t _ht
  rfl

theorem areIndistinguishable_symm {α β : Type*} (T : Set (α → β)) {x y : α}
    (h : AreIndistinguishable T x y) : AreIndistinguishable T y x := by
  intro t ht
  exact (h t ht).symm

theorem areIndistinguishable_trans {α β : Type*} (T : Set (α → β)) {x y z : α}
    (hxy : AreIndistinguishable T x y) (hyz : AreIndistinguishable T y z) :
    AreIndistinguishable T x z := by
  intro t ht
  exact (hxy t ht).trans (hyz t ht)

def indistinguishabilitySetoid {α β : Type*} (T : Set (α → β)) : Setoid α where
  r := AreIndistinguishable T
  iseqv :=
    ⟨areIndistinguishable_refl T, areIndistinguishable_symm T, areIndistinguishable_trans T⟩

theorem areIndistinguishable_testsOf_iff {ι α β : Type*} {O : Set ι} {eval : ι → α → β}
    {x y : α} :
    AreIndistinguishable (testsOf O eval) x y ↔ ∀ obs ∈ O, eval obs x = eval obs y := by
  constructor
  · intro h obs hObs
    exact h (eval obs) ⟨obs, hObs, rfl⟩
  · intro h t ht
    rcases ht with ⟨obs, hObs, rfl⟩
    exact h obs hObs

/-! ### An observer-induced `PseudoEMetricSpace` -/

section EDist

variable {α β : Type*} [NormedAddCommGroup β]

noncomputable def edist (T : Set (α → β)) (x y : α) : ENNReal :=
  ⨆ t : {f // f ∈ T}, ENNReal.ofReal ‖t.1 x - t.1 y‖

@[simp] theorem edist_self (T : Set (α → β)) (x : α) : edist T x x = 0 := by
  classical
  simp [edist]

@[simp] theorem edist_comm (T : Set (α → β)) (x y : α) : edist T x y = edist T y x := by
  classical
  simp [edist, norm_sub_rev]

theorem edist_triangle (T : Set (α → β)) (x y z : α) :
    edist T x z ≤ edist T x y + edist T y z := by
  classical
  refine iSup_le ?_
  intro t
  have hxy : ENNReal.ofReal ‖t.1 x - t.1 y‖ ≤ edist T x y := by
    exact le_iSup (fun s : {f // f ∈ T} => ENNReal.ofReal ‖s.1 x - s.1 y‖) t
  have hyz : ENNReal.ofReal ‖t.1 y - t.1 z‖ ≤ edist T y z := by
    exact le_iSup (fun s : {f // f ∈ T} => ENNReal.ofReal ‖s.1 y - s.1 z‖) t
  have htri :
      ‖t.1 x - t.1 z‖ ≤ ‖t.1 x - t.1 y‖ + ‖t.1 y - t.1 z‖ := by
    -- Apply triangle inequality to `(x - y) + (y - z) = x - z`.
    simpa [sub_add_sub_cancel] using
      (norm_add_le (t.1 x - t.1 y) (t.1 y - t.1 z))
  have htri' :
      ENNReal.ofReal ‖t.1 x - t.1 z‖ ≤
        ENNReal.ofReal (‖t.1 x - t.1 y‖ + ‖t.1 y - t.1 z‖) :=
    ENNReal.ofReal_le_ofReal htri
  have hsum :
      ENNReal.ofReal (‖t.1 x - t.1 y‖ + ‖t.1 y - t.1 z‖) =
        ENNReal.ofReal ‖t.1 x - t.1 y‖ + ENNReal.ofReal ‖t.1 y - t.1 z‖ := by
    simpa using
      (ENNReal.ofReal_add (by positivity : 0 ≤ ‖t.1 x - t.1 y‖)
        (by positivity : 0 ≤ ‖t.1 y - t.1 z‖))
  calc
    ENNReal.ofReal ‖t.1 x - t.1 z‖
        ≤ ENNReal.ofReal ‖t.1 x - t.1 y‖ + ENNReal.ofReal ‖t.1 y - t.1 z‖ := by
            simpa [hsum] using htri'
    _ ≤ edist T x y + edist T y z := by
          exact add_le_add hxy hyz

noncomputable def pseudoEMetricSpace (T : Set (α → β)) : PseudoEMetricSpace α where
  edist := edist T
  edist_self := ObserverDistance.edist_self (T := T)
  edist_comm := ObserverDistance.edist_comm (T := T)
  edist_triangle := ObserverDistance.edist_triangle (T := T)

theorem edist_eq_zero_iff_norm {T : Set (α → β)} {x y : α} :
    edist T x y = 0 ↔ ∀ t ∈ T, ‖t x - t y‖ = 0 := by
  classical
  constructor
  · intro h t ht
    have ht' : ENNReal.ofReal ‖t x - t y‖ ≤ edist T x y := by
      exact le_iSup (fun s : {f // f ∈ T} => ENNReal.ofReal ‖s.1 x - s.1 y‖) ⟨t, ht⟩
    have hle0 : ENNReal.ofReal ‖t x - t y‖ ≤ 0 := by
      simpa [h] using ht'
    have hz : ENNReal.ofReal ‖t x - t y‖ = 0 := le_antisymm hle0 (zero_le _)
    have hnorm_le0 : ‖t x - t y‖ ≤ 0 := by
      exact (ENNReal.ofReal_eq_zero.1 hz)
    exact le_antisymm hnorm_le0 (norm_nonneg _)
  · intro h
    apply le_antisymm
    · refine iSup_le ?_
      intro t
      have h0 : ‖t.1 x - t.1 y‖ = 0 := h t.1 t.2
      have : ENNReal.ofReal ‖t.1 x - t.1 y‖ = 0 := by
        simp [h0]
      simp [this]
    · exact zero_le _

theorem edist_eq_zero_iff_areIndistinguishable {T : Set (α → β)} {x y : α} :
    edist T x y = 0 ↔ AreIndistinguishable T x y := by
  classical
  constructor
  · intro h t ht
    have h0 : ‖t x - t y‖ = 0 := (edist_eq_zero_iff_norm (T := T) (x := x) (y := y)).1 h t ht
    have hsub : t x - t y = 0 := (norm_eq_zero).1 h0
    exact sub_eq_zero.1 hsub
  · intro h
    refine (edist_eq_zero_iff_norm (T := T) (x := x) (y := y)).2 ?_
    intro t ht
    have hEq : t x = t y := h t ht
    simp [hEq]

end EDist

end ObserverDistance

end Pseudorandomness
