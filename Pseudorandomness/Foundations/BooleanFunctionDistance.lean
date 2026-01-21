import Pseudorandomness.Foundations.BooleanFunction
import Pseudorandomness.Foundations.ObserverDistance

namespace Pseudorandomness

open ObserverDistance

namespace BooleanFunctionDistance

variable {n : ℕ}

abbrev observerTests (O : ObserverClass n) : Set (BoolFun n → ℝ) :=
  ObserverDistance.testsOf O (fun obs : BoundedObserver n => obs.observe)

def IndistinguishableTo (O : ObserverClass n) (f g : BoolFun n) : Prop :=
  ObserverDistance.AreIndistinguishable (observerTests (n := n) O) f g

theorem indistinguishableTo_iff (O : ObserverClass n) (f g : BoolFun n) :
    IndistinguishableTo (n := n) O f g ↔ ∀ obs ∈ O, obs.observe f = obs.observe g := by
  simpa [IndistinguishableTo, observerTests] using
    (ObserverDistance.areIndistinguishable_testsOf_iff (O := O)
      (eval := fun obs : BoundedObserver n => obs.observe) (x := f) (y := g))

theorem indistinguishableTo_distinguishes_iff (O : ObserverClass n) {f g : BoolFun n}
    (h : IndistinguishableTo (n := n) O f g) :
    ∀ obs ∈ O, Distinguishes obs f ↔ Distinguishes obs g := by
  intro obs hObs
  have hEq : obs.observe f = obs.observe g :=
    (indistinguishableTo_iff (n := n) O f g).1 h obs hObs
  simp [Distinguishes, hEq]

theorem indistinguishableTo_isPseudorandomTo_iff (O : ObserverClass n) {f g : BoolFun n}
    (h : IndistinguishableTo (n := n) O f g) :
    IsPseudorandomTo f O ↔ IsPseudorandomTo g O := by
  constructor <;> intro hPR <;> intro obs hObs
  · have hEq : obs.observe f = obs.observe g :=
      (indistinguishableTo_iff (n := n) O f g).1 h obs hObs
    simpa [IsPseudorandomTo, hEq] using hPR obs hObs
  · have hEq : obs.observe f = obs.observe g :=
      (indistinguishableTo_iff (n := n) O f g).1 h obs hObs
    simpa [IsPseudorandomTo, hEq] using hPR obs hObs

noncomputable def observerEdist (O : ObserverClass n) (f g : BoolFun n) : ENNReal :=
  ObserverDistance.edist (observerTests (n := n) O) f g

theorem observerEdist_eq_zero_iff (O : ObserverClass n) (f g : BoolFun n) :
    observerEdist (n := n) O f g = 0 ↔ IndistinguishableTo (n := n) O f g := by
  simpa [observerEdist, IndistinguishableTo, observerTests] using
    (ObserverDistance.edist_eq_zero_iff_areIndistinguishable (T := observerTests (n := n) O)
      (x := f) (y := g))

/-! ### Approximate / robust indistinguishability via `observerEdist` -/

/--
`EpsilonIndistinguishableTo O ε f g` means `f` and `g` are within `ε` under the observer-induced
extended pseudo-metric. This is a robust (noise-stable) relaxation of `IndistinguishableTo`.
-/
def EpsilonIndistinguishableTo (O : ObserverClass n) (ε : ℝ) (f g : BoolFun n) : Prop :=
  observerEdist (n := n) O f g ≤ ENNReal.ofReal ε

theorem EpsilonIndistinguishableTo_iff (O : ObserverClass n) {ε : ℝ} (hε : 0 ≤ ε)
    (f g : BoolFun n) :
    EpsilonIndistinguishableTo (n := n) O ε f g ↔
      ∀ obs ∈ O, |obs.observe f - obs.observe g| ≤ ε := by
  classical
  constructor
  · intro h obs hObs
    have hle : ENNReal.ofReal ‖obs.observe f - obs.observe g‖ ≤ observerEdist (n := n) O f g := by
      -- Unfold as `iSup`, then choose the test `obs.observe`.
      -- `obs.observe ∈ testsOf O _` by definition.
      exact le_iSup (fun t : {h // h ∈ observerTests (n := n) O} =>
        ENNReal.ofReal ‖t.1 f - t.1 g‖) ⟨obs.observe, ⟨obs, hObs, rfl⟩⟩
    have hle' : ENNReal.ofReal ‖obs.observe f - obs.observe g‖ ≤ ENNReal.ofReal ε :=
      le_trans hle h
    have : ‖obs.observe f - obs.observe g‖ ≤ ε :=
      (ENNReal.ofReal_le_ofReal_iff hε).1 hle'
    simpa [Real.norm_eq_abs] using this
  · intro h
    -- `iSup` is bounded if each test is bounded.
    refine iSup_le ?_
    intro t
    rcases t with ⟨test, ht⟩
    rcases ht with ⟨obs, hObs, rfl⟩
    have hObsBound : |obs.observe f - obs.observe g| ≤ ε := h obs hObs
    -- Convert back to `ENNReal`.
    have : ENNReal.ofReal ‖obs.observe f - obs.observe g‖ ≤ ENNReal.ofReal ε := by
      -- `‖x‖ = |x|` for `ℝ`.
      simpa [Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hObsBound
    simpa [observerEdist, observerTests] using this

theorem epsilonIndistinguishableTo_zero_iff (O : ObserverClass n) (f g : BoolFun n) :
    EpsilonIndistinguishableTo (n := n) O 0 f g ↔ IndistinguishableTo (n := n) O f g := by
  -- `edist ≤ 0` iff `edist = 0`.
  have : observerEdist (n := n) O f g ≤ (0 : ENNReal) ↔ observerEdist (n := n) O f g = 0 :=
    ⟨fun h => le_antisymm h (zero_le _), fun h => h.le⟩
  simp [EpsilonIndistinguishableTo, ENNReal.ofReal_zero, observerEdist_eq_zero_iff, this]

/-! ### Robust pseudorandomness: stability under perturbations -/

theorem isPseudorandomToWithSlack_of_observerEdist_le (O : ObserverClass n) {f g : BoolFun n}
    {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : observerEdist (n := n) O f g ≤ ENNReal.ofReal ε)
    (hPR : IsPseudorandomTo g O) :
    IsPseudorandomToWithSlack f O ε := by
  intro obs hObs
  have hSmall : |obs.observe g - obs.randomExpectation| < 1 / obs.bound :=
    hPR obs hObs
  have hfg : |obs.observe f - obs.observe g| ≤ ε :=
    (EpsilonIndistinguishableTo_iff (n := n) O hε f g).1 hclose obs hObs
  -- Triangle inequality: `|f-r| ≤ |f-g| + |g-r|`.
  have htri :
      |obs.observe f - obs.randomExpectation| ≤
        |obs.observe f - obs.observe g| + |obs.observe g - obs.randomExpectation| :=
    abs_sub_le (obs.observe f) (obs.observe g) (obs.randomExpectation)
  -- Combine `< 1/bound` and `≤ ε`.
  have :
      |obs.observe f - obs.randomExpectation| <
        (1 / obs.bound) + ε := by
    calc
      |obs.observe f - obs.randomExpectation|
          ≤ |obs.observe f - obs.observe g| + |obs.observe g - obs.randomExpectation| := htri
      _ < ε + (1 / obs.bound) := by
            exact add_lt_add_of_le_of_lt hfg hSmall
      _ = (1 / obs.bound) + ε := by ac_rfl
  -- Match the slack definition shape.
  simpa [IsPseudorandomToWithSlack] using this

/-! ### Observable quotient

`ObservableQuotient O` is the quotient of `BoolFun n` by the kernel of the observer class `O`.
This packages the idea that all reasoning “using only observers in `O`” factors through this
quotient.
-/

def indistinguishabilitySetoid (O : ObserverClass n) : Setoid (BoolFun n) :=
  ObserverDistance.indistinguishabilitySetoid (observerTests (n := n) O)

abbrev ObservableQuotient (O : ObserverClass n) : Type _ :=
  Quotient (indistinguishabilitySetoid (n := n) O)

abbrev toObservableQuotient (O : ObserverClass n) (f : BoolFun n) : ObservableQuotient (n := n) O :=
  Quotient.mk (indistinguishabilitySetoid (n := n) O) f

theorem toObservableQuotient_eq_iff (O : ObserverClass n) (f g : BoolFun n) :
    toObservableQuotient (n := n) O f = toObservableQuotient (n := n) O g ↔
      IndistinguishableTo (n := n) O f g := by
  -- `Quotient.mk` equality is exactly the quotient relation.
  exact Quotient.eq

/-- Each observation `obs.observe` (for `obs ∈ O`) factors through the quotient. -/
noncomputable def observeOnQuotient (O : ObserverClass n) (obs : BoundedObserver n)
    (hObs : obs ∈ O) : ObservableQuotient (n := n) O → ℝ :=
  Quotient.lift (fun f : BoolFun n => obs.observe f) (by
    intro f g hfg
    exact (indistinguishableTo_iff (n := n) O f g).1 hfg obs hObs)

@[simp] theorem observeOnQuotient_mk (O : ObserverClass n) (obs : BoundedObserver n) (hObs : obs ∈ O)
    (f : BoolFun n) :
    observeOnQuotient (n := n) O obs hObs (toObservableQuotient (n := n) O f) = obs.observe f :=
  rfl

/-- `Distinguishes obs` (for `obs ∈ O`) factors through the quotient. -/
noncomputable def distinguishesOnQuotient (O : ObserverClass n) (obs : BoundedObserver n)
    (hObs : obs ∈ O) : ObservableQuotient (n := n) O → Prop :=
  Quotient.lift (fun f : BoolFun n => Distinguishes obs f) (by
    intro f g hfg
    -- `Distinguishes` depends on `obs.observe f`, so it is invariant under `O`-indistinguishability.
    have : Distinguishes obs f ↔ Distinguishes obs g :=
      (indistinguishableTo_distinguishes_iff (n := n) O (f := f) (g := g) hfg) obs hObs
    exact propext this)

@[simp] theorem distinguishesOnQuotient_mk (O : ObserverClass n) (obs : BoundedObserver n) (hObs : obs ∈ O)
    (f : BoolFun n) :
    distinguishesOnQuotient (n := n) O obs hObs (toObservableQuotient (n := n) O f) ↔
      Distinguishes obs f :=
  Iff.rfl

/-- `IsPseudorandomTo · O` is well-defined on the observable quotient. -/
noncomputable def isPseudorandomToOnQuotient (O : ObserverClass n) :
    ObservableQuotient (n := n) O → Prop :=
  Quotient.lift (fun f : BoolFun n => IsPseudorandomTo f O) (by
    intro f g hfg
    exact propext (indistinguishableTo_isPseudorandomTo_iff (n := n) O (f := f) (g := g) hfg))

@[simp] theorem isPseudorandomToOnQuotient_mk (O : ObserverClass n) (f : BoolFun n) :
    isPseudorandomToOnQuotient (n := n) O (toObservableQuotient (n := n) O f) ↔
      IsPseudorandomTo f O :=
  Iff.rfl

theorem isPseudorandomToOnQuotient_iff_no_distinguisher (O : ObserverClass n)
    (q : ObservableQuotient (n := n) O) :
    isPseudorandomToOnQuotient (n := n) O q ↔
      ∀ obs (hObs : obs ∈ O), ¬distinguishesOnQuotient (n := n) O obs hObs q := by
  refine Quotient.inductionOn q ?_
  intro f
  simp [isPseudorandomToOnQuotient, distinguishesOnQuotient, pseudorandom_iff_no_distinguisher]

end BooleanFunctionDistance

end Pseudorandomness
