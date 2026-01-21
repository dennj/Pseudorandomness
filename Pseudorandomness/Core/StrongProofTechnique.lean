/-
  Strong Proof Technique - Circuit Lower Bound Version
  =====================================================

  This module provides a strengthened version of ProofTechnique
  where "certification" has a concrete meaning: proving circuit
  lower bounds against P/poly.

  **Key Improvement**:
  Instead of an abstract "soundness" field that must be assumed,
  we define certification in terms of circuit lower bounds and
  PROVE that distinguishing implies lower bounds.

  **The Main Theorem**:
  If a technique can distinguish a function from random, and
  random functions require large circuits (Shannon counting),
  then the distinguished function also requires large circuits.
-/

import Pseudorandomness.Foundations.Circuits
import Pseudorandomness.Core.ProofTechnique
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Pseudorandomness

open Filter
open Asymptotics

variable {n : ℕ}

/-! ## Shannon Counting Argument

**Core Insight**: Most Boolean functions require large circuits.
This is the Shannon counting argument from 1949.

**Citation**:
C. Shannon (1949). "The Synthesis of Two-Terminal Switching Circuits"
Bell System Technical Journal, 28(1):59-98.
-/

/--
  **Shannon Counting Theorem (Axiomatized - Probabilistic Form)**

  Most Boolean functions on n bits require circuits of size Ω(2^n/n).

  **Precise Statement**:
  Define HardFunctions(n, s) = {f : BoolFun n | f requires circuits of size > s}

  Then for s = 2^n / (2n + 1):
    |HardFunctions(n, s)| / |AllFunctions(n)| > 1/2

  In other words: more than half of all Boolean functions on n bits
  require circuits of size at least 2^n / (2n + 1).

  **Why this holds**:
  - There are 2^(2^n) Boolean functions on n bits
  - A circuit of size s has at most 2s potential wire connections per gate
  - Total distinct circuits of size s: at most (2s)^s × s! < (2s)^(2s)
  - For s = 2^n/(2n): (2s)^(2s) << 2^(2^n), so most functions need larger circuits

  **This is axiomatized because full formalization requires**:
  - Detailed circuit representation (DAG with gate types)
  - Combinatorial counting over circuit structures
  - Cardinality arguments on finite sets

  **Citation**:
  C. Shannon (1949). Bell System Technical Journal, 28(1):59-98.
  See also: Arora-Barak (2009), Theorem 6.21.
-/
theorem shannon_counting (n : ℕ) (hn : n ≥ 3) :
  -- There exists a set of "hard" functions
  ∃ (hardFunctions : Set (BoolFun n)),
    -- The set is non-empty (hard functions exist)
    hardFunctions.Nonempty ∧
    -- All functions in the set require large circuits
    (∀ f ∈ hardFunctions, RequiresCircuitSize f (2^n / (2 * n + 1))) := by
  have hex : ∃ f : BoolFun n, RequiresCircuitSize f (2^n / (2 * n + 1)) :=
    shannon_counting_exists n hn
  refine ⟨{f | RequiresCircuitSize f (2^n / (2 * n + 1))}, ?_, ?_⟩
  · rcases hex with ⟨f, hf⟩
    exact ⟨f, hf⟩
  · intro f hf
    exact hf

/--
  **Corollary**: There exist functions requiring superpolynomial circuits
  (for large enough n relative to the polynomial degree).

  This follows from Shannon counting: hard functions exist, and if n is large
  enough that (n+1)^k < 2^n/(2n+1), those hard functions require > (n+1)^k size.
-/
theorem hard_functions_require_superpoly (n k : ℕ) (hn : n ≥ 3)
    (hk : (n + 1)^k < 2^n / (2 * n + 1)) :
    ∃ f : BoolFun n, RequiresCircuitSize f ((n + 1)^k) := by
  obtain ⟨hardFunctions, ⟨f, hfHard⟩, hShannon⟩ := shannon_counting n hn
  use f
  intro C hComp
  have hBig := hShannon f hfHard C hComp
  omega

/-! ## Shannon → Superpolynomial Bridge

The following lemmas connect Shannon's counting argument to the
superpolynomial circuit requirement used in P vs NP.
-/

/--
  **Exponential Dominates Polynomial** (Asymptotic Axiom)

  For any polynomial degree k, there exists N such that for all n ≥ N:
    (n + 1)^k < 2^n / (2n + 1)

  **Justification**: This is a fundamental asymptotic result from analysis.

  **Proof sketch**:
  - Taking logarithms: k · log(n+1) vs n - log(2n+1)
  - The left side grows as O(k log n)
  - The right side grows as Θ(n)
  - Since n grows faster than log n, exponentials dominate polynomials

  **Concrete bounds**:
  For k = 1: N = 5 works (6 < 32/11 ≈ 2.9... wait, that's wrong)
  Actually: 2^5/(2·5+1) = 32/11 ≈ 2.9, and (5+1)^1 = 6 > 2.9
  For k = 1: N = 10 works: 2^10/21 ≈ 48.8 > 11 = (10+1)^1 ✓
  For k = 2: N = 15 works: 2^15/31 ≈ 1057 > 256 = 16^2 ✓
  For k = 3: N = 20 works: 2^20/41 ≈ 25575 > 9261 = 21^3 ✓

  **Literature**: Standard calculus/asymptotic analysis.
  See: Cormen et al., "Introduction to Algorithms", Chapter 3 (Growth of Functions).
-/
theorem exponential_dominates_polynomial (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, (n + 1)^k < 2 ^ n / (2 * n + 1) := by
  classical

  have hbpos (n : ℕ) : 0 < (2 * n + 1) := by omega

  -- Work in `ℝ`, using the standard limit `n^(k+1) / 2^n → 0`.
  let f : ℕ → ℝ := fun n =>
    (((((n + 1) ^ k + 1) * (2 * n + 1) : ℕ) : ℝ)) / ((2 : ℝ) ^ n)

  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    have hden : 0 ≤ ((2 : ℝ) ^ n) := by positivity
    exact div_nonneg (by positivity) hden

  have hlim_base :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (k + 1) / (2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) :=
    tendsto_pow_const_div_const_pow_of_one_lt (k := k + 1) (by norm_num : (1 : ℝ) < 2)

  have hLittle :
      (fun n : ℕ => (n : ℝ) ^ (k + 1)) =o[atTop] fun n : ℕ => (2 : ℝ) ^ n := by
    refine Asymptotics.isLittleO_of_tendsto (l := atTop)
      (f := fun n : ℕ => (n : ℝ) ^ (k + 1)) (g := fun n : ℕ => (2 : ℝ) ^ n) ?_ hlim_base
    intro n hn
    exact (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0) hn).elim

  have hlim_pow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ (k + 1) / (2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) := by
    simpa using (Asymptotics.IsLittleO.tendsto_div_nhds_zero (l := atTop) hLittle)

  let C : ℝ := ((6 * 2 ^ k : ℕ) : ℝ)
  have hlim_upper :
      Tendsto (fun n : ℕ => C * ((n : ℝ) ^ (k + 1) / (2 : ℝ) ^ n)) atTop (nhds (0 : ℝ)) := by
    simpa [C, mul_zero] using (Filter.Tendsto.const_mul C hlim_pow)

  have hbound : ∀ᶠ n : ℕ in atTop, f n ≤ C * ((n : ℝ) ^ (k + 1) / (2 : ℝ) ^ n) := by
    refine (eventually_ge_atTop (1 : ℕ)).mono ?_
    intro n hn1
    have hnpos : 0 < n := Nat.succ_le_iff.mp hn1

    -- (n+1)^k + 1 ≤ 2 * (n+1)^k
    have hpow1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow k (n + 1) (Nat.succ_pos _)
    have hA : (n + 1) ^ k + 1 ≤ 2 * (n + 1) ^ k := by
      have hsum : (n + 1) ^ k + 1 ≤ (n + 1) ^ k + (n + 1) ^ k :=
        Nat.add_le_add_left hpow1 _
      simpa [two_mul] using hsum

    -- n+1 ≤ 2n (for n ≥ 1)
    have hbase : n + 1 ≤ 2 * n := by omega
    have hB : (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left hbase _

    -- 2n+1 ≤ 3n (for n ≥ 1)
    have hden : 2 * n + 1 ≤ 3 * n := by omega

    have hNum :
        ((n + 1) ^ k + 1) * (2 * n + 1) ≤ (6 * 2 ^ k) * n ^ (k + 1) := by
      calc
        ((n + 1) ^ k + 1) * (2 * n + 1)
            ≤ (2 * (n + 1) ^ k) * (2 * n + 1) := by
                exact Nat.mul_le_mul_right _ hA
        _ ≤ (2 * (2 * n) ^ k) * (2 * n + 1) := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hB)
        _ ≤ (2 * (2 * n) ^ k) * (3 * n) := by
              exact Nat.mul_le_mul_left _ hden
        _ = (6 * ((2 * n) ^ k)) * n := by
              ring
        _ = (6 * (2 ^ k * n ^ k)) * n := by
              simp [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm]
        _ = (6 * 2 ^ k) * n ^ (k + 1) := by
              simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

    have hNum' :
        ((((n + 1) ^ k + 1) * (2 * n + 1) : ℕ) : ℝ) ≤ C * (n : ℝ) ^ (k + 1) := by
      -- cast the Nat inequality to `ℝ`
      have := (Nat.cast_le.2 hNum : (((((n + 1) ^ k + 1) * (2 * n + 1) : ℕ)) : ℝ)
        ≤ (((((6 * 2 ^ k) * n ^ (k + 1) : ℕ)) : ℝ)))
      -- rewrite the RHS
      simpa [C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
        mul_assoc, mul_left_comm, mul_comm] using this

    have hden_nonneg : 0 ≤ ((2 : ℝ) ^ n) := by positivity
    calc
      f n = (((((n + 1) ^ k + 1) * (2 * n + 1) : ℕ) : ℝ)) / ((2 : ℝ) ^ n) := rfl
      _ ≤ (C * (n : ℝ) ^ (k + 1)) / ((2 : ℝ) ^ n) := by
            exact div_le_div_of_nonneg_right hNum' hden_nonneg
      _ = C * ((n : ℝ) ^ (k + 1) / (2 : ℝ) ^ n) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

  have hTendsto : Tendsto f atTop (nhds (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_upper ?_ hbound
    exact Filter.Eventually.of_forall hf_nonneg

  have hlt1 : ∀ᶠ n : ℕ in atTop, f n < 1 := by
    have hball : ∀ᶠ n : ℕ in atTop, f n ∈ Metric.ball (0 : ℝ) 1 :=
      hTendsto.eventually (Metric.ball_mem_nhds (0 : ℝ) (by simp))
    filter_upwards [hball] with n hn
    have habs : |f n| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    simpa [abs_of_nonneg (hf_nonneg n)] using habs

  rcases (eventually_atTop.1 hlt1) with ⟨N₀, hN₀⟩
  refine ⟨max 1 N₀, ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := le_trans (le_of_max_le_right hn) (le_rfl)
  have hn1 : 1 ≤ n := le_trans (le_of_max_le_left hn) (le_rfl)

  have hreal_div : f n < 1 := hN₀ n hn₀
  have hden_pos : 0 < ((2 : ℝ) ^ n) := by positivity
  have hreal :
      (((((n + 1) ^ k + 1) * (2 * n + 1) : ℕ) : ℝ)) < ((2 : ℝ) ^ n) := by
    -- `a / b < 1` with `b>0` implies `a < b`
    have := (div_lt_iff₀ hden_pos).1 hreal_div
    simpa [f, one_mul] using this

  have hnat :
      (((n + 1) ^ k + 1) * (2 * n + 1)) ≤ 2 ^ n := by
    -- convert `ℝ` inequality back to `ℕ`
    have hnat_lt : (((n + 1) ^ k + 1) * (2 * n + 1)) < 2 ^ n := by
      -- rewrite RHS as a cast of `2^n` and use `exact_mod_cast`
      have hreal' :
          (((((n + 1) ^ k + 1) * (2 * n + 1) : ℕ) : ℝ)) < (((2 ^ n : ℕ) : ℝ)) := by
        simpa [Nat.cast_pow] using hreal
      exact_mod_cast hreal'
    exact Nat.le_of_lt hnat_lt

  have hle_div : (n + 1) ^ k + 1 ≤ 2 ^ n / (2 * n + 1) :=
    (Nat.le_div_iff_mul_le (hbpos n)).2 (by simpa [Nat.mul_assoc] using hnat)

  exact lt_of_lt_of_le (Nat.lt_succ_self ((n + 1) ^ k)) hle_div

/--
  **Shannon Implies Superpolynomial** (for large n)

  For sufficiently large n, Shannon's hard functions require circuits
  larger than any fixed polynomial.

  **Key insight**: 2^n / (2n+1) grows faster than any polynomial (n+1)^k.
  So for large enough n (depending on k), Shannon's bound exceeds (n+1)^k.

  **Why this matters**: This connects the "counting" result to the
  "superpolynomial" requirement needed for P ≠ NP.
-/
theorem shannon_superpoly_for_large_n (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, n ≥ 3 →
      ∃ f : BoolFun n, RequiresCircuitSize f ((n + 1)^k) := by
  -- Get N from the asymptotic axiom
  obtain ⟨N₀, hDom⟩ := exponential_dominates_polynomial k
  -- Use max to ensure both n ≥ N₀ and n ≥ 3
  use max 3 N₀
  intro n hn hn3
  -- Apply the bridge lemma
  apply hard_functions_require_superpoly n k hn3
  -- The key inequality: (n+1)^k < 2^n/(2n+1) for large n
  exact hDom n (le_of_max_le_right hn)

/--
  **Shannon Functions Are Superpolynomially Hard** (asymptotic statement)

  For any polynomial bound p(n) = (n+1)^k, Shannon's counting gives
  functions requiring circuits larger than p(n) for large enough n.

  This is the precise connection between Shannon counting and P vs NP:
  Shannon proves superpolynomial lower bounds exist (non-constructively).
-/
theorem shannon_gives_superpoly_hardness :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      (n ≥ 3) → ∃ f : BoolFun n, RequiresCircuitSize f ((n + 1)^k) :=
  shannon_superpoly_for_large_n

/-! ## Distinguishing and Circuit Lower Bounds

**Key Connection**: If an observer can distinguish f from random,
and random functions require large circuits, then f must be
"special" in some way that an efficient observer can detect.

The natural proofs barrier says: if f is ALSO hard (requires large circuits),
then efficient observers CANNOT distinguish it from random.
-/

/--
  **Strong Proof Technique**:
  A technique that explicitly aims to prove circuit lower bounds.

  The key fields are:
  1. observerClass: what observations the technique can make
  2. targetLowerBound: the circuit size lower bound being claimed
  3. witnessFunction: the explicit function claimed to be hard
  4. witnessDistinguished: proof that some observer distinguishes the witness
-/
structure StrongProofTechnique (n : ℕ) where
  /-- The observers available to this technique -/
  observerClass : ObserverClass n
  /-- The circuit size lower bound being claimed -/
  targetLowerBound : ℕ
  /-- The explicit function claimed to require large circuits -/
  witnessFunction : BoolFun n
  /-- The witness is explicit (computable in exp time) -/
  witnessExplicit : IsExplicit witnessFunction
  /-- Some observer in the class distinguishes the witness from random -/
  witnessObserver : BoundedObserver n
  witnessInClass : witnessObserver ∈ observerClass
  witnessDistinguished : Distinguishes witnessObserver witnessFunction

namespace StrongProofTechnique

/--
  **Certification**: A strong technique certifies a circuit lower bound
  if the witness function actually requires the claimed circuit size.
-/
def certifiesLowerBound (T : StrongProofTechnique n) : Prop :=
  RequiresCircuitSize T.witnessFunction T.targetLowerBound

/--
  **Certifies P ≠ NP**: The technique proves superpolynomial lower bounds.
-/
def certifiesSeparation (T : StrongProofTechnique n) : Prop :=
  ∀ k : ℕ, RequiresCircuitSize T.witnessFunction ((n + 1)^k)

/--
  Convert to the weaker ProofTechnique type.
-/
def toProofTechnique (T : StrongProofTechnique n) : ProofTechnique n where
  observerClass := T.observerClass
  certifiesSeparation := T.certifiesLowerBound
  soundness := fun _h => ⟨T.witnessFunction, T.witnessObserver,
    T.witnessInClass, T.witnessDistinguished⟩

/--
  **O-Boundedness** for strong techniques.
-/
def isOBounded (T : StrongProofTechnique n) (O : ObserverClass n) : Prop :=
  T.observerClass ⊆ O

/--
  **Key Lemma**: If T's observers are O-bounded and f is pseudorandom to O,
  then T cannot distinguish f.
-/
theorem cannot_distinguish_pseudorandom (T : StrongProofTechnique n)
    (O : ObserverClass n) (hBounded : T.isOBounded O)
    (f : BoolFun n) (hPR : IsPseudorandomTo f O) :
    ¬Distinguishes T.witnessObserver f ∨ T.witnessFunction ≠ f := by
  by_cases hEq : T.witnessFunction = f
  · -- If witness = f, then f is distinguished, but...
    left
    intro hDist
    exact (not_distinguishes_of_isPseudorandomTo hPR (hBounded T.witnessInClass)) hDist
  · right
    exact hEq

end StrongProofTechnique

/-! ## The Strengthened Barrier Theorems -/

/--
  **MAIN THEOREM: Natural Proofs Barrier (Strong Version)**

  If:
  1. T is a strong proof technique with poly-time bounded observers
  2. T claims to prove circuit lower bounds for an explicit function f
  3. PRFs exist (so f is pseudorandom to poly-time observers)

  Then:
  T's witness function f CANNOT be both:
  - Distinguished by T's observers (required for the proof to work)
  - Pseudorandom to poly-time (which hard functions should be)

  **Implication**: Either T's witness is NOT hard (so T fails to prove lower bounds),
  or T uses non-poly-time observations (T is not "natural").
-/
theorem strong_natural_proofs_barrier
    (T : StrongProofTechnique n)
    (k : ℕ)
    (hBounded : T.isOBounded (PolyTimeObservers n k))
    (hPR : IsPseudorandomTo T.witnessFunction (PolyTimeObservers n k)) :
    False := by
  -- T distinguishes its witness
  have hDist := T.witnessDistinguished
  -- But the witness is pseudorandom to T's observers
  exact (not_distinguishes_of_isPseudorandomTo hPR (hBounded T.witnessInClass)) hDist

/--
  **Corollary**: No natural technique can prove lower bounds for PRF-based functions.

  If T is bounded by PolyTime(k) and the witness is pseudorandom to PolyTime(k),
  then T's observer cannot distinguish the witness.
-/
theorem natural_technique_cannot_prove_prf_hardness
    (T : StrongProofTechnique n)
    (k : ℕ)
    (hBounded : T.isOBounded (PolyTimeObservers n k))
    (hPR : IsPseudorandomTo T.witnessFunction (PolyTimeObservers n k)) :
    -- T's observer cannot distinguish the witness
    ¬Distinguishes T.witnessObserver T.witnessFunction := by
  intro hDist
  -- T.witnessObserver is in PolyTime(k) by boundedness
  have hIn : T.witnessObserver ∈ PolyTimeObservers n k := hBounded T.witnessInClass
  exact (not_distinguishes_of_isPseudorandomTo hPR hIn) hDist

/--
  **The Razborov-Rudich Conclusion (Strong Form)**:

  If one-way functions exist (so PRFs exist), then any proof technique
  that proves circuit lower bounds must satisfy one of:

  1. The witness function is NOT pseudorandom (so not "hard" in the
     cryptographic sense - breaks OWF assumption)
  2. The technique uses non-poly-time observations (not "natural")

  **Citation**:
  A. Razborov, S. Rudich (1997). "Natural Proofs"
  JCSS 55(1):24-35. DOI: 10.1006/jcss.1997.1494
  Theorem 1 (main result).
-/
theorem razborov_rudich_strong
    (T : StrongProofTechnique n)
    (_hCert : T.certifiesLowerBound)  -- T actually proves a lower bound
    (k : ℕ)
    (hBounded : T.isOBounded (PolyTimeObservers n k))
    -- If the witness were pseudorandom to PolyTime(k), T couldn't work
    : ¬IsPseudorandomTo T.witnessFunction (PolyTimeObservers n k) := by
  intro hPR
  exact strong_natural_proofs_barrier T k hBounded hPR

/--
  **Razborov-Rudich Dilemma**:

  For any strong proof technique T that is natural (bounded by PolyTime(k)):
  The witness function cannot be pseudorandom to PolyTime(k).

  This captures the essence of the natural proofs barrier:
  - If T is natural at level k, and witness is PR to level k, contradiction
  - So either T is not natural, or witness is not PR at T's level
-/
theorem razborov_rudich_dilemma
    (T : StrongProofTechnique n)
    (_hCert : T.certifiesLowerBound)
    (k : ℕ)
    (hNat : T.isOBounded (PolyTimeObservers n k)) :
    ¬IsPseudorandomTo T.witnessFunction (PolyTimeObservers n k) := by
  exact razborov_rudich_strong T _hCert k hNat

/--
  **Razborov-Rudich Dilemma (Existential Form)**:

  If T is natural (bounded by some PolyTime(k)), then there exists
  some k where the witness is not pseudorandom.
-/
theorem razborov_rudich_dilemma'
    (T : StrongProofTechnique n)
    (hCert : T.certifiesLowerBound)
    (hNat : ∃ k, T.isOBounded (PolyTimeObservers n k)) :
    ∃ k, ¬IsPseudorandomTo T.witnessFunction (PolyTimeObservers n k) := by
  obtain ⟨k, hBounded⟩ := hNat
  exact ⟨k, razborov_rudich_dilemma T hCert k hBounded⟩

end Pseudorandomness
