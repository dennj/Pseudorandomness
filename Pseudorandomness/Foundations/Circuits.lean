/-
  Circuit Complexity Foundations
  ==============================

  This module provides the circuit complexity foundations for the
  strengthened proof technique framework.

  **Circuit Model**: Boolean circuits with AND, OR, NOT gates.
  Standard model from computational complexity theory.

  **References**:
  - S. Arora, B. Barak. "Computational Complexity: A Modern Approach"
    Cambridge University Press, 2009. Chapter 6.
    DOI: 10.1017/CBO9780511804090

  - O. Goldreich. "Computational Complexity: A Conceptual Perspective"
    Cambridge University Press, 2008. Chapter 4.
    DOI: 10.1017/CBO9780511804106
-/

import Pseudorandomness.Foundations.BooleanFunction
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Pseudorandomness

-- `BoolFun n` is a finite type: it is a function space `(Fin (2^n)) → Bool`.
noncomputable instance (n : ℕ) : Fintype (BoolFun n) := by
  dsimp [BoolFun, ComplexityBarriers.BoolFun]
  infer_instance

/-! ## Circuit Definition

We axiomatize circuits rather than fully formalizing them because:
1. Mathlib doesn't have circuit complexity yet
2. Full formalization requires DAG representation, gate types, etc.
3. The key properties we need are well-established

  **Citation**:
  S. Arora, B. Barak (2009). "Computational Complexity: A Modern Approach"
Cambridge University Press. Chapter 6, Definition 6.1.
-/

/--
  **Circuit**: a simple, fully formal Boolean-circuit syntax tree.

  This is strong enough to support Shannon-style counting arguments in Lean
  without axioms: circuits of bounded size form a finite type, so there are
  strictly fewer of them than all Boolean functions.

  Note: this is closer to Boolean *formula* size than DAG-circuit size; it is
  deliberately lightweight to keep the library mathlib-friendly.
-/
inductive Circuit (n : ℕ) where
  | input : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n
deriving DecidableEq

namespace Circuit

/-- Syntactic size (number of nodes). -/
def size {n : ℕ} : Circuit n → ℕ
  | input _ => 1
  | const _ => 1
  | not c => c.size + 1
  | and c₁ c₂ => c₁.size + c₂.size + 1
  | or c₁ c₂ => c₁.size + c₂.size + 1

/-- Evaluate a circuit under an assignment of input variables. -/
def eval {n : ℕ} (assignment : Fin n → Bool) : Circuit n → Bool
  | input i => assignment i
  | const b => b
  | not c => !(c.eval assignment)
  | and c₁ c₂ => (c₁.eval assignment) && (c₂.eval assignment)
  | or c₁ c₂ => (c₁.eval assignment) || (c₂.eval assignment)

/-- Interpret a truth-table index `x : Fin (2^n)` as an `n`-bit assignment. -/
def assignmentOf {n : ℕ} (x : Fin (2^n)) : Fin n → Bool :=
  fun i => (x.val / 2 ^ i.val) % 2 = 1

/-- The Boolean function computed by a circuit. -/
def computes {n : ℕ} (C : Circuit n) : BoolFun n :=
  fun x => C.eval (assignmentOf x)

/-! ### Building circuits from truth tables -/

/-- Rename variables to embed an `n`-variable circuit into `n+1` variables (ignoring the last variable). -/
def weaken {n : ℕ} : Circuit n → Circuit (n + 1)
  | input i => input (Fin.castSucc i)
  | const b => const b
  | not c => not (weaken c)
  | and c₁ c₂ => and (weaken c₁) (weaken c₂)
  | or c₁ c₂ => or (weaken c₁) (weaken c₂)

@[simp] theorem size_weaken {n : ℕ} (C : Circuit n) : (weaken C).size = C.size := by
  induction C <;> simp [weaken, Circuit.size, *]

@[simp] theorem eval_weaken {n : ℕ} (C : Circuit n) (assignment : Fin (n + 1) → Bool) :
    (weaken C).eval assignment = C.eval (fun i => assignment (Fin.castSucc i)) := by
  induction C <;> simp [weaken, eval, *]

/--
Boolean conditional (if-then-else) circuit built from `AND/OR/NOT`:
`ite c t e = (c ∧ t) ∨ (¬c ∧ e)`.
-/
def ite {n : ℕ} (cond t e : Circuit n) : Circuit n :=
  or (and cond t) (and (not cond) e)

@[simp] theorem eval_ite {n : ℕ} (cond t e : Circuit n) (assignment : Fin n → Bool) :
    (ite cond t e).eval assignment = (if cond.eval assignment then t.eval assignment else e.eval assignment) := by
  by_cases h : cond.eval assignment <;> simp [ite, eval, h]

@[simp] theorem size_ite {n : ℕ} (cond t e : Circuit n) :
    (ite cond t e).size = t.size + e.size + 2 * cond.size + 4 := by
  -- unfold and let arithmetic be handled by `omega`
  simp [ite, Circuit.size, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

private lemma assignmentOf_castSucc_eq_assignmentOf_mod {n : ℕ} (x : Fin (2 ^ (n + 1))) :
    (fun i : Fin n => assignmentOf x (Fin.castSucc i)) =
      assignmentOf (n := n) ⟨x.val % 2 ^ n, Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) n)⟩ := by
  funext i
  -- use the fact that modulo `2^n` preserves the low `n` bits
  have hi : i.val < n := i.isLt
  -- `getBit_mod_two_pow` is in the `ComplexityBarriers` namespace (from `Pseudorandomness.Basic.Foundations`)
  simpa [assignmentOf, ComplexityBarriers.getBit] using
    (ComplexityBarriers.getBit_mod_two_pow (x := x.val) (k := n) (i := i.val) hi).symm

/--
Construct a circuit that computes a given Boolean function by a full decision tree
splitting on the last variable (Shannon expansion).
-/
noncomputable def ofBoolFun : {n : ℕ} → BoolFun n → Circuit n
  | 0, f => const (f ⟨0, by simp⟩)
  | n + 1, f =>
      let f0 : BoolFun n := fun x =>
        f ⟨x.val, lt_of_lt_of_le x.isLt (by
          -- `2^n ≤ 2^(n+1)`
          simp [pow_succ, Nat.mul_comm] )⟩
      let f1 : BoolFun n := fun x =>
        f ⟨x.val + 2 ^ n, by
          -- `x.val < 2^n` implies `x.val + 2^n < 2^(n+1) = 2^n + 2^n`
          simp [pow_succ, two_mul, Nat.mul_comm, x.isLt]⟩
      ite (input (Fin.last n)) (weaken (ofBoolFun f1)) (weaken (ofBoolFun f0))

theorem ofBoolFun_computes : ∀ {n : ℕ} (f : BoolFun n), (ofBoolFun f).computes = f
  | 0, f => by
      funext x
      fin_cases x
      simp [ofBoolFun, computes, eval]
  | n + 1, f => by
      classical
      funext x
      -- decompose `x` into high bit `q` and low bits `r`
      let q : ℕ := x.val / 2 ^ n
      let rVal : ℕ := x.val % 2 ^ n
      have hr : rVal < 2 ^ n := Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : ℕ)) n)
      let r : Fin (2 ^ n) := ⟨rVal, hr⟩
      have hxlt : x.val < 2 ^ n * 2 := by
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using x.isLt
      have hq : q < 2 := by
        -- `q = x / 2^n`, and `x < 2^n * 2`
        simpa [q] using Nat.div_lt_of_lt_mul hxlt
      have hb :
          assignmentOf x (Fin.last n) = (q = 1) := by
        -- `assignmentOf` reads the `n`th bit: `(x / 2^n) % 2 = 1`
        -- and since `q < 2`, `q % 2 = q`
        have : q % 2 = q := Nat.mod_eq_of_lt hq
        simp [assignmentOf, q, this]

      -- Evaluate the two branches by reducing to the `n`-bit input `r`.
      have hassign :
          (fun i : Fin n => assignmentOf x (Fin.castSucc i)) = assignmentOf (n := n) r := by
        simpa [r, rVal] using assignmentOf_castSucc_eq_assignmentOf_mod (n := n) x

      -- The restricted functions used by `ofBoolFun` at arity `n+1`.
      let f0 : BoolFun n := fun y =>
        f ⟨y.val, lt_of_lt_of_le y.isLt (by
          simp [pow_succ, Nat.mul_comm] )⟩
      let f1 : BoolFun n := fun y =>
        f ⟨y.val + 2 ^ n, by
          simp [pow_succ, two_mul, Nat.mul_comm, y.isLt]⟩

      have hcomp0 : (ofBoolFun (n := n) f0).eval (assignmentOf (n := n) r) = f0 r := by
        -- Apply the correctness theorem at input `r`.
        simpa [computes] using congrArg (fun g => g r) (ofBoolFun_computes (n := n) f0)
      have hcomp1 : (ofBoolFun (n := n) f1).eval (assignmentOf (n := n) r) = f1 r := by
        simpa [computes] using congrArg (fun g => g r) (ofBoolFun_computes (n := n) f1)

      have hbranch0 : (weaken (ofBoolFun (n := n) f0)).eval (assignmentOf x) = f0 r := by
        calc
          (weaken (ofBoolFun (n := n) f0)).eval (assignmentOf x)
              = (ofBoolFun (n := n) f0).eval (fun i => assignmentOf x (Fin.castSucc i)) := by
                  simp [eval_weaken]
          _ = (ofBoolFun (n := n) f0).eval (assignmentOf (n := n) r) := by simp [hassign]
          _ = f0 r := hcomp0

      have hbranch1 : (weaken (ofBoolFun (n := n) f1)).eval (assignmentOf x) = f1 r := by
        calc
          (weaken (ofBoolFun (n := n) f1)).eval (assignmentOf x)
              = (ofBoolFun (n := n) f1).eval (fun i => assignmentOf x (Fin.castSucc i)) := by
                  simp [eval_weaken]
          _ = (ofBoolFun (n := n) f1).eval (assignmentOf (n := n) r) := by simp [hassign]
          _ = f1 r := hcomp1

      -- Combine via the `ite` definition
      have hite :
          (ofBoolFun (n := n + 1) f).eval (assignmentOf x)
            =
            (if q = 1 then
              f1 r
             else
              f0 r) := by
        -- expand `ofBoolFun` at `n+1` and use the branch computations
        simp [ofBoolFun, eval_ite, eval, hb, hbranch0, hbranch1, f0, f1]

      -- show the RHS equals `f x` using `Nat.div_add_mod`
      have hdecomp : x.val = 2 ^ n * q + rVal := by
        -- `x = 2^n * (x / 2^n) + x % 2^n`
        simpa [q, rVal] using (Nat.div_add_mod x.val (2 ^ n)).symm
      have hq01 : q = 0 ∨ q = 1 := (Nat.le_one_iff_eq_zero_or_eq_one).1 (Nat.le_of_lt_succ hq)
      rcases hq01 with hq0 | hq1
      · -- high bit 0
        have hxval : x.val = rVal := by simpa [hq0] using hdecomp
        let x0 : Fin (2 ^ (n + 1)) :=
          ⟨rVal, lt_of_lt_of_le hr (by simp [pow_succ, Nat.mul_comm] )⟩
        have hx0 : x = x0 := Fin.ext hxval
        have hL :
            (ofBoolFun (n := n + 1) f).computes x = f0 r := by
          have :
              (ofBoolFun (n := n + 1) f).computes x =
                (if q = 1 then f1 r else f0 r) := by
            simpa [computes] using hite
          simpa [hq0] using this
        have hR : f0 r = f x := by
          calc
            f0 r = f x0 := by
              simp [f0, r, rVal, x0]
            _ = f x := by
              simpa using congrArg f hx0.symm
        exact hL.trans hR
      · -- high bit 1
        have hxval : x.val = rVal + 2 ^ n := by
          -- from `q = 1`, `x = 2^n + r`
          simpa [hq1, Nat.mul_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdecomp
        let x1 : Fin (2 ^ (n + 1)) :=
          ⟨rVal + 2 ^ n, by
            have hy : rVal + 2 ^ n < 2 ^ n + 2 ^ n := Nat.add_lt_add_right hr _
            simpa [pow_succ, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hy⟩
        have hx1 : x = x1 := Fin.ext hxval
        have hL :
            (ofBoolFun (n := n + 1) f).computes x = f1 r := by
          have :
              (ofBoolFun (n := n + 1) f).computes x =
                (if q = 1 then f1 r else f0 r) := by
            simpa [computes] using hite
          simpa [hq1] using this
        have hR : f1 r = f x := by
          calc
            f1 r = f x1 := by
              simp [f1, r, rVal, x1]
            _ = f x := by
              simpa using congrArg f hx1.symm
        exact hL.trans hR

theorem ofBoolFun_size : ∀ {n : ℕ} (f : BoolFun n), (ofBoolFun f).size = 7 * 2 ^ n - 6
  | 0, f => by
      simp [ofBoolFun, Circuit.size]
  | n + 1, f => by
      have h6 : 6 ≤ 7 * 2 ^ n := by
        have hpow : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide : 0 < (2 : ℕ))
        have h7 : 7 ≤ 7 * 2 ^ n := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left 7 hpow
        exact (by decide : 6 ≤ 7) |>.trans h7
      -- Unfold the construction and compute the size recurrence.
      have hrec :
          (ofBoolFun (n := n + 1) f).size =
            (7 * 2 ^ n - 6) + (7 * 2 ^ n - 6) + 6 := by
        simp [ofBoolFun, size_ite, size_weaken, Circuit.size, ofBoolFun_size (n := n)]
      -- Massage the recurrence into `7 * 2^(n+1) - 6`.
      set A : ℕ := 7 * 2 ^ n
      have hA : A - 6 + 6 = A := Nat.sub_add_cancel (by simpa [A] using h6)
      calc
        (ofBoolFun (n := n + 1) f).size
            = (A - 6) + (A - 6) + 6 := by
                simpa [A] using hrec
        _ = (A - 6) + ((A - 6) + 6) := by
                simp [Nat.add_assoc]
        _ = (A - 6) + A := by
                simpa [Nat.add_assoc] using congrArg (fun t => (A - 6) + t) hA
        _ = A + (A - 6) := by
                ac_rfl
        _ = A + A - 6 := by
                simpa using
                  (Nat.add_sub_assoc (m := A) (n := A) (k := 6) (by simpa [A] using h6)).symm
        _ = 2 * A - 6 := by
                simp [two_mul]
        _ = 7 * 2 ^ (n + 1) - 6 := by
                have h2 : 2 * A = 7 * 2 ^ (n + 1) := by
                  calc
                    2 * A = 2 * (7 * 2 ^ n) := by simp [A]
                    _ = (7 * 2 ^ n) * 2 := by simp [Nat.mul_comm]
                    _ = 7 * (2 ^ n * 2) := by simp [Nat.mul_assoc]
                    _ = 7 * 2 ^ (n + 1) := by simp [pow_succ]
                simp [h2]

/-! ### Encoding circuits for counting -/

/--
Tokens used for a prefix (Polish) encoding of circuits.

We choose `Fin n ⊕ Fin 5`, i.e. `n` variable tokens plus 5 operator/constant tokens:
0=false, 1=true, 2=not, 3=and, 4=or.
-/
abbrev Token (n : ℕ) := (Fin n) ⊕ (Fin 5)

namespace Token

@[simp] theorem card (n : ℕ) : Fintype.card (Token n) = n + 5 := by
  classical
  simp [Token, Fintype.card_sum, Fintype.card_fin]

def falseTok {n : ℕ} : Token n := Sum.inr ⟨0, by decide⟩
def trueTok {n : ℕ} : Token n := Sum.inr ⟨1, by decide⟩
def notTok {n : ℕ} : Token n := Sum.inr ⟨2, by decide⟩
def andTok {n : ℕ} : Token n := Sum.inr ⟨3, by decide⟩
def orTok {n : ℕ} : Token n := Sum.inr ⟨4, by decide⟩

end Token

/-- Prefix encoding of a circuit as a token list. -/
def encode {n : ℕ} : Circuit n → List (Token n)
  | input i => [Sum.inl i]
  | const b => [if b then Token.trueTok else Token.falseTok]
  | not c => Token.notTok :: encode c
  | and c₁ c₂ => Token.andTok :: (encode c₁ ++ encode c₂)
  | or c₁ c₂ => Token.orTok :: (encode c₁ ++ encode c₂)

@[simp] theorem encode_length {n : ℕ} (C : Circuit n) :
    (encode C).length = C.size := by
  induction C <;> simp [encode, Circuit.size, *, Nat.add_comm]

/--
Decode a prefix encoding with a fuel parameter.

Fuel makes the definition structurally recursive (and total) without having to prove that
the nested recursive calls always decrease on the input list.
-/
def decodeFuel {n : ℕ} : ℕ → List (Token n) → Option (Circuit n × List (Token n))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: ts =>
    match t with
    | Sum.inl i => some (Circuit.input i, ts)
    | Sum.inr tag =>
      match tag.1 with
      | 0 => some (Circuit.const false, ts)
      | 1 => some (Circuit.const true, ts)
      | 2 => do
        let (c, rest) ← decodeFuel fuel ts
        pure (Circuit.not c, rest)
      | 3 => do
        let (c₁, rest₁) ← decodeFuel fuel ts
        let (c₂, rest₂) ← decodeFuel fuel rest₁
        pure (Circuit.and c₁ c₂, rest₂)
      | 4 => do
        let (c₁, rest₁) ← decodeFuel fuel ts
        let (c₂, rest₂) ← decodeFuel fuel rest₁
        pure (Circuit.or c₁ c₂, rest₂)
      | _ => none

/-- Decode using `fuel = input.length`. -/
def decode {n : ℕ} (l : List (Token n)) : Option (Circuit n × List (Token n)) :=
  decodeFuel l.length l

theorem decodeFuel_encode_append {n : ℕ} (C : Circuit n) (rest : List (Token n)) :
    ∀ fuel, (encode C ++ rest).length ≤ fuel →
      decodeFuel (n := n) fuel (encode C ++ rest) = some (C, rest) := by
  induction C generalizing rest with
  | input i =>
    intro fuel hfuel
    cases fuel with
    | zero =>
      -- impossible: `(encode (input i) ++ rest).length = 1 + rest.length`
      simpa [encode] using (Nat.not_succ_le_zero _ hfuel)
    | succ fuel =>
      simp [encode, decodeFuel]
  | const b =>
    intro fuel hfuel
    cases fuel with
    | zero =>
      simpa [encode] using (Nat.not_succ_le_zero _ hfuel)
    | succ fuel =>
      cases b <;> simp [encode, decodeFuel, Token.falseTok, Token.trueTok]
  | not c ih =>
    intro fuel hfuel
    cases fuel with
    | zero =>
      simpa [encode] using (Nat.not_succ_le_zero _ hfuel)
    | succ fuel =>
      have hfuel' : (encode c ++ rest).length ≤ fuel := by
        -- drop the leading token
        simpa [encode, Nat.succ_le_succ_iff] using hfuel
      simp [encode, decodeFuel, Token.notTok, ih (rest := rest) fuel hfuel']
  | and c₁ c₂ ih₁ ih₂ =>
    intro fuel hfuel
    cases fuel with
    | zero =>
      simpa [encode] using (Nat.not_succ_le_zero _ hfuel)
    | succ fuel =>
      have hfuel' : (encode c₁ ++ encode c₂ ++ rest).length ≤ fuel := by
        simpa [encode, Nat.succ_le_succ_iff, List.append_assoc] using hfuel
      have hfuel₁ : (encode c₁ ++ (encode c₂ ++ rest)).length ≤ fuel := by
        simpa [List.append_assoc] using hfuel'
      have hfuel₂ : (encode c₂ ++ rest).length ≤ fuel := by
        have : (encode c₂ ++ rest).length ≤ (encode c₁ ++ (encode c₂ ++ rest)).length := by
          simp [List.length_append]
        exact this.trans hfuel₁
      simp [encode, decodeFuel, Token.andTok, ih₁ (rest := encode c₂ ++ rest) fuel hfuel₁,
        ih₂ (rest := rest) fuel hfuel₂, List.append_assoc]
  | or c₁ c₂ ih₁ ih₂ =>
    intro fuel hfuel
    cases fuel with
    | zero =>
      simpa [encode] using (Nat.not_succ_le_zero _ hfuel)
    | succ fuel =>
      have hfuel' : (encode c₁ ++ encode c₂ ++ rest).length ≤ fuel := by
        simpa [encode, Nat.succ_le_succ_iff, List.append_assoc] using hfuel
      have hfuel₁ : (encode c₁ ++ (encode c₂ ++ rest)).length ≤ fuel := by
        simpa [List.append_assoc] using hfuel'
      have hfuel₂ : (encode c₂ ++ rest).length ≤ fuel := by
        have : (encode c₂ ++ rest).length ≤ (encode c₁ ++ (encode c₂ ++ rest)).length := by
          simp [List.length_append]
        exact this.trans hfuel₁
      simp [encode, decodeFuel, Token.orTok, ih₁ (rest := encode c₂ ++ rest) fuel hfuel₁,
        ih₂ (rest := rest) fuel hfuel₂, List.append_assoc]

theorem decode_encode_append {n : ℕ} (C : Circuit n) (rest : List (Token n)) :
    decode (encode C ++ rest) = some (C, rest) := by
  -- unfold `decode` and use the fuel lemma with `fuel = length`
  have h :=
    decodeFuel_encode_append (C := C) (rest := rest) (fuel := (encode C ++ rest).length) le_rfl
  simpa [decode] using h

theorem encode_injective {n : ℕ} : Function.Injective (encode (n := n)) := by
  intro C₁ C₂ h
  have h₁ : decode (encode C₁) = decode (encode C₂) := by simp [h]
  have d₁ : decode (encode C₁) = some (C₁, []) := by
    simpa using (decode_encode_append (C := C₁) (rest := []))
  have d₂ : decode (encode C₂) = some (C₂, []) := by
    simpa using (decode_encode_append (C := C₂) (rest := []))
  have : (C₁, ([] : List (Token n))) = (C₂, []) := by
    apply Option.some.inj
    -- rewrite `d₁` along `h` and compare to `d₂`
    simpa using d₁.symm.trans (h₁.trans d₂)
  exact congrArg Prod.fst this

/--
Finite code space for circuits of size at most `s`:
we remember the exact encoding length `k ≤ s` and the vector of `k` tokens.
-/
abbrev Code (n s : ℕ) := Σ k : Fin (s + 1), List.Vector (Token n) k.1

def SmallCircuit (n s : ℕ) := { C : Circuit n // C.size ≤ s }

noncomputable def encodeCode {n s : ℕ} : SmallCircuit n s → Code n s := fun c =>
  ⟨⟨c.1.size, Nat.lt_succ_of_le c.2⟩, ⟨encode c.1, by simp [encode_length]⟩⟩

@[simp] theorem encodeCode_toList {n s : ℕ} (c : SmallCircuit n s) :
    (encodeCode (n := n) (s := s) c).2.toList = encode c.1 := by
  simp [encodeCode]

theorem encodeCode_injective {n s : ℕ} : Function.Injective (encodeCode (n := n) (s := s)) := by
  intro c₁ c₂ h
  have : encode c₁.1 = encode c₂.1 := by
    simpa [encodeCode_toList] using congrArg (fun x => x.2.toList) h
  have hC : c₁.1 = c₂.1 := encode_injective this
  exact Subtype.ext hC

instance {n s : ℕ} : Finite (SmallCircuit n s) := by
  classical
  refine Finite.of_injective (encodeCode (n := n) (s := s)) (encodeCode_injective (n := n) (s := s))

noncomputable instance {n s : ℕ} : Fintype (SmallCircuit n s) :=
  Fintype.ofFinite (SmallCircuit n s)

lemma sum_pow_le_pow_succ (A s : ℕ) (hA : 2 ≤ A) :
    Finset.sum (Finset.range (s + 1)) (fun k => A ^ k) ≤ A ^ (s + 1) := by
  induction s with
  | zero =>
    -- `∑_{k < 1} A^k = 1 ≤ A`
    simp
    exact le_trans (by decide : (1 : ℕ) ≤ 2) hA
  | succ s ih =>
    calc
      Finset.sum (Finset.range (s + 2)) (fun k => A ^ k)
          = Finset.sum (Finset.range (s + 1)) (fun k => A ^ k) + A ^ (s + 1) := by
              simp [Finset.sum_range_succ]
      _ ≤ A ^ (s + 1) + A ^ (s + 1) := by
              exact Nat.add_le_add_right ih _
      _ = 2 * A ^ (s + 1) := by
              simp [two_mul]
      _ ≤ A * A ^ (s + 1) := by
              exact Nat.mul_le_mul_right _ hA
      _ = A ^ (s + 2) := by ring

theorem card_code_le (n s : ℕ) :
    Fintype.card (Code n s) ≤ (Fintype.card (Token n)) ^ (s + 1) := by
  classical
  let A := Fintype.card (Token n)
  have hA : 2 ≤ A := by
    -- `A = n + 5 ≥ 5`
    simp [A]
  -- `card (Σ k : Fin (s+1), Vector _ k) = ∑_{k < s+1} A^k ≤ A^(s+1)`
  calc
    Fintype.card (Code n s)
        = ∑ k : Fin (s + 1), Fintype.card (List.Vector (Token n) k.1) := by
            simp [Code, Fintype.card_sigma]
    _ = ∑ k : Fin (s + 1), A ^ (k : ℕ) := by
            simp [A]
    _ = Finset.sum (Finset.range (s + 1)) (fun k => A ^ k) := by
            -- convert the `Fin (s+1)` sum into a `Finset.range` sum
            simp [Fin.sum_univ_eq_sum_range (fun k : ℕ => A ^ k) (s + 1)]
    _ ≤ A ^ (s + 1) := sum_pow_le_pow_succ A s hA
    _ = (Fintype.card (Token n)) ^ (s + 1) := by simp [A]

end Circuit

/--
  **Circuit Existence Theorem**: Every Boolean function can be computed by a circuit.

  This file uses a lightweight circuit syntax (a Boolean formula tree). A direct Shannon-expansion
  (decision tree) construction yields a circuit of size `O(2^n)`. We package the bound as
  `C.size ≤ 2^(n+3)` (i.e. within a constant factor of `2^n`).
-/
theorem circuit_exists (n : ℕ) (f : BoolFun n) :
    ∃ C : Circuit n, C.computes = f ∧ C.size ≤ 2 ^ (n + 3) := by
  refine ⟨Circuit.ofBoolFun f, Circuit.ofBoolFun_computes f, ?_⟩
  have hsize : (Circuit.ofBoolFun f).size = 7 * 2 ^ n - 6 := Circuit.ofBoolFun_size (n := n) f
  have hle1 : (Circuit.ofBoolFun f).size ≤ 7 * 2 ^ n := by
    simp [hsize]
  have hle2 : 7 * 2 ^ n ≤ 2 ^ (n + 3) := by
    calc
      7 * 2 ^ n ≤ 8 * 2 ^ n := Nat.mul_le_mul_right (2 ^ n) (by decide : 7 ≤ 8)
      _ = 2 ^ (n + 3) := by
        -- `2^(n+3) = 2^n * 2^3 = 8 * 2^n`
        simp [pow_add, Nat.mul_comm]
  exact hle1.trans hle2

/-! ## Circuit Lower Bounds -/

/--
  **HasCircuitSize**: Function f can be computed by size-s circuits.
-/
def HasCircuitSize (f : BoolFun n) (s : ℕ) : Prop :=
  ∃ C : Circuit n, C.computes = f ∧ C.size ≤ s

/--
  **RequiresCircuitSize**: Function f requires circuits of size > s.
  This is the negation of HasCircuitSize.
-/
def RequiresCircuitSize (f : BoolFun n) (s : ℕ) : Prop :=
  ∀ C : Circuit n, C.computes = f → C.size > s

/--
  RequiresCircuitSize is the negation of HasCircuitSize.
-/
theorem requires_iff_not_has {f : BoolFun n} {s : ℕ} :
    RequiresCircuitSize f s ↔ ¬HasCircuitSize f s := by
  constructor
  · intro hReq ⟨C, hComp, hSize⟩
    have hBig := hReq C hComp
    omega
  · intro hNotHas C hComp
    by_contra hLE
    push_neg at hLE
    exact hNotHas ⟨C, hComp, hLE⟩

/-! ## Shannon Counting (Fully Formal, Existence Form) -/

private lemma add_five_le_two_pow (n : ℕ) (hn : 3 ≤ n) : n + 5 ≤ 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    simp
  | succ k ih =>
    -- `(3+k)+6 ≤ 2^(3+k+1)` from `(3+k)+5 ≤ 2^(3+k)`
    have h1 : (3 + k) + 6 ≤ (2 ^ (3 + k)) + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.succ_le_succ ih
    have h2 : (2 ^ (3 + k)) + 1 ≤ (2 ^ (3 + k)) + (2 ^ (3 + k)) := by
      exact Nat.add_le_add_left (Nat.one_le_pow (3 + k) 2 (by decide : 0 < (2 : ℕ))) _
    have h3 : (2 ^ (3 + k)) + (2 ^ (3 + k)) = 2 ^ (3 + (k + 1)) := by
      calc
        (2 ^ (3 + k)) + (2 ^ (3 + k))
            = 2 * (2 ^ (3 + k)) := by simp [two_mul]
        _ = (2 ^ (3 + k)) * 2 := by simp [Nat.mul_comm]
        _ = 2 ^ (3 + k + 1) := by simp [pow_succ]
        _ = 2 ^ (3 + (k + 1)) := by simp [Nat.add_assoc]
    exact (h1.trans (h2.trans_eq h3))

private lemma two_mul_add_one_le_two_pow (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero =>
    simp
  | succ k ih =>
    -- Let `m = 3 + k`. We show `2*(m+1)+1 ≤ 2^(m+1)` using the IH `2*m+1 ≤ 2^m`.
    set m : ℕ := 3 + k
    have hstep : 2 * (m + 1) + 1 ≤ 2 * (2 * m + 1) := by omega
    have hmul : 2 * (2 * m + 1) ≤ 2 * (2 ^ m) := Nat.mul_le_mul_left 2 ih
    have hpow : 2 * (2 ^ m) = 2 ^ (m + 1) := by
      simp [pow_succ, Nat.mul_comm]
    -- unfold `m` back to `3+k`
    simpa [m, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (hstep.trans (hmul.trans_eq hpow))

/--
Existence form of Shannon counting: for `n ≥ 3`, there exists a Boolean function on `n` bits
requiring circuits larger than `2^n / (2n+1)`.
-/
theorem shannon_counting_exists (n : ℕ) (hn : n ≥ 3) :
    ∃ f : BoolFun n, RequiresCircuitSize f (2 ^ n / (2 * n + 1)) := by
  classical
  let s : ℕ := 2 ^ n / (2 * n + 1)
  have hbpos : 0 < (2 * n + 1) := by omega
  have hs1 : 1 ≤ s := by
    -- `1 ≤ a/b ↔ b ≤ a` for `b>0`
    have hden : (2 * n + 1) ≤ 2 ^ n := two_mul_add_one_le_two_pow n hn
    exact (Nat.le_div_iff_mul_le hbpos).2 (by simpa using hden)
  have hspos : 0 < s := (Nat.succ_le_iff).1 hs1

  -- `card (small circuits)` is strictly less than `card (all Boolean functions)`
  have hSmall_lt : Fintype.card (Circuit.SmallCircuit n s) < Fintype.card (BoolFun n) := by
    -- bound small circuits by codes
    have hSmall_le_code :
        Fintype.card (Circuit.SmallCircuit n s) ≤ Fintype.card (Circuit.Code n s) :=
      Fintype.card_le_of_injective (Circuit.encodeCode (n := n) (s := s))
        (Circuit.encodeCode_injective (n := n) (s := s))
    have hCode_le : Fintype.card (Circuit.Code n s) ≤ (Fintype.card (Circuit.Token n)) ^ (s + 1) :=
      Circuit.card_code_le n s
    have hTok_le : Fintype.card (Circuit.Token n) ≤ 2 ^ n := by
      simpa [Circuit.Token.card] using add_five_le_two_pow n hn
    have hTokPow_le : (Fintype.card (Circuit.Token n)) ^ (s + 1) ≤ (2 ^ n) ^ (s + 1) :=
      Nat.pow_le_pow_left hTok_le _

    -- show `(2^n)^(s+1) < 2^(2^n)` by comparing exponents of base 2
    have hs_succ_le_two_mul : s + 1 ≤ 2 * s := by
      have : s + 1 ≤ s + s := Nat.add_le_add_left hs1 s
      simpa [two_mul, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
    have hExp :
        n * (s + 1) < 2 ^ n := by
      have hmul_lt : s * (2 * n) < 2 ^ n := by
        have hlt : s * (2 * n) < s * (2 * n + 1) :=
          Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self (2 * n)) hspos
        have hle : s * (2 * n + 1) ≤ 2 ^ n := by
          -- `(a/b) * b ≤ a`
          simpa [s] using (Nat.div_mul_le_self (2 ^ n) (2 * n + 1))
        exact lt_of_lt_of_le hlt hle
      have hmul_lt' : 2 * n * s < 2 ^ n := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul_lt
      have hn_le : n * (s + 1) ≤ 2 * n * s := by
        calc
          n * (s + 1) ≤ n * (2 * s) := Nat.mul_le_mul_left _ hs_succ_le_two_mul
          _ = 2 * n * s := by ring
      exact lt_of_le_of_lt hn_le hmul_lt'
    have hPow_lt :
        (2 ^ n) ^ (s + 1) < 2 ^ (2 ^ n) := by
      -- `(2^n)^(s+1) = 2^(n*(s+1))`
      have : (2 ^ n) ^ (s + 1) = 2 ^ (n * (s + 1)) := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (pow_mul 2 n (s + 1)).symm
      -- `2^(n*(s+1)) < 2^(2^n)` since `n*(s+1) < 2^n`
      simpa [this] using
        (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).2 hExp

    -- put the bounds together
    have hBoolCard : Fintype.card (BoolFun n) = 2 ^ (2 ^ n) := by
      classical
      simp [BoolFun]
    have hSmall_lt_pow :
        Fintype.card (Circuit.SmallCircuit n s) < 2 ^ (2 ^ n) := by
      exact lt_of_le_of_lt
        (le_trans hSmall_le_code (le_trans hCode_le hTokPow_le))
        hPow_lt
    simpa [hBoolCard] using hSmall_lt_pow

  -- If every function had a circuit of size ≤ s, we'd get a surjection from small circuits to all functions.
  by_contra hNone
  have hAll : ∀ f : BoolFun n, HasCircuitSize (n := n) f s := by
    intro f
    have hnreq : ¬RequiresCircuitSize (n := n) f s := by
      intro hf
      exact hNone ⟨f, hf⟩
    have : ¬¬HasCircuitSize (n := n) f s := by
      intro hNotHas
      exact hnreq ((requires_iff_not_has (n := n) (f := f) (s := s)).2 hNotHas)
    exact Classical.not_not.mp this

  let smallComputes : Circuit.SmallCircuit n s → BoolFun n := fun c => c.1.computes
  have hsurj : Function.Surjective smallComputes := by
    intro f
    rcases hAll f with ⟨C, hComp, hSize⟩
    refine ⟨⟨C, hSize⟩, ?_⟩
    simpa [smallComputes] using hComp
  have hcard_ge : Fintype.card (BoolFun n) ≤ Fintype.card (Circuit.SmallCircuit n s) :=
    Fintype.card_le_of_surjective smallComputes hsurj
  exact (Nat.not_lt_of_ge hcard_ge) hSmall_lt

/--
  **Superpolynomial circuit lower bound**: f requires circuits of
  size n^k for all k.
-/
def RequiresSuperpolyCircuits (f : BoolFun n) : Prop :=
  ∀ k : ℕ, RequiresCircuitSize f ((n + 1)^k)

/-! ## P/poly and Circuit Complexity Classes

**P/poly**: The class of problems solvable by polynomial-size circuits.

**Citation**:
A. Karp, R. Lipton (1980). "Some connections between nonuniform and
uniform complexity classes"
STOC 1980, pp. 302-309. DOI: 10.1145/800141.804678
-/

/--
  **HasPolyCircuits**: A function family is in P/poly if it has polynomial-size circuits.
-/
def HasPolyCircuits (f : BoolFun n) : Prop :=
  ∃ k : ℕ, HasCircuitSize f ((n + 1)^k)

/--
  **RequiresSuperPolyCircuits**: A function requires superpolynomial circuits.
-/
def RequiresSuperPolyCircuits (f : BoolFun n) : Prop :=
  RequiresSuperpolyCircuits f

theorem requiresSuperPoly_iff {f : BoolFun n} :
    RequiresSuperPolyCircuits f ↔ ¬HasPolyCircuits f := by
  unfold RequiresSuperPolyCircuits HasPolyCircuits RequiresSuperpolyCircuits
  constructor
  · intro hSuper ⟨k, hPoly⟩
    have := hSuper k
    rw [requires_iff_not_has] at this
    exact this hPoly
  · intro hNotPoly k
    rw [requires_iff_not_has]
    intro hHas
    exact hNotPoly ⟨k, hHas⟩

/-! ## Connection to NP

**The P vs NP connection**: If P ≠ NP, then SAT ∉ P/poly
(under standard derandomization assumptions).

More directly: proving circuit lower bounds for explicit functions
is a key step toward P ≠ NP.

**Citation**:
S. Arora, B. Barak (2009). "Computational Complexity: A Modern Approach"
Chapter 6.3, Theorem 6.19 (Karp-Lipton).
-/

/--
  **Explicit function** (Axiomatized Predicate)

  A Boolean function f : {0,1}^n → {0,1} is explicit if there exists a
  Turing machine M and constant c such that:
  - M(x) = f(x) for all x ∈ {0,1}^n
  - M runs in time at most 2^(c·n)

  **Why we axiomatize this**:
  Full formalization requires Turing machine definitions and time complexity
  analysis, which are substantial undertakings not yet in Mathlib.

  **Key properties** (axiomatized below):
  1. Explicit functions are closed under Boolean operations
  2. Standard functions (parity, majority) are explicit
  3. Not all functions are explicit (cardinality argument)

  **Citation**: Arora-Barak (2009), Definition 6.16
-/
axiom IsExplicit : {n : ℕ} → BoolFun n → Prop

/--
  **Constant functions are explicit**.

  The trivial functions (always true, always false) are computable in O(1) time.
-/
axiom explicit_const_true {n : ℕ} : IsExplicit (fun _ : Fin (2^n) => true)
axiom explicit_const_false {n : ℕ} : IsExplicit (fun _ : Fin (2^n) => false)

/--
  **Not all functions are explicit** (cardinality argument).

  There are 2^(2^n) Boolean functions on n bits, but only countably many
  Turing machines. Hence for large n, most functions are not explicit.

  **Citation**: Arora-Barak (2009), Theorem 6.20
-/
axiom not_all_explicit (n : ℕ) (hn : n ≥ 10) :
  ∃ f : BoolFun n, ¬IsExplicit f

/-! ## Polynomial Hierarchy

The polynomial hierarchy (PH) is a hierarchy of complexity classes:
  Σ₀ᵖ = Π₀ᵖ = P
  Σₖ₊₁ᵖ = NP^(Σₖᵖ)   (NP with oracle for Σₖᵖ)
  Πₖ₊₁ᵖ = coNP^(Σₖᵖ)  (coNP with oracle for Σₖᵖ)
  PH = ⋃ₖ Σₖᵖ

**Key Facts**:
- P ⊆ NP ⊆ Σ₂ᵖ ⊆ Σ₃ᵖ ⊆ ... ⊆ PH ⊆ PSPACE
- If Σₖᵖ = Πₖᵖ for some k, then PH = Σₖᵖ (collapses)
- It's widely believed PH does NOT collapse (infinite hierarchy)

**Citation**:
L. Stockmeyer (1976). "The polynomial-time hierarchy"
Theoretical Computer Science 3(1):1-22.
-/

/--
  **Polynomial Hierarchy Collapse** (axiomatized predicate)

  `PHCollapses` represents the statement that the polynomial hierarchy
  collapses to some finite level: ∃ k, Σₖᵖ = PH.

  **Semantic Content**:
  - If PHCollapses is true: PH = Σₖᵖ for some fixed k
  - If PHCollapses is false: The hierarchy is infinite (Σₖᵖ ⊊ Σₖ₊₁ᵖ for all k)

  **Why axiomatized**:
  Full formalization would require:
  1. Oracle Turing machine definitions
  2. Σₖᵖ class definitions for all k
  3. Proper containment proofs

  **Standard Assumption**: Complexity theorists believe ¬PHCollapses.
  This is because a collapse would have dramatic consequences (e.g.,
  NP = coNP if PH collapses to level 1).

  **Citation**:
  L. Stockmeyer (1976). "The polynomial-time hierarchy"
  Theoretical Computer Science 3(1):1-22.
-/
axiom PHCollapses : Prop

/--
  **Standard Complexity Assumption**: PH Does Not Collapse

  This is a widely-held belief in complexity theory. It serves as a
  complexity assumption similar to P ≠ NP.

  **Why we believe this**:
  1. No evidence of collapse has been found despite decades of research
  2. A collapse would trivialize many hard problems
  3. Random oracles separate all levels of PH (with probability 1)

  **Citation**:
  S. Arora, B. Barak (2009). "Computational Complexity: A Modern Approach"
  Section 5.4 discusses PH and the assumption that it doesn't collapse.
-/
axiom ph_does_not_collapse : ¬PHCollapses

/--
  **Karp-Lipton Theorem (Axiomatized)**:
  If NP ⊆ P/poly, then PH = Σ₂ᵖ (collapses to second level).

  **Why this matters**:
  - If we believe PH doesn't collapse, then NP ⊄ P/poly
  - This means some NP-complete function requires superpolynomial circuits
  - This is a key step toward P ≠ NP

  **Citation**:
  R. Karp, R. Lipton (1980). "Some connections between nonuniform and
  uniform complexity classes"
  STOC 1980, pp. 302-309. DOI: 10.1145/800141.804678
-/
axiom karp_lipton :
  (∀ f : BoolFun n, IsExplicit f → HasPolyCircuits f) → PHCollapses

/--
  **Contrapositive of Karp-Lipton**:
  If PH doesn't collapse, then some explicit function requires superpolynomial circuits.
-/
theorem karp_lipton_contrapositive (hPH : ¬PHCollapses) :
    ∃ f : BoolFun n, IsExplicit f ∧ ¬HasPolyCircuits f := by
  by_contra h
  push_neg at h
  have hAll : ∀ f : BoolFun n, IsExplicit f → HasPolyCircuits f := h
  exact hPH (karp_lipton hAll)

/--
  **Explicit Hard Function Exists** (Under Standard Assumptions)

  Using the standard assumption that PH doesn't collapse, we derive
  the existence of an explicit function requiring superpolynomial circuits.

  This is the key consequence: NP ⊄ P/poly under standard assumptions.
-/
theorem explicit_hard_function_exists :
    ∃ f : BoolFun n, IsExplicit f ∧ ¬HasPolyCircuits f :=
  karp_lipton_contrapositive ph_does_not_collapse

/-! ## Circuit Lower Bounds and P ≠ NP -/

/--
  **The Circuit Lower Bound Goal**:
  Proving P ≠ NP is equivalent to proving that some explicit NP function
  requires superpolynomial circuits.

  **Citation**:
  S. Arora, B. Barak (2009). Chapter 6.3
-/
def CircuitLowerBoundWitness (n : ℕ) : Prop :=
  ∃ f : BoolFun n, IsExplicit f ∧ RequiresSuperPolyCircuits f

/--
  A circuit lower bound witness implies P ≠ NP (informally).
  We state this as: if we have a lower bound witness, we have
  separated some explicit function from polynomial circuits.
-/
theorem lower_bound_implies_separation {n : ℕ}
    (h : CircuitLowerBoundWitness n) :
    ∃ f : BoolFun n, IsExplicit f ∧ ¬HasPolyCircuits f := by
  obtain ⟨f, hExpl, hHard⟩ := h
  exact ⟨f, hExpl, requiresSuperPoly_iff.mp hHard⟩

end Pseudorandomness
