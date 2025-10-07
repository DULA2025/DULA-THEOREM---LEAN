import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Hom.Monoid
import Mathlib.Tactic
import Mathlib.NumberTheory.PadicValuation.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Equiv.Basic

-- We work with natural numbers for simplicity.
open Nat

namespace DulaTheorem

/-!
### Section 1: Preliminaries and Definitions
We define the sets of primes and the monoid S.
-/

-- Define primes congruent to 1 mod 6
def P₁ : Set ℕ := { p | Prime p ∧ p ≡ 1 [MOD 6] }

-- Define primes congruent to 5 mod 6
def P₅ : Set ℕ := { p | Prime p ∧ p ≡ 5 [MOD 6] }

-- Union P = P₁ ∪ P₅, which are all primes not dividing 6.
def P : Set ℕ := P₁ ∪ P₅

/-- The monoid S: positive integers whose prime factors are all in P. -/
structure S where
  val : ℕ
  pos : val > 0
  factors : ∀ {p : ℕ}, p.Prime → p ∣ val → p ∈ P

/-!
### Section 2: Monoid Structure and Helper Functions
-/

-- Auxiliary definition for -1 as a unit in ℤ
lemma isUnit_neg_one : IsUnit (-1 : ℤ) := ⟨-1, neg_neg.symm⟩

def negOneUnit : Units ℤ := ⟨-1, isUnit_neg_one⟩

-- Define multiplication and identity for S to make it a Monoid.
@[simp] lemma val_mul (a b : S) : (a * b).val = a.val * b.val := rfl

instance : Monoid S where
  mul a b := {
    val := a.val * b.val,
    pos := mul_pos a.pos b.pos,
    factors := by
      intro p hp hpdvd
      rw [← val_mul] at hpdvd
      rw [Prime.dvd_mul hp] at hpdvd
      cases hpdvd with
      | inl ha => exact a.factors hp ha
      | inr hb => exact b.factors hp hb
  }
  one := {
    val := 1,
    pos := by simp,
    factors := by
      intro p hp hpdvd
      simp at hpdvd
      exact (hp.ne_one (Eq.symm hpdvd)).elim
  }
  mul_one := by intro a; simp [Mul.mul]
  one_mul := by intro a; simp [Mul.mul]
  mul_assoc := by intro a b c; simp [Mul.mul, mul_assoc]

/-- The function m: sum of exponents for primes in P₅. -/
def m (n : S) : ℕ :=
  n.val.factorization.sum fun p k => if p ∈ P₅ then k else 0

/-!
### Section 3: The Homomorphisms and the Theorem
-/

-- The additive group ℤ/2ℤ, via the Additive functor.
abbrev AddZ₂ := Additive (ZMod 2)

-- The multiplicative group {±1}, represented as units of integers.
abbrev MulZ₂ := Units ℤ

/-- The grading homomorphism φ: S → ℤ/2ℤ (additive). -/
def phi (n : S) : AddZ₂ :=
  (m n : ZMod 2)

/-- The homomorphism ψ: S → {±1} (multiplicative). -/
def psi (n : S) : MulZ₂ :=
  negOneUnit ^ m n

/-- A crucial lemma about how m behaves under multiplication. -/
lemma m_mul (a b : S) : m (a * b) = m a + m b := by
  simp only [m, val_mul, factorization_mul a.pos.ne' b.pos.ne']
  rw [Finsupp.sum_add_index]
  rfl

/-- Theorem: φ is a MonoidHom. -/
def phiHom : MonoidHom S AddZ₂ where
  toFun := phi
  map_one' := by simp [phi, m, factorization_one]
  map_mul' a b := by
    simp [phi, m_mul, Additive.mul_def, ZMod.int_cast_add]

/-- Theorem: ψ is a MonoidHom. -/
def psiHom : MonoidHom S MulZ₂ where
  toFun := psi
  map_one' := by simp [psi, m, factorization_one, pow_zero]
  map_mul' a b := by simp [psi, m_mul, pow_add]

/-- The isomorphism θ: ℤ/2ℤ → {±1}. -/
def theta : AddZ₂ ≃* MulZ₂ where
  toFun z := if (z : ZMod 2) = 0 then 1 else negOneUnit
  invFun u := if u = 1 then 0 else 1
  left_inv := by
    intro z
    simp [theta, Additive.coe_eq_coe]
    fin_cases (z : ZMod 2)
    · rfl
    · rfl
  right_inv := by
    intro u
    simp [theta]
    by_cases h : u = 1
    · simp [h]
    · simp only [dif_neg h, if_neg (by norm_num)]
      rw [← Units.ext]
      simp [Int.is_unit_iff.mp u.2, h]
  map_mul' := by
    intro x y
    simp [theta, Additive.mul_def]
    fin_cases (x : ZMod 2)
    · fin_cases (y : ZMod 2)
      · simp
      · simp
    · fin_cases (y : ZMod 2)
      · simp
      · simp

/-- The DULA Theorem: Commutativity holds, ψ = θ ∘ φ. -/
theorem dula_theorem_commutes (n : S) : psi n = theta (phi n) := by
  simp only [psi, phi, theta, Additive.coe_eq_coe, Equiv.toFun_apply]
  rw [ZMod.two_nat_cast_eq_zero_iff]
  by_cases heven : Even (m n)
  · rw [if_pos heven]
    rw [pow_even heven, pow_mul, sq]
    simp [negOneUnit]
  · have hodd : Odd (m n) := Nat.odd_iff_not_even.mpr heven
    rw [if_neg heven, pow_odd hodd, pow_mul, sq]
    simp [negOneUnit]

end DulaTheorem
