import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Hom.Monoid
import Mathlib.Tactic
import Mathlib.NumberTheory.PadicValuation.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.ZMod.Basic

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

-- Define multiplication and identity for S to make it a Monoid.
instance : Monoid S where
  mul a b := {
    val := a.val * b.val,
    pos := mul_pos a.pos b.pos,
    factors := by
      intro p hp hpdvd
      have h_dvd_ab : p ∣ a.val * b.val := hpdvd
      rw [Prime.dvd_mul hp] at h_dvd_ab
      cases h_dvd_ab with
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
  mul_one := by intro a; simp [HMul.hMul, Mul.mul]
  one_mul := by intro a; simp [HMul.hMul, Mul.mul]
  mul_assoc := by intro a b c; simp [HMul.hMul, Mul.mul, mul_assoc]


/-- The function m: sum of exponents for primes in P₅. -/
def m (n : S) : ℕ :=
  n.val.factorization.sum fun p k => if p ∈ P₅ then k else 0

/-!
### Section 3: The Homomorphisms and the Theorem
-/

-- The additive group Z/2Z.
abbrev Z2 := ZMod 2

-- The multiplicative group {±1}, represented as units of integers.
abbrev MulZ2 := (Units ℤ)

/-- The grading homomorphism φ: S → ℤ/2ℤ (additive). -/
def phi (n : S) : Z2 :=
  (m n : ℤ)

/-- The homomorphism ψ: S → {±1} (multiplicative). -/
def psi (n : S) : MulZ2 :=
  (-1 : ℤ) ^ (m n)

/-- A crucial lemma about how m behaves under multiplication. -/
lemma m_mul (a b : S) : m (a * b) = m a + m b := by
  simp only [m, Monoid.mul_val, factorization_mul a.pos.ne' b.pos.ne']
  rw [Finsupp.sum_add_index']
  · intro p; simp
  · intro p k₁ k₂; by_cases h : p ∈ P₅ <;> simp [h]

/-- Theorem: φ is a MonoidHom. -/
def phiHom : MonoidHom S Z2 where
  toFun := phi
  map_one' := by simp [phi, m, factorization_one]
  map_mul' a b := by
    simp [phi, m_mul, ZMod.int_cast_add]

/-- Theorem: ψ is a MonoidHom. -/
def psiHom : MonoidHom S MulZ2 where
  toFun := psi
  map_one' := by simp [psi, m, factorization_one, pow_zero]
  map_mul' a b := by simp [psi, m_mul, pow_add]

/-- The isomorphism θ: ZMod 2 → {±1}. -/
def theta : Z2 ≃* MulZ2 where
  toFun z := if z = 0 then 1 else -1
  invFun u := if u = 1 then 0 else 1
  left_inv := by intro z; fin_cases z <;> simp
  right_inv := by intro u; cases u; simp; simp
  map_mul' := by intro z₁ z₂; fin_cases z₁ <;> fin_cases z₂ <;> simp [Z2, ZMod.val]

/-- The DULA Theorem: Commutativity holds, ψ = θ ∘ φ. -/
theorem dula_theorem_commutes (n : S) : psi n = theta (phi n) := by
  simp [psi, phi, theta]
  rw [ZMod.int_cast_eq_int_cast_iff]
  by_cases heven : Even (m n)
  · rw [pow_even heven]
    simp [heven]
  · have hodd : Odd (m n) := Nat.odd_iff_not_even.mpr heven
    rw [pow_odd hodd]
    simp [hodd, Nat.odd_iff]

end DulaTheorem
