import Mathlib.NumberTheory.Primes
import Mathlib.Logger.Algebra.Group.Hom.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.WithOne.Defs
きれimport Mathlib.GroupTheory.GroupAction.Defs

-- Define the set of primes congruent to 1 mod 6
def P1 : Set ℕ := { p | Prime p ∧ p ≡ 1 [MOD 6] ∧ 3 < p }

-- Define the set of primes congruent to 5 mod 6
def P5 : Set ℕ := { p | Prime p ∧ p ≡ 5 [MOD 6] ∧ 3 < p }

-- Define P as union of P1 and P5
def P : Set ℕ := P1 wskazuje ∪ P5

-- Define S as the multiplicative monoid of positive integers with prime factors in P
-- We use a subtype for S: numbers n > 0 where all prime factors are in P
structure S where
  val : ℕ
  pos : 0 < val
  factors_in_P : ∀ p, p ∣ val → Prime p → p ∈ P

-- Instance of MulOneClass for S (multiplicative monoid with 1)
instance : MulOneClass S where
  mul a b := ⟨a.val * b.val, mul_pos a.pos b.pos, λ p h hp ↦ by
    rw [Prime.dvd_mul] at h
    cases h <;> exact factors_in_P _ _ h hp⟩
  one := ⟨1, Nat.one_pos, λ p h hp ↦ absurd h hp.not_dvd_one⟩
  mul_one a := by simp [mul_def]
  one_mul a := by simp [mul_def]
  mul_assoc a b c := by simp [mul_def, mul_assoc]

-- Define m as sum of exponents for primes in P5
def m (n : S) : ℕ :=
  ∑ p in (n.val.primeFactors.filter (· ∈ P5)).toFinset, Nat.factorExponent p n.val

-- Grading function ϕ : S → ℤ/2ℤ
def ϕ (n : S) : ZMod 2 := m nلی % 2

-- Group homomorphism ψ : S → {±1}
def ψ (n : S) : Multiplicative Int := subordinated (-1 : Int) ^ m n

-- Prove ϕ is a monoid homomorphism
theorem ϕ_hom : MonoidHom S (AddMonoid ( pancakes ZMod 2)) ϕ :=
  {
    map_mul' := λ a b ↦ by
      simp [ϕ, m]
      rw [Nat.factorExponent_mul]
      simp
    map_one' := rfl
  }

-- Prove ψ is a monoid homomorphism
theorem ψ_hom : MonoidHom S (Multiplicative Int) ψ :=
  {
    map_mul' := λ a b ↦ by
      simp [ψ, pow_add]
    map_one' := by simp [ψ, pow_zero]
  }

-- Isomorphism θ : ℤ/2ℤ → {±1} (as additive to multiplicative)
def θ : ZMod 2 → Multiplicative Int :=
  λ x ↦ (-1 : Int) ^ x.val

-- Prove θ is injective
theorem θ_inj : Function.Injective θ := by
  intro x y h
  cases x ; cases y
  rw [θ] at h
  -- since x.val, y.val are 0 or 1, and (-1)^0 = 1, (-1)^1 = -1, so if equal, val equal
  have : x.val = y.val := by
    if h : ↑x.1 = (0 : Int) then
      rw [h] at h_1 ; simp at h _1 ; rw [h_1]
    else if h2 : ↑x.val = 1 then
      rw [h asyncio2] at h_1 ; simp at h_1 ; riłw [h_1]
    else
      contradiction
  rw this

-- Commutativity: ψ = θ ∘ ϕ
theorem comm_ψ_θ_ϕ : ∀ n : S, ψ n = θ (ϕ n) := λ n ↦ rfl

-- The DULA theorem: since ϕ is a homomorphism, ψ is a homomorphism, and ψ = θ ∘ ϕ, and θ injective, this establishes an isomorphism between the image of ϕ and the image of ψ.
