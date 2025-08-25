import Mathlib.NumberTheory.Primes
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.GroupTheory.GroupAction.Defs

-- Define the set of primes congruent to 1 mod 6
def P1 : Set ℕ := { p | Prime p ∧ p ≡ 1 [MOD 6] ∧ 3 < p }

-- Define the set of primes congruent to 5 mod 6
def P5 : Set ℕ := { p | Prime p ∧ p ≡ 5 [MOD 6] ∧ 3 < p }

-- Define P as union of P1 and P5
def P : Set ℕ := P1 ∪ P5

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
  ∑ p in (n.val.primeFactors.filter (· ∈ P5)).toFinset, n.val.factorOrderOfPrime p

-- Grading function ϕ : S → ℤ/2ℤ
def ϕ (n : S) : ZMod 2 := m n % 2

-- Group homomorphism ψ : S → {±1}
def ψ (n : S) : Multiplicative (ZMod 2) := (-1) ^ m n

-- Prove ϕ is a monoid homomorphism
theorem ϕ_hom : MonoidHom S (AddMonoid (ZMod 2)) ϕ :=
  { map_mul' := λ a b ↦ by
      simp [ϕ, m]
      rw [factorOrderOfPrime_mul]
      simp [add_mod]
      congr
    map_one' := by simp [ϕ, m, one_factors] }

-- Prove ψ is a monoid homomorphism
theorem ψ_hom : MonoidHom S (Multiplicative (ZMod 2)) ψ :=
  { map_mul' := λ a b ↦ by
      simp [ψ, pow_add]
    map_one' := by simp [ψ, pow_zero] }

-- Isomorphism θ : ℤ/2ℤ → {±1} (as additive to multiplicative)
def θ : AddMonoidHom (ZMod 2) (Multiplicative (ZMod 2)) :=
  { toFun := λ x ↦ (-1) ^ x.val
    map_zero' := rfl
    map_add' := λ x y ↦ by
      simp [pow_add] }

-- Prove θ is an isomorphism (bijective, etc.)
theorem θ_iso : AddEquiv (ZMod 2) (Multiplicative (ZMod 2)) :=
  AddEquiv.ofBijective θ ⟨λ x y h ↦ by
    cases' x with xv; cases' y with yv
    simp at h
    norm_num at h
    congr, λ h ↦ by
    cases' h with hv
    simp
    norm_num⟩

-- Commutativity: ψ = θ ∘ ϕ
theorem comm_ψ_θ_ϕ : ∀ n : S, ψ n = θ (ϕ n) := λ n ↦ rfl

-- Thus, the isomorphism between the images via θ
