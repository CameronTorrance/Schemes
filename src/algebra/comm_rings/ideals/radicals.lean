import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import algebra.comm_rings.instances.quotient_ring

namespace comm_ring

universe u

def nilpotent {R : Type u} [comm_ring R] (r : R) : Prop := ∃ n : ℕ, r^(nat.succ n) = 0

/-
  In an ideal world prove the binomial thm but I'm too stupid to do that in
  LEAN. So I will prove a weaker version at least for now.
-/

inductive is_weak_binomial_expansion_up_to_k {R : Type u} [comm_ring R] (a b : R) (n : ℕ)
  : R → ℕ → Prop
| last_term : ∀ c : R, is_weak_binomial_expansion_up_to_k (c * a^n) 0
| add_term : ∀ (t c l: R) (k : ℕ), nat.succ k ≤ n → (is_weak_binomial_expansion_up_to_k l k) →
  (t = c * a^(n -k.succ) * b^k.succ + l)
  → is_weak_binomial_expansion_up_to_k t (nat.succ k)

@[reducible]
def is_weak_binomial_expansion {R : Type u} [comm_ring R] (a b t: R) (n : ℕ) : Prop 
  := is_weak_binomial_expansion_up_to_k a b n t n  

theorem weak_binomial_scaled_by_a {R : Type u} [comm_ring R] {a b : R} : ∀ {t : R} {n : ℕ}, 
  is_weak_binomial_expansion a b t n → is_weak_binomial_expansion a b (a * t) (nat.succ n) := sorry

theorem weak_binomial_scaled_by_b {R : Type u} [comm_ring R] {a b : R} : ∀ {t : R} {n : ℕ},
  is_weak_binomial_expansion a b t n → is_weak_binomial_expansion a b (b * t) (nat.succ n) := sorry

theorem weak_binomial_sum {R : Type u} [comm_ring R] {a b : R} : ∀ {t₁ t₂ : R} {n : ℕ}, 
  is_weak_binomial_expansion a b t₁ n → is_weak_binomial_expansion a b t₂ n 
  → is_weak_binomial_expansion a b (t₁ + t₂) n := sorry

theorem weak_binomial_theorem {R : Type u} [comm_ring R] (a b : R) (n : ℕ) 
  : is_weak_binomial_expansion a b ((a + b)^n) n :=
begin
  induction n with n hn,
  rw power_of_zero,
  rw ← power_of_zero a,
  rw ← mul_one (a^0),
  apply is_weak_binomial_expansion_up_to_k.last_term,
  have hrw : (a + b)^n.succ = a*(a + b)^n + b*(a + b)^n,
    have h : (a + b)^n.succ = (a + b) * (a + b)^n := rfl,
    rw [h,mul_comm,mul_dis],
    simp [mul_comm],
  rw hrw,
  apply weak_binomial_sum,
  apply weak_binomial_scaled_by_a,
  exact hn,
  apply weak_binomial_scaled_by_b, 
  exact hn,
end

end comm_ring