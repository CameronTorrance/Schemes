import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import algebra.comm_rings.instances.quotient_ring

namespace comm_ring

universe u

open set

def nilpotent {R : Type u} [comm_ring R] (r : R) : Prop := ∃ n : ℕ, r^(nat.succ n) = 0

/-
  In an ideal world prove the binomial thm and it to prove that the nilradical is an
  ideal but I'm too stupid to do that in LEAN. Instead I'm going show the intersetion
  of prime ideals is equal to the set of nilradicals.
-/

def intersection_of_prime_ideals (R : Type u) [comm_ring R] : ideal R
  := ⋂₀ (image (λ p : Spec R, p) (@univ (Spec R)))

theorem nilpotents_in_all_prime_ideals {R : Type u} [comm_ring R] : ∀ (x : R) (p : Spec R), 
  nilpotent x → x ∈ p.body :=
begin
  intros x p hx,
  cases hx with n hx,
  end


end comm_ring