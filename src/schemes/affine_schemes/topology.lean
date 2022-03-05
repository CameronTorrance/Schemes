import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import algebra.comm_rings.ideals.identities
import algebra.comm_rings.ideals.radicals
import topology.basic
import misc.set

universes v u 

open set comm_ring topology

namespace scheme


def vanishing_set {R : Type u} [comm_ring R] : set R → set (Spec R)
  := λ S p, S ⊆ p 

theorem vanishing_set_reverses_order {R : Type u} [comm_ring R] {S₁ S₂ : set R}
  : S₁ ⊆ S₂ → vanishing_set S₂ ⊆ vanishing_set S₁  :=
begin
  intros hS₁S₂ p hp,
  apply subset_transitive,
  exact hS₁S₂,
  exact hp,
end

theorem vanishing_set_can_move_to_ideals {R : Type u} [comm_ring R] (S : set R)
  : vanishing_set S = vanishing_set (ideal_generated_by_set S) :=
begin
  apply subset_antisymmetric,
  split,
  intros p hp,
  intros f hf,
  induction hf with x s₁ s₂ l trv hs₂ hl hx linp,
  apply p.contains_zero,
  rw hx,
  apply p.add_closure,
  apply p.mul_absorb,
  apply hp,
  exact hs₂,
  exact linp,
  apply vanishing_set_reverses_order,
  apply set_in_ideal_gen_by_set,
end

theorem vanishing_set_can_move_to_radicals {R : Type u} [comm_ring R] (I : ideal R)
  : vanishing_set (↑I : set R) = vanishing_set (√I) :=
begin
  apply subset_antisymmetric,
  split,
  intros p hp f hf,
  have trv₁ : ↑(√I) = (√I).body := rfl, 
  rw [trv₁,elements_of_radical] at hf,
  cases hf with n hn,
  apply prime_ideal_power_mem,
  apply hp,
  have trv₂ : ↑I = I.body := rfl,
  rw  trv₂,
  exact hn,
  apply vanishing_set_reverses_order,
  apply ideal_subset_of_radical,
end

end scheme