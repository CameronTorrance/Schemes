import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import algebra.comm_rings.ideals.identities
import algebra.comm_rings.ideals.radicals
import topology.basic
import topology.instances.basic
import misc.set

universes v u 

open set comm_ring topology classical

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
  rw trv₂,
  exact hn,
  apply vanishing_set_reverses_order,
  apply ideal_subset_of_radical,
end

theorem vanishing_set_of_union {R : Type u} [comm_ring R] (C : set (set R)) 
  : vanishing_set (⋃₀ C) = ⋂₀ (image (vanishing_set) C) :=
begin
  apply subset_antisymmetric,
  split,
  intros p hp,
  intros A hA,
  cases hA with W hW,
  cases hW with WinC Arw,
  rw ← Arw,
  apply subset_transitive,
  apply union_upper_bound,
  assumption,
  assumption,
  intros p hp,
  have sub : ∀ {Cₛ}, Cₛ ∈ C → p ∈ vanishing_set Cₛ,
    intros Cₛ hCₛ,
    apply hp (vanishing_set Cₛ),
    apply image_membership,
    exact hCₛ,
  apply bounded_union_in_bound,
  exact @sub,
end

theorem vanishing_set_of_univ {R : Type u} [comm_ring R]
  : vanishing_set (univ : set R) = ∅ :=
begin
  apply subset_antisymmetric,
  split,
  intros p hp,
  apply p.proper,
  apply subset_antisymmetric,
  split,
  apply set_subset_of_univ,
  exact hp,
  exact empty_set_subset,
end

theorem vanishing_set_of_zero {R : Type u} [comm_ring R]
  : vanishing_set ((λ x : R, x = 0)) = univ :=
begin
  apply subset_antisymmetric,
  split,
  intros p hp,
  trivial,
  intros p trv s hs,
  have h : s = 0 := hs,
  rw h,
  apply p.contains_zero,
end

theorem vanishing_set_of_inter {R : Type u} [comm_ring R] (I₁ I₂ : ideal R)
  : vanishing_set (↑(I₁ ∩ I₂) : set R) = (vanishing_set I₁) ∪ (vanishing_set I₂) :=
begin
  apply subset_antisymmetric,
  split,
  intro p,
  apply contrapostive,
  intro hp,
  cases not_in_union hp,
  cases not_subset_some_element_in_diff left with f₁ hf₁,
  cases not_subset_some_element_in_diff right with f₂ hf₂,
  cases hf₁ with f₁inI₁ f₁ninp,
  cases hf₂ with f₂inI₂ f₂ninp,
  intro ab,
  have f₁f₂ninp : f₁ * f₂ ∉ ↑p,
    intro ab,
    cases p.prime f₁ f₂ ab,
    apply f₁ninp,
    assumption,
    apply f₂ninp,
    assumption,
  apply f₁f₂ninp,
  apply ab,
  rw ideal_pairwise_inter_set,
  split,
  rw mul_comm,
  apply I₁.mul_absorb,
  assumption,
  apply I₂.mul_absorb,
  assumption,
  have h₁ : vanishing_set ↑I₁ ⊆ vanishing_set (↑(I₁ ∩ I₂) :set R),
    apply vanishing_set_reverses_order,
    rw ideal_pairwise_inter_set,
    apply intersection_in_set,
  have h₂ : vanishing_set ↑I₂ ⊆ vanishing_set (↑(I₁ ∩ I₂) :set R),
    apply vanishing_set_reverses_order,
    rw ideal_pairwise_inter_set,
    rw intersection_commuative,
    apply intersection_in_set,
  intros p hp,
  cases hp,
  apply h₁,
  exact hp,
  apply h₂,
  exact hp,
end

def prime_spectrum_closed_topology (R : Type u) [comm_ring R] : closed_topology (Spec R) :=
{
  closed_b := λ S : set (Spec R), ∃ A : set R, vanishing_set A = S,
  whole_space_closed :=
    begin
      existsi (λ x : R, x = 0),
      rw vanishing_set_of_zero,
    end,
  empty_set_closed :=
    begin
      existsi univ,
      rw vanishing_set_of_univ,
    end,
  pairwise_unions_closed :=
    begin
      intros S₁ S₂ hS₁ hS₂,
      cases hS₁ with A₁ hA₁,
      cases hS₂ with A₂ hA₂,
      existsi ↑((ideal_generated_by_set A₁) ∩ (ideal_generated_by_set A₂)),
      rw vanishing_set_of_inter,
      simp [← vanishing_set_can_move_to_ideals,hA₁,hA₂],
    end,
  arbitary_inters_closed :=
    begin
      intros C hC,
      let data := λ S hS, some (hC S hS),
      have hdata : Π S hS, vanishing_set (data S hS) = S := 
        λ S hS, some_spec (hC S hS),
      let C' : set (set R) := λ S', ∃ S hS, S' = data S hS,
      have hC' : C = image vanishing_set C',
        apply subset_antisymmetric,
        split,
        intros S hS,
        existsi data S hS,
        split,
        existsi S,
        existsi hS,
        refl,
        apply hdata,
        intros S hS,
        cases hS with W hW,
        cases hW with WinC' Wrw,
        cases WinC' with A hA,
        cases hA with AinC hA,
        rw ← Wrw,
        rw hA,
        rw hdata,
        assumption,
        rw hC',
        existsi ⋃₀ C',
        rw vanishing_set_of_union,
    end,
}

instance prime_spectrum_topology (R : Type u) [comm_ring R] : topology (Spec R)
  := from_closed_topology (prime_spectrum_closed_topology R)


def distinguished_open_set {R : Type u} [comm_ring R] : R → set (Spec R)  
  := λ x, univ \ (vanishing_set (princple_ideal x))

theorem distinguished_opens_open {R : Type u} [comm_ring R] : ∀ x : R, is_open (distinguished_open_set x) :=
begin
  intro x,
  existsi (↑(princple_ideal x): set R),
  simp [distinguished_open_set],
end

end scheme