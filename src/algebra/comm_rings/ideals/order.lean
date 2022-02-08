import algebra.comm_rings.basic
import algebra.comm_rings.ideals.basic
import algebra.comm_rings.ideals.instances
import misc.zorns_lemma
import misc.prop

namespace comm_ring

open set
open classical

universe u

def le_proper_ideal {R : Type u} [comm_ring R] : proper_ideal R → proper_ideal R → Prop :=
  λ I₁ I₂ : proper_ideal R, I₁.body ⊆ I₂.body

instance le_for_proper_ideals {R : Type u} [comm_ring R] : has_le (proper_ideal R) := ⟨le_proper_ideal⟩ 

theorem le_proper_ideal_refl {R : Type u} [comm_ring R] : ∀ I : proper_ideal R, I ≤ I :=
begin
  intro I,
  apply subset_reflexive,
end

theorem le_proper_ideal_trans {R : Type u} [comm_ring R] : ∀ I₁ I₂ I₃ : proper_ideal R,  I₁ ≤ I₂ →  I₂ ≤ I₃ →  I₁ ≤ I₃ :=
begin
  intros I₁ I₂ I₃ h₁ h₂,
  apply subset_transitive,
  exact h₁,
  exact h₂,
end

theorem le_proper_ideal_anti_symm {R : Type u} [comm_ring R] : ∀ I₁ I₂ : proper_ideal R,  I₁ ≤ I₂ →  I₂ ≤ I₁ → I₁ = I₂ :=
begin
  intros I₁ I₂ h₁ h₂,
  apply proper_ideal_equality,
  apply subset_antisymmetric,
  split,
  exact h₁,
  exact h₂,
end

instance proper_ideals_poset {R : Type u} [l:comm_ring R] : partial_order (proper_ideal R) := 
 begin
   split,
   apply le_proper_ideal_anti_symm,
   apply le_proper_ideal_refl,
   apply le_proper_ideal_trans,
 end

 theorem maximal_element_is_maximal_ideal {R : Type u} [comm_ring R] : ∀ {I : proper_ideal R}, maximal_element I ↔ is_maximal I :=
 begin
  
   intro I,
   split,
   intros hI J hJ,
   by_cases ↑J = univ,
   right,
   have trv : ↑J = J.body := rfl,
   rw ← trv,
   exact h,
   left,
   let K := ideal_to_proper h,
   have trv : ↑J = K.body := rfl,
   rw ← hI K hJ,
   rw trv,
   intros hI J hJ,
   apply proper_ideal_equality,
   cases hI (proper_ideals_are_ideals J) hJ,
   exact h,
   apply false.elim,
   apply J.proper,
   exact h,
 end

def union_of_chain_of_ideals_set {R : Type u} [comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅) : set R 
  := ⋃₀ (image (λ I : proper_ideal R, I.body) s) 

lemma union_of_chain_of_ideals_contains_zero {R : Type u} [l:comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅)
  : l.zero ∈ union_of_chain_of_ideals_set hs ns :=
begin
  let I := some (not_empty_set_has_element ns),
  have hI : I ∈ s := some_spec (not_empty_set_has_element ns),
  apply union_upper_bound,
  have hIbody : I.body ∈ image (λ I :proper_ideal R, I.body) s,
    apply image_membership,
    exact hI,
  exact hIbody,
  apply I.contains_zero,
end

lemma union_of_chain_of_ideals_add_closure {R : Type u} [comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅)
  : ∀ a b, a ∈ union_of_chain_of_ideals_set hs ns → b ∈ union_of_chain_of_ideals_set hs ns → a + b ∈ union_of_chain_of_ideals_set hs ns :=
begin
  intros a b ha hb,
  cases ha with A₁ hA₁,
  cases hb with A₂ hA₂,
  cases hA₁ with hA₁inim hainA₁,
  cases hA₂ with hA₂inim hbinA₂,
  cases hA₁inim with I₁ hI₁,
  cases hA₂inim with I₂ hI₂,
  let I := some (every_pair_is_bounded_in_chain hs ⟨and.left hI₁,and.left hI₂⟩),
  have hI : I ∈ s ∧ I₁ ≤ I ∧ I₂ ≤ I := some_spec (every_pair_is_bounded_in_chain hs ⟨and.left hI₁,and.left hI₂⟩),
  existsi I.body,
  have trv : I.body ∈ image (λ I : proper_ideal R, I.body) s,
    apply image_membership,
    exact and.left hI,
  existsi trv,
  apply I.add_closure,
  apply and.left (and.right hI),
  rw ← and.right hI₁ at hainA₁,
  exact hainA₁,
  apply and.right (and.right hI),
  rw ← and.right hI₂ at hbinA₂,
  exact hbinA₂,
end

lemma union_of_chain_of_ideals_mul_absorb {R : Type u} [comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅)
  : ∀ r {i}, i ∈ union_of_chain_of_ideals_set hs ns → r * i ∈ union_of_chain_of_ideals_set hs ns :=
begin
  intros r i hi,
  cases hi with A hA,
  cases hA with hAinim hiinA,
  cases hAinim with I hI,
  existsi I.body,
  have trv : I.body ∈ image (λ I : proper_ideal R, I.body) s,
    apply image_membership,
    exact and.left hI,
  existsi trv,
  apply I.mul_absorb,
  rw ← and.right hI at hiinA,
  exact hiinA,
end

lemma union_of_chain_of_ideals_proper {R : Type u} [l:comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅)
  : union_of_chain_of_ideals_set hs ns ≠ univ :=
begin
  have h : l.one ∉ union_of_chain_of_ideals_set hs ns,
    intro ab,
    cases ab with A hA,
    cases hA with hAinIm hainA,
    cases hAinIm with I hI,
    rw ← (and.right hI) at hainA,
    have h₁ : l.one ∉ I.body := unit_not_in_proper_ideal one_is_unit,
    apply h₁,
    exact hainA,
  intro ab,
  apply h,
  rw ab,
  trivial,
end

lemma union_of_chain_of_ideals_minus_closure {R : Type u} [comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅)
  : ∀ r : R, r ∈ union_of_chain_of_ideals_set hs ns → -r ∈ union_of_chain_of_ideals_set hs ns :=
begin
  intros i hi,
  cases hi with A hA,
  cases hA with hAinim hiinA,
  cases hAinim with I hI,
  existsi I.body,
  have trv : I.body ∈ image (λ I : proper_ideal R, I.body) s,
    apply image_membership,
    exact and.left hI,
  existsi trv,
  apply I.minus_closure,
  rw ← and.right hI at hiinA,
  exact hiinA,
end

def union_of_chain_of_ideals {R : Type u} [comm_ring R] {s : set (proper_ideal R)} (hs : is_chain s) (ns : s ≠ ∅) : proper_ideal R :=
  {
    body := union_of_chain_of_ideals_set hs ns,
    contains_zero := union_of_chain_of_ideals_contains_zero hs ns,
    minus_closure := union_of_chain_of_ideals_minus_closure hs ns,
    add_closure := union_of_chain_of_ideals_add_closure hs ns,
    mul_absorb := union_of_chain_of_ideals_mul_absorb hs ns,
    proper := union_of_chain_of_ideals_proper hs ns,
  }

theorem union_of_chain_of_ideals_is_upper_bound {R : Type u} [comm_ring R] (s : set (proper_ideal R)) (hs : is_chain s) (ns : s ≠ ∅)
  : ∀ t : proper_ideal R, t ∈ s → t ≤ (union_of_chain_of_ideals hs ns) :=
begin
  intros t htins,
  apply union_upper_bound,
  split,
  split,
  exact htins,
  refl,
end

theorem non_zero_ring_has_maximal_ideal {R: Type u} [comm_ring R] (not_zero: ∃ x : R, x ≠ 0) : ∃ I : proper_ideal R, is_maximal I :=
begin
  have h : ∃ I : proper_ideal R, maximal_element I,
    apply zorns_lemma,
    intros C hC,
    by_cases C ≠ ∅,
    existsi union_of_chain_of_ideals hC h,
    apply union_of_chain_of_ideals_is_upper_bound,
    have h₁ := not_not h,
    have zero_ideal_p : proper_ideal R,
      apply ideal_to_proper,
      exact zero_ideal_proper not_zero,
    existsi zero_ideal_p,
    rw h₁,
    intros a ha b hb,
    apply false.elim,
    exact ha,
  let I := some h,
  have hI : maximal_element I := some_spec h,
  existsi I,
  rw ← maximal_element_is_maximal_ideal,
  exact hI,
end

end comm_ring