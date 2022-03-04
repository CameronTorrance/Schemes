import topology.basic
import topology.instances.basic
import misc.set

namespace topology

universe u

open set

def is_cover {X : Type u} : set (set X) → Prop
  := λ s, ∀ x : X , ∃ t : set X , t ∈ s ∧ x ∈ t

def is_subcover {X : Type u} (s : set (set X)) : set (set X) → Prop := λ t, is_cover t ∧ t ⊆ s

def all_open_set {X : Type u} [topology X] (s : set (set X)) : Prop := ∀ t : set X, t ∈ s → is_open t

def compact_space (X : Type u) [topology X] : Prop 
  := ∀ t : set (set X), (is_cover t) ∧ (all_open_set t) → ∃ xs : list (set X), (list_to_set xs) ⊆ t ∧ (is_subcover t (list_to_set xs))

def compact_set {X : Type u} [topology X] (S : set X) : Prop := compact_space (subtype S)

def hausdorff (X : Type u) [topology X] : Prop
  := ∀ x y : X, x ≠ y → ∃ U_x U_y : set X, (is_open U_x) ∧ (is_open U_y) ∧ (x ∈ U_x) ∧ (y ∈ U_y) ∧ (U_x ∩ U_y = ∅)

/-
  For technical reasons I need show that we can bulid a topology from a base here.
-/

structure base (X : Type u) :=
  (elm: set X → Prop)
  (cover : is_cover elm)
  (inters_covered : ∀ {B₁ B₂ : set X}, elm B₁ → elm B₂ → 
    ∀ {x}, x ∈ B₁ ∩ B₂ → ∃ B₃, elm B₃ ∧ x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂)

def topology_from_base {X : Type u} (𝓑 : base X) : topology X :=
{
  is_open := λ U, ∀ {x}, x ∈ U → ∃ B, 𝓑.elm B ∧ x ∈ B ∧ B ⊆ U,
  whole_space_open :=
    begin
      intros x _,
      cases 𝓑.cover x with B hB,
      cases hB with Belm xinB,
      existsi B,
      split,
      assumption,
      split,
      assumption,
      apply set_subset_of_univ,
    end,
  empty_set_open :=
    begin
      intros _ hx,
      apply false.elim,
      exact hx,
    end,
  arbitary_unions_open :=
    begin
      intros C hC x hx,
      cases hx with U hU,
      cases hU with UinC xinU,
      cases hC U UinC xinU with B hB,
      existsi B,
      cases hB with Belm hB,
      cases hB with xinB BsubU,
      split,
      exact Belm,
      split,
      exact xinB,
      apply subset_transitive,
      assumption,
      apply union_upper_bound,
      assumption,
    end,
  pairwise_inters_open :=
    begin
      intros U₁ U₂ hU₁ hU₂ x hx,
      cases hx with xinU₁ xinU₂,
      cases hU₁ xinU₁ with B₁ hB₁,
      cases hB₁ with B₁elm hB₁,
      cases hB₁ with xinB₁ B₁inU₁,
      cases hU₂ xinU₂ with B₂ hB₂,
      cases hB₂ with B₂elm hB₂,
      cases hB₂ with xinB₂ B₂inU₂,
      have xinB₁B₂: x ∈ B₁ ∩ B₂ := ⟨xinB₁,xinB₂⟩,
      cases 𝓑.inters_covered B₁elm B₂elm xinB₁B₂ with B hB,
      existsi B,
      cases hB with Belm hB,
      cases hB with xinB BinB₁B₂,
      split,
      assumption,
      split,
      assumption,
      intros x hx,
      cases BinB₁B₂ hx,
      split,
      apply B₁inU₁,
      exact left,
      apply B₂inU₂,
      exact right,
    end,
}

end topology