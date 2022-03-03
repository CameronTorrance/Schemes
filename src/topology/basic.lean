import category_theory.basic
import misc.set

namespace topology

open set
open classical

universes u v

class topology (X : Type u) :=
  (is_open : set X → Prop)
  (whole_space_open : is_open univ)
  (empty_set_open : is_open ∅)
  (arbitary_unions_open (s: set (set X)) : (∀ t : set X, t ∈ s → is_open t) → is_open (⋃₀ s))
  (pairwise_inters_open : ∀ s t : set X, is_open s → is_open t → is_open (s ∩ t))

def is_open {X : Type u} [T_X: topology X] : set X → Prop := T_X.is_open

def is_continous_map {X : Type u} {Y : Type v}[T_X : topology X][T_Y : topology Y] (f : X → Y) : Prop :=
∀ s : set Y , is_open s → is_open (pre_image f s)

structure Open (X : Type u) [topology X] : Type u:=
  (val : set X)
  (val_open : is_open val)

def open_set_membership {X : Type u} [topology X] : X → Open X → Prop
  := λ p O, p ∈ O.val

instance open_set_has_mem (X : Type u) [topology X] : has_mem X (Open X)
  := ⟨open_set_membership⟩ 

inductive inclusion {X : Type u} [topology X] (O₁ O₂ : Open X) : Type u
  | proof : O₁.val ⊆ O₂.val → inclusion

theorem inclusion_equality {X : Type u} [topology X] {O₁ O₂ : Open X} 
  : ∀ x y : inclusion O₁ O₂, x = y :=
begin
  intros x y,
  cases x,
  cases y,
  refl,
end

def inclusion_comp {X : Type u} [topology X] {O₁ O₂ O₃ : Open X}
  : inclusion O₂ O₃ → inclusion O₁ O₂ → inclusion O₁ O₃ :=
begin
  intros i₁ i₂,
  apply inclusion.proof,
  cases i₁,
  cases i₂,
  intros x hx,
  apply i₁,
  apply i₂,
  assumption,
end

def open_set_intersection {X : Type u} [topology X] : Open X → Open X → Open X 
  | O₁ O₂ := ⟨O₁.val ∩ O₂.val, topology.pairwise_inters_open O₁.val O₂.val O₁.val_open O₂.val_open⟩ 

instance open_set_has_inter {X : Type u} [topology X] : has_inter (Open X) := ⟨topology.open_set_intersection⟩

lemma open_set_inter_val {X : Type u} [topology X] (O₁ O₂ : Open X) : (O₁ ∩ O₂).val = O₁.val ∩ O₂.val := rfl

instance category_of_open_sets (X : Type u) [topology X] : category (Open X) :=
{
  Mor := λ O₁ O₂, inclusion O₁ O₂,
  idₘ := λ O, inclusion.proof (λ x hx, hx),
  comp := λ O₁ O₂ O₃ i₁ i₂, inclusion_comp i₁ i₂,
  comp_assoc :=
    begin
      intros O₁ O₂ O₃ O₄ i₁ i₂ i₃,
      apply inclusion_equality,
    end,
  id_comp_left :=
    begin
      intros O₁ O₂ f,
      apply inclusion_equality,
    end,
  id_comp_right :=
    begin
      intros O₁ O₂ f,
      apply inclusion_equality,
    end,
}

instance category_of_open_sets_at_point {X : Type u} (p : X) [topology X] : category ({O :Open X // p ∈ O}) :=
{
  Mor := λ O₁ O₂, inclusion O₁.val O₂.val,
  idₘ := λ O, inclusion.proof (λ x hx, hx),
  comp := λ O₁ O₂ O₃ i₁ i₂, inclusion_comp i₁ i₂,
  comp_assoc :=
    begin
      intros O₁ O₂ O₃ O₄ i₁ i₂ i₃,
      apply inclusion_equality,
    end,
  id_comp_left :=
    begin
      intros O₁ O₂ f,
      apply inclusion_equality,
    end,
  id_comp_right :=
    begin
      intros O₁ O₂ f,
      apply inclusion_equality,
    end,
}

instance open_sets_at_a_point_nonempty {X : Type u} [topology X] (p : X) : nonempty ({O: Open X // p ∈ O}) :=
begin
  split,
  existsi Open.mk univ topology.whole_space_open,
  trivial,
end 

def open_cover_of {X : Type u} [topology X] (C : set (Open X)) (S : Open X)
  : Prop := (∀ {U : Open X} , U ∈ C → U.val ⊆ S.val) ∧ (∀ {x}, x ∈ S.val → ∃ U : Open X, U ∈ C ∧ x ∈ S.val)

def open_cover_includes {X : Type u} [topology X] {C : set (Open X)} {S : Open X}
  (hC : open_cover_of C S)  : Π {O}, O ∈ C → inclusion O S :=
begin
  intros O hO,
  apply inclusion.proof,
  apply hC.1,
  exact hO,
end

def inter_inc_left {X : Type u} [topology X] (O₁ O₂ : Open X) : inclusion (O₁ ∩ O₂) O₁ := 
begin
  apply inclusion.proof,
  rw open_set_inter_val,
  apply intersection_in_set,
end

def inter_inc_right {X : Type u} [topology X] (O₁ O₂ : Open X) : inclusion (O₁ ∩ O₂) O₂ := 
begin
  apply inclusion.proof,
  rw open_set_inter_val,
  rw intersection_commuative,
  apply intersection_in_set,
end

def open_at_point_forget {X : Type u} [topology X] (p : X) : {O: Open X // p ∈ O} +→ Open X :=
{
  map := λ O, O.val,
  fmap := λ O₁ O₂ f, f,
  fmap_prevs_comp := λ _ _ _ _ _, rfl,
  fmap_prevs_id := λ _, rfl,
}

end topology