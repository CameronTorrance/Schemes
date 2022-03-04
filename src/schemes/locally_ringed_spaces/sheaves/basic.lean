import topology.basic
import category_theory.basic
import category_theory.instances
import category_theory.universal_properties.limit_colimt

universes v v₁ v₂ u u₁ u₂ 

open category
open topology
open set


/-
  We have a category C with obj in Type u and mor in Type v, we'd like to think of C
  as being at least locally small so we will of v as being the level of sets.

  A 
-/

def inc_to_mor {X : Type u} [topology X] {O₁ O₂ : Open X} : inclusion O₁ O₂ → inclusion (op O₁).val (op O₂).val :=
begin
  intro,
  simp [op_val],
  assumption,
end

def res {X : Type v} [topology X]{C : Type u} [category.{v} C] {S : concrete_category.{v} C} (𝓕 : opposite (Open X) +→ C)
  {O₁ O₂ : Open X} (ι : inclusion O₁ O₂) : (S.val ⊚ 𝓕).map (op O₂) → (S.val ⊚ 𝓕).map (op O₁) 
  := λ f : (S.val ⊚ 𝓕).map (op O₂), ((S.val ⊚ 𝓕).fmap) (inc_to_mor ι) f 

def glueable_sections {X : Type v} [topology X] {C : Type u} [category.{v} C] {S : concrete_category C} 
  {𝓕 : opposite (Open X) +→ C} {Co : set (Open X)} {O : Open X} (hCo : open_cover_of Co O) 
  (Cs : set (Σ O' : Open X, (S.val ⊚ 𝓕).map (op O'))) : Prop 
  := (∀ {s : Σ O' : Open X, (S.val ⊚ 𝓕).map (op O')}, s ∈ Cs → s.1 ∈ Co) ∧
     (open_cover_of (image (λ s : Σ O' : Open X, (S.val ⊚ 𝓕).map (op O'), s.1 ) Cs) O) ∧ 
     (∀ {s₁ s₂ : Σ O' : Open X, (S.val ⊚ 𝓕).map (op O')}, res 𝓕 (inter_inc_left s₁.1 s₂.1) s₁.2 = res 𝓕 (inter_inc_right s₁.1 s₂.1) s₂.2)


structure sheaf (X : Type v) [topology X] {C : Type u} [category.{v} C] (S : concrete_category.{v} C)  :=
  (body : opposite (Open X) +→ C)
  (local_equality : ∀ O : Open X, ∀ {Co} (hCo : open_cover_of Co O),  
                    ∀ f g : (S.val ⊚ body).map (op O), 
                    (∀ {O' : Open X} (hO' : O' ∈ Co), 
                    res body (open_cover_includes hCo hO') f = res body (open_cover_includes hCo hO') g) 
                    → f = g)
  (sections_glue : ∀ O : Open X, ∀ {Co} (hCo : open_cover_of Co O), 
                   ∀ {Cs : set (Σ O' : Open X, (S.val ⊚ body).map (op O'))},
                   ∀ hgs : glueable_sections hCo Cs, ∃ f : (S.val ⊚ body).map (op O),
                   ∀ {s : Σ O' : Open X, (S.val ⊚ body).map (op O')} (hs : s ∈ Cs), 
                   res body (open_cover_includes hCo (hgs.1 hs)) f = s.2)

namespace sheaf

theorem op_open_sets_at_a_point_filtered_category {X : Type v} [topology X] (p : X) : filtered_category (opposite ({O : Open X // p ∈ O})) :=
begin
  split,
  intros i₁ i₂,
  cases i₁ with O₁,
  cases i₂ with O₂,
  have hp : p ∈ (O₁ ∩ O₂ : Open X),
    exact ⟨O₁.property, O₂.property⟩,
  existsi op (subtype.mk (O₁ ∩ O₂ : Open X) hp),
  split,
  split,
  apply inc_to_mor,
  simp,
  apply inter_inc_left,
  split,
  apply inc_to_mor,
  simp,
  apply inter_inc_right,
  intros i j f₁ f₂,
  existsi j,
  existsi idₘ j,
  apply inclusion_equality,
end

def stalk_shape {X : Type v} [topology X] {C : Type u} [category.{v} C] {S : concrete_category.{v} C} 
  (𝓕 : sheaf X S) (p : X) : opposite ({O: Open X // p ∈ O}) +→ C := 𝓕.body ⊚ (op_functor (open_at_point_forget p))

noncomputable def stalk {X : Type v} [topology X] {C : Type u} [category.{v} C] {S : concrete_category.{v} C} 
  (𝓕 : sheaf X S) (p : X) 
  : Σ st : C, (Π oOp : opposite ({O: Open X // p ∈ O}), Mor ((stalk_shape 𝓕 p).map oOp) st) 
  := filtered_colimit (op_open_sets_at_a_point_filtered_category p) S (stalk_shape 𝓕 p)

theorem stalk_property {X : Type v} [topology X] {C : Type u} [category.{v} C] {S : concrete_category.{v} C} 
  (𝓕 : sheaf X S) (p : X) 
  : is_colimit (stalk_shape 𝓕 p) (stalk 𝓕 p)
  := filtered_colimit_property (op_open_sets_at_a_point_filtered_category p) S (stalk_shape 𝓕 p)


end sheaf