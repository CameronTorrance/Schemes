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

instance sheaf_category {X : Type v} [topology X] {C : Type u} [category.{v} C] {S : concrete_category.{v} C}
  : category (sheaf X S) :=
{
  Mor := λ 𝓕₁ 𝓕₂, 𝓕₁.body →ₙ 𝓕₂.body,
  idₘ := λ 𝓕, idₙ 𝓕.body,
  comp := λ F₁ F₂ F₃ φ₁ φ₂, φ₁ ∘ₙ φ₂,
  comp_assoc :=
    begin
      intros F₁ F₂ F₃ F₄ φ₁ φ₂ φ₃,
      apply natural_trans_equality,
      apply funext,
      intro,
      simp,
      rw comp_assoc,
    end,
  id_comp_left := 
    begin
      intros F₁ F₂ φ,
      apply natural_trans_equality,
      apply funext,
      intro,
      rw natural_trans_comp_map,
      simp,
      rw id_comp_left,
    end,
  id_comp_right := 
    begin
      intros F₁ F₂ φ,
      apply natural_trans_equality,
      apply funext,
      intro,
      rw natural_trans_comp_map,
      simp,
      rw id_comp_right,
    end, 
}


noncomputable def natural_trans_im_cocone {X : Type v} [topology X] {C : Type u} [category.{v} C]
  {S : concrete_category C} {𝓕₁ 𝓕₂ : sheaf X S} (φ : Mor 𝓕₁ 𝓕₂) (p : X) 
  : Σ c : C, Π O : opposite {O : Open X // p ∈ O}, Mor (𝓕₁.body.map (op O.val)) c
  := ⟨(stalk 𝓕₂ p).1, λ O : opposite {O : Open X // p ∈ O}, ((stalk 𝓕₂ p).2 ( O))∘ₘ(φ.map (op O.val))⟩

theorem natural_trans_im_cocone_obj {X : Type v} [topology X] {C : Type u} [category.{v} C]
  {S : concrete_category C} {𝓕₁ 𝓕₂ : sheaf X S} (φ : Mor 𝓕₁ 𝓕₂) (p : X) 
  : (natural_trans_im_cocone φ p).1 = (stalk 𝓕₂ p).1 := rfl

theorem natural_trans_im_cocone_map {X : Type v} [topology X] {C : Type u} [category.{v} C]
  {S : concrete_category C} {𝓕₁ 𝓕₂ : sheaf X S} (φ : Mor 𝓕₁ 𝓕₂) (p : X)
  : (natural_trans_im_cocone φ p).2 = λ O : opposite {O : Open X // p ∈ O}, ((stalk 𝓕₂ p).2 O)∘ₘ(φ.map (op O.val))
  := rfl

theorem existance_of_induced_morphism_of_stalks {X : Type v} [topology X] {C : Type u} [category.{v} C]
  (S : concrete_category C) {𝓕₁ 𝓕₂ : sheaf X S} (φ : Mor 𝓕₁ 𝓕₂) (p : X) 
  : ∃! φₚ : Mor (stalk 𝓕₁ p).1 (stalk 𝓕₂ p).1, 
   ∀ O : opposite {O : Open X// p ∈ O}, ((stalk 𝓕₂ p).2 O) ∘ₘ (φ.map (op O.val)) = φₚ ∘ₘ ((stalk 𝓕₁ p).2 O) :=
begin
  have hcc : is_cocone (stalk_shape 𝓕₁ p) (natural_trans_im_cocone φ p),
    intros O₁ O₂ i₂₁,
    have hrw₁ : (stalk_shape 𝓕₁ p).fmap i₂₁ = 𝓕₁.body.fmap i₂₁ := rfl, 
    have hrw₂ : (stalk_shape 𝓕₂ p).fmap i₂₁ = 𝓕₂.body.fmap i₂₁ := rfl,
    rw [hrw₁,← comp_assoc,← φ.natural,comp_assoc],
    have h𝓕₁ := (stalk_property 𝓕₂ p).1 ,
    simp,
    have hrw₄ : (stalk 𝓕₂ p).2 O₁ = ((stalk 𝓕₂ p).2 O₂) ∘ₘ 𝓕₂.body.fmap i₂₁,
      cases stalk 𝓕₂ p,
      apply h𝓕₁,
    rw hrw₄,
    refl,
  -- what follows is mere abstract nonsense.
  have hint := (stalk_property 𝓕₁ p).2 (natural_trans_im_cocone φ p) hcc,
  rw natural_trans_im_cocone_map φ p at hint,
  cases hint with φₚ hφₚ,
  simp [natural_trans_im_cocone_obj] at hφₚ,
  existsi φₚ,
  exact hφₚ,
end


end sheaf