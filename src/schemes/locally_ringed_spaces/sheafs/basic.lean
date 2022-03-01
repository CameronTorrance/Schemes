import topology.basic
import category_theory.basic
import category_theory.properties
import category_theory.instances

universes v u uₜ

open category
open topology
open set

def inc_to_mor {X : Type u} [topology X] {O₁ O₂ : Open X} : inclusion O₁ O₂ → inclusion (op O₁).val (op O₂).val :=
begin
  intro,
  simp [op_val],
  assumption,
end

def res {X : Type u} [topology X]{C : Type u} [category.{v} C] {S : concrete_category.{v u uₜ} C} (𝓕 : opposite (Open X) +→ C)
  {O₁ O₂ : Open X} (ι : inclusion O₁ O₂) : (S.val ⊚ 𝓕).map (op O₂) → (S.val ⊚ 𝓕).map (op O₁) 
  := λ f : (S.val ⊚ 𝓕).map (op O₂), ((S.val ⊚ 𝓕).fmap) (inc_to_mor ι) f 

def glueable_sections {X : Type u} [topology X] {C : Type u} [category.{v} C] {S : concrete_category C} 
  {𝓕 : opposite (Open X) +→ C} {Co : set (Open X)} {O : Open X} (hCo : open_cover_of Co O) 
  (Cs : set (Σ O' : Open X, (S.val ⊚ 𝓕).map (op O'))) : Prop 
  := (∀ {s : Σ O' : Open X, (S.val ⊚ 𝓕).map (op O')}, s ∈ Cs → s.1 ∈ Co) ∧
     (open_cover_of (image (λ s : Σ O' : Open X, (S.val ⊚ 𝓕).map (op O'), s.1 ) Cs) O) ∧ 
     (∀ {s₁ s₂ : Σ O' : Open X, (S.val ⊚ 𝓕).map (op O')}, res 𝓕 (inter_inc_left s₁.1 s₂.1) s₁.2 = res 𝓕 (inter_inc_right s₁.1 s₂.1) s₂.2)


structure sheaf (X : Type u) [topology X]{C : Type u} [category.{v} C] (S : concrete_category C)  :=
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


end sheaf