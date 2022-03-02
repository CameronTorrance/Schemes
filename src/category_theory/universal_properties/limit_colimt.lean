import category_theory.basic
import category_theory.instances

universes v vᵢ u uᵢ uₛ

namespace category

def filtered_category (C : Type u) [nonempty C] [category.{v} C] 
  := (∀ i₁ i₂ : C, ∃ (j : C), nonempty (Mor i₁ j) ∧ nonempty (Mor i₂ j)) 
      ∧ (∀ (i j : C) (f₁ f₂ : Mor i j), ∃ (k : C) (w : Mor j k), w ∘ₘ f₁ = w ∘ₘ f₂)  

def is_cocone {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] (F : I +→ C) 
  : (Σ cl : C, Π i : I, Mor (F.map i) cl) → Prop 
  | ⟨cl ,j⟩ := ∀ (i₁ i₂ : I) (f : Mor i₁ i₂), j i₁ = (j i₂) ∘ₘ (F.fmap f)

def is_colimit {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] (F : I +→ C) 
  : (Σ cl : C, Π i : I, Mor (F.map i) cl) → Prop := 
  λ cᵤ, is_cocone F cᵤ ∧ ∀ c, is_cocone F c → ∃! φ : Mor cᵤ.1 c.1, ∀ i : I, c.2 i = φ ∘ₘ cᵤ.2 i    

def is_cone {C: Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] (F : I +→ C) 
  : (Σ l : C, Π i : I, Mor l (F.map i)) → Prop 
  | ⟨l ,j⟩ := ∀ (i₁ i₂ : I) (f : Mor i₁ i₂), j i₂ = (F.fmap f) ∘ₘ (j i₁)

/-
  Using a nonstandard defintion of concrete category based on the idea
  that I'm only using the defn for sheaf, and need them to commute with
  colimits to define stalks. 
-/


structure concrete_category (C : Type u) [category.{v} C] :=
  (val : C +→ Type uₛ)
  (property : faithful_functor val)
  (prevs_filtered_colims : ∀ (J : Type u) [SJ: category.{v} J] 
    [nonempty J] (hJ : filtered_category J) (F : J +→ C), 
    ∀ c : (Σ cl : C, Π i : J, Mor (F.map i) cl) , is_colimit F c ↔
    is_colimit (val ⊚ F) ⟨val.map c.1, λ i : J, val.fmap (c.2 i)⟩)

end category