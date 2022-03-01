import category_theory.basic
import category_theory.instances

universes v u uₛ

namespace category

def filtered_category (C : Type u) [nonempty C] [category.{v} C] 
  := (∀ i₁ i₂ : C, ∃ (j : C), nonempty (Mor i₁ j) ∧ nonempty (Mor i₂ j)) 
      ∧ (∀ (i j : C) (f₁ f₂ : Mor i j), ∃ (k : C) (w : Mor j k), w ∘ₘ f₁ = w ∘ₘ f₂)  

structure concrete_category (C : Type u) [category.{v} C] :=
  (val : C +→ Type uₛ)
  (property : faithful_functor val)


end category 