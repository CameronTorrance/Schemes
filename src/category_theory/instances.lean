import category_theory.basic

universes v₁ v₂ v u₁ u₂ u

namespace category

instance functor_category (C : Type u₁) (D : Type u₂) [category.{v₁} C] [category.{v₂} D]
  : category (C +→ D) := 
{
  Mor := λ F₁ F₂, F₁ →ₙ F₂,
  idₘ := idₙ,
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


instance Type_Cat : category (Type u) :=
{
  Mor := λ A B : Type u, A → B,
  comp := λ A₁ A₂ A₃ f₁ f₂, f₁ ∘ f₂,
  idₘ := λ A, id,
  comp_assoc :=
    begin
      intros A B C D f₁ f₂ f₃,
      apply funext,
      intro,
      refl, 
    end,
  id_comp_left :=
    begin
      intros A B f,
      apply funext,
      intro,
      refl,
    end,
  id_comp_right :=
    begin
      intros A B f,
      apply funext,
      intro,
      refl,
    end,
}



end category