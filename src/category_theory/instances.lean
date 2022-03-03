import category_theory.basic

universes v₁ v₂ v u₁ u₂ u

namespace category

open classical

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

structure opposite (C : Type u) :=
  (val : C)

def op {C : Type u} : C → opposite C := λ c, {val := c}

theorem op_val (C : Type u) : ∀ c : C, (op c).val = c := λ _,rfl 

@[simp]
theorem opposite_equality (C : Type u) 
  : ∀ c₁ c₂ : opposite C , c₁.val = c₂.val ↔ c₁ = c₂ :=
begin
  intros c₁ c₂,
  split,
  cases c₁,
  cases c₂,
  simp,
  intro,
  assumption,
  intro h,
  rw h,
end

instance opposite_nonempty (C : Type u) [nC :nonempty C] : nonempty (opposite C) :=
begin
  split,
  split,
  apply choice,
  assumption,
end

instance opposite_categoy (C : Type u) [category.{v} C]: category.{v} (opposite C) :=
{
  Mor := λ A B, Mor B.val A.val,
  idₘ := λ A, idₘ A.val,
  comp := λ A B C f₁ f₂, f₂ ∘ₘ f₁,
  comp_assoc :=
    begin
      intros A₁ A₂ A₃ A₄ f₁ f₂ f₃,
      rw comp_assoc,
    end,
  id_comp_left :=
    begin
      intros A B f,
      rw id_comp_right,
    end,
  id_comp_right :=
    begin
      intros A B f,
      rw id_comp_left,
    end,
}



end category