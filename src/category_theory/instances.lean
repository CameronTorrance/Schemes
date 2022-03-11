import category_theory.basic

universes v₁ v₂ v₃ v₄ v u₁ u₂ u₃ u₄ u

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

@[simp]
theorem functor_cat_comp {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
  {F₁ F₂ F₃ : C +→ D} (φ₁ : Mor F₂ F₃) (φ₂ : Mor F₁ F₂) : φ₁ ∘ₘ φ₂ = φ₁ ∘ₙ φ₂ := rfl

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

theorem set_comp_app : ∀ {A₁ A₂ A₃ : Type u} (f₁ : Mor A₂ A₃) (f₂ : Mor A₁ A₂) (s : A₁), 
  ((f₁ ∘ₘ f₂) : A₁ → A₃) s =  f₁ ( f₂ s) := λ _ _ _ _ _ _, rfl

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

def op_functor {C : Type u₁} {D : Type u₂} [SC:category.{v₁} C] [SD:category.{v₂} D] (F : C +→ D)
  : (opposite C) +→ (opposite D) :=
{
  map := λ oC₁, op (F.map oC₁.val),
  fmap := λ oC₁ oC₂ f, F.fmap f,
  fmap_prevs_comp :=
    begin
      intros oC₁ oC₂ oC₃ f₁ f₂,
      apply F.fmap_prevs_comp,
    end, 
  fmap_prevs_id :=
    begin
      intro oC,
      cases oC with c,
      have hrw : op c = {val := c} := rfl,
      rw ← hrw,
      simp [idₘ],
      rw F.fmap_prevs_id,
      refl,
    end,
}

instance product_category (C : Type u₁) (D : Type u₂) [category.{v₁} C] [category.{v₂} D] 
  : category.{max v₁ v₂} (C × D) :=
{
  Mor := λ p₁ p₂, (Mor p₁.1 p₂.1) × (Mor p₁.2 p₂.2),
  idₘ := λ p, ⟨idₘ p.1, idₘ p.2⟩,
  comp := λ _ _ _ pf₁ pf₂, ⟨pf₁.1 ∘ₘ pf₂.1, pf₁.2 ∘ₘ pf₂.2⟩,
  comp_assoc :=
    begin
      intros p₁ p₂ p₃ p₄ pf₁ pf₂ pf₃,
      simp [comp_assoc],
    end,
  id_comp_right :=
    begin
      intros p₁ p₁ pf,
      simp [id_comp_right],
    end,
  id_comp_left :=
    begin
      intros p₁ p₂ pf,
      simp [id_comp_left],
    end,
}

theorem prod_cat_id {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
  : ∀ A : C × D, idₘ A = ⟨idₘ A.1, idₘ A.2⟩ := λ _, rfl 

theorem prod_cat_comp {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
  {A₁ A₂ A₃ : C × D} (pf₁ : Mor A₂ A₃) (pf₂ : Mor A₁ A₂) 
  : pf₁ ∘ₘ pf₂ = ⟨pf₁.1 ∘ₘ pf₂.1, pf₁.2 ∘ₘ pf₂.2⟩ := rfl

def product_functor {C₁: Type u₁} {D₁ : Type u₂} {C₂ : Type u₃} {D₂ : Type u₄} [category.{v₁} C₁]
  [category.{v₂} D₁] [category.{v₃} C₂] [category.{v₄} D₂] 
  (F : C₁ +→ C₂) (G : D₁ +→ D₂) : (C₁ × D₁) +→ (C₂ × D₂) :=
{
  map := λ O, ⟨F.map O.1, G.map O.2⟩,
  fmap := λ _ _ pf, ⟨F.fmap pf.1, G.fmap pf.2⟩,
  fmap_prevs_id :=
    begin
      intro,
      simp [prod_cat_id, functor.fmap_prevs_id],
    end,
  fmap_prevs_comp := 
    begin
      intros A₁ A₂ A₃ pf₁ pf₂,
      simp [prod_cat_comp, functor.fmap_prevs_comp],
    end,
}

end category