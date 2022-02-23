
universes v u v₁ u₁ v₂ u₂ v₃ u₃

/-
  notation: C +→ D = functor from C to D
  notation: F₁ →ₙ F₂ = natural transformation from F₁ to F₂
-/

class category (obj : Type u ) : Type (max u (v+1)) :=
  (Mor : obj → obj → Type v)
  (comp : Π {A B C : obj}, Mor B C → Mor A B → Mor A C)
  (id : Π A : obj, Mor A A)
  (comp_assoc : ∀ {A B C D: obj} (f₁ : Mor A B) (f₂ : Mor B C) (f₃ : Mor C D),
     (comp f₃ (comp f₂ f₁)) = comp (comp f₃ f₂) f₁)
  (id_comp_left : ∀ {A B : obj} (f : Mor A B), comp (id B) f = f)
  (id_comp_right : ∀ {A B : obj} (f : Mor A B), comp f (id A) = f)


namespace category

notation f ` ∘ₘ `:80 g:80 := category.comp f g

structure functor (C : Type u₁) (D : Type u₂) [category.{v₁} C] [category.{v₂} D] :=
  (map : C → D)
  (fmap : Π {A B : C}, Mor A B → Mor (map A) (map B))
  (fmap_prevs_comp : ∀ {A₁ A₂ A₃ : C} (f₁ : Mor A₂ A₃) (f₂ : Mor A₁ A₂) , fmap (f₁ ∘ₘ f₂) = (fmap f₁) ∘ₘ (fmap f₂))
  (fmap_prevs_id : ∀ A : C, fmap (id A) = id (map A))

notation C ` +→ `:80 D:80 := functor C D

def functor_comp {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} [category.{v₁} C₁] [category.{v₂} C₂] [category.{v₃} C₃]
  (F₁ : C₂ +→ C₃) (F₂ : C₁ +→ C₂) : C₁ +→ C₃ := 
{
  map := (λ o, F₁.map (F₂.map o)),
  fmap := (λ A B f , F₁.fmap  (F₂.fmap f)),
  fmap_prevs_comp := 
    begin
      intros A₁ A₂ A₃ f₁ f₂,
      rw F₂.fmap_prevs_comp,
      rw F₁.fmap_prevs_comp,
    end,
  fmap_prevs_id :=
    begin
      intro A,
      rw F₂.fmap_prevs_id,
      rw F₁.fmap_prevs_id,
    end,
}

notation C ` ⊚ `:80 D:80 := functor_comp C D

structure natural_transformation {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] (F₁ F₂ : C +→ D) :=
  (map : Π c : C, Mor (F₁.map c) (F₂.map c))
  (natural : ∀ (c : C) {c' : C} (f : Mor c c'), (F₂.fmap f) ∘ₘ (map c)  = (map c') ∘ₘ (F₁.fmap f))

notation F₁ ` →ₙ `:80 F₂:80 := natural_transformation F₁ F₂

end category