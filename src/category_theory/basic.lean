
universes v u v₁ u₁ v₂ u₂ v₃ u₃

/-
  notation: C +→ D = functor from C to D
  notation: F₁ →ₙ F₂ = natural transformation from F₁ to F₂
-/

class category (obj : Type u ) : Type (max u (v+1)) :=
  (Mor : obj → obj → Type v)
  (comp : Π {A B C : obj}, Mor B C → Mor A B → Mor A C)
  (idₘ : Π A : obj, Mor A A)
  (comp_assoc : ∀ {A B C D: obj} (f₁ : Mor A B) (f₂ : Mor B C) (f₃ : Mor C D),
     (comp f₃ (comp f₂ f₁)) = comp (comp f₃ f₂) f₁)
  (id_comp_left : ∀ {A B : obj} (f : Mor A B), comp (idₘ B) f = f)
  (id_comp_right : ∀ {A B : obj} (f : Mor A B), comp f (idₘ A) = f)


namespace category

notation f ` ∘ₘ `:80 g:80 := category.comp f g

structure functor (C : Type u₁) (D : Type u₂) [category.{v₁} C] [category.{v₂} D] :=
  (map : C → D)
  (fmap : Π {A B : C}, Mor A B → Mor (map A) (map B))
  (fmap_prevs_comp : ∀ {A₁ A₂ A₃ : C} (f₁ : Mor A₂ A₃) (f₂ : Mor A₁ A₂) , fmap (f₁ ∘ₘ f₂) = (fmap f₁) ∘ₘ (fmap f₂))
  (fmap_prevs_id : ∀ A : C, fmap (idₘ A) = idₘ (map A))

notation C ` +→ `:80 D:80 := functor C D

def faithful_functor {C : Type u₁} {D: Type u₂} [category.{v₁} C] [category.{v₂} D] (F : C +→ D) : Prop 
  := ∀ (A B : C) (f g : Mor A B) , F.fmap f = F.fmap g → f = g 

def equal_to_morphism {C : Type u} [category.{v} C] {A B : C} : A = B → Mor A B :=
begin
  intro h,
  rw h,
  exact idₘ B,
end

theorem functor_equality {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] (F₁ F₂ : C +→ D) 
  : F₁.map = F₂.map → F₁.fmap == F₂.fmap → F₁ = F₂ :=
begin
  cases F₁,
  cases F₂,
  intros h₁ h₂,
  simp,
  split,
  exact h₁,
  exact h₂,
end


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

def id_func (C : Type u) [category.{v} C] : C +→ C :=
{
  map := id,
  fmap := λ _ _, id,
  fmap_prevs_comp :=
    begin
      intros A₁ A₂ A₃ f₁ f₂,
      refl,
    end,
  fmap_prevs_id :=
    begin
      intro,
      refl,
    end,
} 

structure natural_transformation {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] (F₁ F₂ : C +→ D) :=
  (map : Π c : C, Mor (F₁.map c) (F₂.map c))
  (natural : ∀ (c : C) {c' : C} (f : Mor c c'), (F₂.fmap f) ∘ₘ (map c)  = (map c') ∘ₘ (F₁.fmap f))

notation F₁ ` →ₙ `:80 F₂:80 := natural_transformation F₁ F₂

theorem natural_trans_equality {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F₁ F₂ : C +→ D} {φ₁ φ₂: F₁ →ₙ F₂} 
  : φ₁.map = φ₂.map → φ₁ = φ₂ :=
begin
  intro h,
  cases φ₁,
  cases φ₂,
  rw natural_transformation.mk.inj_eq,
  exact h,
end

def natural_trans_comp {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F₁ F₂ F₃: C +→ D} 
  : F₂ →ₙ F₃ → F₁ →ₙ F₂ → F₁ →ₙ F₃ := λ (φ₁ : F₂ →ₙ F₃) (φ₂ : F₁ →ₙ F₂),
{
  map := λ c : C, (φ₁.map c) ∘ₘ (φ₂.map c),
  natural := 
    begin
      intros c c' f,
      rw comp_assoc,
      rw φ₁.natural,
      rw ← comp_assoc,
      rw φ₂.natural,
      rw comp_assoc,
    end,
}

notation φ₁ ` ∘ₙ `:80 φ₂:80 := natural_trans_comp φ₁ φ₂

@[simp]
theorem natural_trans_comp_map {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F₁ F₂ F₃: C +→ D}
  (φ₁ : F₂ →ₙ F₃) (φ₂ : F₁ →ₙ F₂) : ∀ c : C, (φ₁ ∘ₙ φ₂).map c = (φ₁.map c) ∘ₘ (φ₂.map c) :=
begin
  intro,
  refl,
end

def idₙ {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D](F : C +→ D) : F →ₙ F :=
{
  map := λ c, idₘ (F.map c),
  natural := 
    begin
      intros c c' f,
      rw id_comp_right,
      rw id_comp_left,
    end,
}

@[simp]
theorem natural_trans_id_map {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F : C +→ D} 
  : ∀ c : C, (idₙ F).map c = idₘ (F.map c) :=
begin
  intro c,
  refl,
end

def natural_isomorphism {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F₁ F₂ : C +→ D} 
  (φ : F₁ →ₙ F₂) : Prop := ∃ ψ : F₂ →ₙ F₁, φ ∘ₙ ψ = idₙ F₂ ∧ ψ ∘ₙ φ = idₙ F₁    

def isomorphism {C : Type u} [category.{v} C] {A B : C} : Mor A B → Prop 
  := λ f, ∃ g : Mor B A, f ∘ₘ g = idₘ B ∧ g ∘ₘ f = idₘ A 

def epimorphism {C : Type u} [category.{v} C] {A₁ A₂ A₃ : C} : Mor A₁ A₂ → Prop
  := λ f, ∀ {g₁ g₂ : Mor A₂ A₃}, g₁ ∘ₘ f = g₂ ∘ₘ f → g₁ = g₂

def monomorphism {C : Type u} [category.{v} C] {A₁ A₂ A₃ : C} : Mor A₂ A₃ → Prop 
  := λ f, ∀ {g₁ g₂ : Mor A₁ A₂}, f ∘ₘ g₁ = f ∘ₘ g₂ → g₁ = g₂



end category