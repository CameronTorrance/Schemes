import category_theory.basic
import category_theory.instances
import category_theory.universal_properties.colimit
import misc.graph
import misc.matrix

universes v u vᵢ uᵢ

open classical

namespace category

def is_product {C : Type u} [category.{v} C] {I : Type uᵢ} (f : I → C) : 
  (Σ p : C, Π i : I, Mor p (f i)) → Prop 
| ⟨p,j⟩ := ∀ pair : (Σ p : C, Π i : I, Mor p (f i)), ∃! φ : Mor pair.1 p, ∀ i : I, pair.2 i = (j i) ∘ₘ φ

-- the following makes is_product a little easier to work with.

theorem is_product_fn {C : Type u} [category.{v} C] {I : Type uᵢ} {f : I → C} 
  {prod :Σ p : C, Π i : I, Mor p (f i)} : is_product f prod → 
  ∀ pair : (Σ p : C, Π i : I, Mor p (f i)), ∃! φ : Mor pair.1 prod.1, 
  ∀ i : I, pair.2 i = (prod.2 i) ∘ₘ φ :=
begin
  intro hprod,
  have hrw : prod = ⟨prod.1,prod.2⟩,
    apply sigma.eq,
    refl,
    refl,
  rw hrw at hprod,
  exact hprod, 
end

theorem pi_type_product {I : Type u} {β : I → Type u} 
  : is_product β ⟨Π i, β i, λ i f, f i⟩ :=
begin
  intro pair,
  cases pair with p' j',
  dsimp,
  existsi  λ x : p', λ i : I, j' i x,
  dsimp,
  split,
  intro i,
  refl,
  intros ψ hψ,
  apply funext,
  intro a,
  apply funext,
  intro i,
  rw hψ,
  rw set_comp_app,
end

theorem product_essentially_unquie {C : Type u} [category.{v} C] {I : Type uᵢ} {f : I → C} 
  {p₁ p₂ :(Σ p : C, Π i : I, Mor p (f i))} : is_product f p₁ → is_product f p₂ 
  → ∃! φ : Mor p₁.1 p₂.1, isomorphism φ ∧ (∀ i : I, p₁.2 i = (p₂.2 i) ∘ₘ φ ):=
begin
  intros hp₁ hp₂,
  cases p₁ with p₁ j₁,
  cases p₂ with p₂ j₂,
  cases hp₂ ⟨p₁,j₁⟩ with φ₁ hφ₁,
  cases hp₁ ⟨p₂,j₂⟩ with φ₂ hφ₂,
  cases hp₁ ⟨p₁, λ i, (j₂ i) ∘ₘ φ₁⟩ with id₁ hid₁,
  cases hp₂ ⟨p₂, λ i, (j₁ i) ∘ₘ φ₂⟩ with id₂ hid₂,
  dsimp at hφ₁,
  dsimp at hφ₂,
  dsimp at hid₁,
  dsimp at hid₂,
  cases hφ₁ with hφ₁ uφ₁,
  cases hφ₂ with hφ₂ uφ₂,
  cases hid₁ with hid₁ uid₁,
  cases hid₂ with hid₂ uid₂,
  have hrw₁ : idₘ p₁ = id₁,
    apply uid₁,
    simp [id_comp_right,← hφ₁],
  have hrw₂ : idₘ p₂ = id₂,
    apply uid₂,
    simp [id_comp_right,← hφ₂],
  existsi φ₁,
  dsimp,
  split,
  split,
  existsi φ₂,
  rw [hrw₁,hrw₂],
  split,
  apply uid₂,
  simp [comp_assoc,hφ₁],
  apply uid₁,
  simp [comp_assoc,hφ₂],
  exact hφ₁,
  intros φ hφ,
  apply uφ₁,
  exact hφ.2,
end

noncomputable def prod_can_iso {C : Type u} [category.{v} C] {I : Type uᵢ} {f : I → C} 
  {p₁ p₂ :(Σ p : C, Π i : I, Mor p (f i))} : is_product f p₁ → is_product f p₂ 
  → Mor p₁.1 p₂.1 := λ hp₁ hp₂, some (product_essentially_unquie hp₁ hp₂)

theorem prod_can_iso_property {C : Type u} [category.{v} C] {I : Type uᵢ} {f : I → C} 
  {p₁ p₂ : (Σ p : C, Π i : I, Mor p (f i))} : Π (hp₁ : is_product f p₁) (hp₂ : is_product f p₂),
  (isomorphism (prod_can_iso hp₁ hp₂) ∧ ( Π i : I, p₁.2 i = p₂.2 i ∘ₘ (prod_can_iso hp₁ hp₂))) 
  ∧ (∀ φ : Mor p₁.1 p₂.1, ((isomorphism φ ∧ ( Π i : I, p₁.2 i = p₂.2 i ∘ₘ φ)) 
  → φ = prod_can_iso hp₁ hp₂)) := λ hp₁ hp₂, some_spec (product_essentially_unquie hp₁ hp₂)

class has_products (C : Type u) [category.{v} C] :=
(all_products_exist : ∀ {I : Type uᵢ} (f : I → C) , ∃ p : (Σ p : C, Π i : I, Mor p (f i)), 
  is_product f p)

noncomputable def product {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I : Type uᵢ} 
  (f : I → C) : (Σ p : C, Π i : I, Mor p (f i)) := some (has_products.all_products_exist f) 

prefix `Π₀`:110 := product

theorem has_product_prod_is_prod {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I : Type uᵢ} 
  (f : I → C) : is_product f (Π₀ f) := some_spec (has_products.all_products_exist f) 

noncomputable def into_product {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I : Type uᵢ} 
  {f : I → C} {A : C} (g : Π i : I, Mor A (f i)) 
  : Mor A (Π₀ f).1 := some (is_product_fn (has_product_prod_is_prod f) ⟨A,g⟩)

theorem into_product_property {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I : Type uᵢ} 
  {f : I → C} {A : C} (g : Π i : I, Mor A (f i)) : (∀ i : I, g i = ((Π₀f).2 i) ∘ₘ (into_product g)) ∧ 
  ∀ φ : Mor A (Π₀f).1, (∀ i, g i = ((Π₀f).2 i) ∘ₘ φ) → φ = into_product g 
  := some_spec (is_product_fn (has_product_prod_is_prod f) ⟨A,g⟩)

theorem into_product_property_comp {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I : Type uᵢ} 
  {f : I → C} {A : C} (g : Π i : I, Mor A (f i)) : ∀ i : I, g i = ((Π₀f).2 i) ∘ₘ (into_product g)
  := (into_product_property g).1

theorem into_product_property_up {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] 
  {I : Type uᵢ} {f : I → C} {A : C} (g : Π i : I, Mor A (f i)) 
  : ∀ φ : Mor A (Π₀f).1, (∀ i, g i = ((Π₀f).2 i) ∘ₘ φ) → φ = into_product g 
  := (into_product_property g).2

theorem double_prod_prod_left {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I J : Type uᵢ} 
  (f : I → J → C) : is_product (function.uncurry f) ⟨(Π₀ (λ i : I,(Π₀ (λ j : J,f i j)).1)).1, 
  λ ij : I × J, (Π₀ (λ k : J, f ij.1 k)).2 ij.2 ∘ₘ (Π₀ (λ i : I,(Π₀ (λ j : J,f i j)).1)).2 ij.1⟩ := 
begin
  simp[is_product],
  intro,
  cases pair with p g,
  let φ : Mor p (Π₀ (λ i : I,(Π₀ (λ j : J,f i j)).1)).1,
    apply into_product,
    intro i,
    apply into_product,
    intro j,
    exact g (i,j),
  existsi φ,
  simp[φ],
  split,
  intro ij,
  cases ij with i j,
  rw ← comp_assoc,
  simp[← into_product_property_comp],
  intros ψ hψ,
  apply into_product_property_up,
  intro i,
  symmetry,
  apply into_product_property_up,
  intro j,
  rw hψ (i,j),
  rw comp_assoc,
end

theorem double_prod_prod_right {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I J : Type uᵢ} 
  (f : I → J → C) : is_product (function.uncurry f) ⟨(Π₀ (λ j : J ,(Π₀ (λ i : I,f i j)).1)).1, 
  λ ij : I × J, (Π₀ (λ k : I, f k ij.2)).2 ij.1 ∘ₘ (Π₀ (λ j : J ,(Π₀ (λ i : I,f i j)).1)).2 ij.2⟩ := 
begin
  simp[is_product],
  intro,
  cases pair with p g,
  let φ : Mor p (Π₀ (λ j : J,(Π₀ (λ i : I,f i j)).1)).1,
    apply into_product,
    intro j,
    apply into_product,
    intro i,
    exact g (i,j),
  existsi φ,
  simp[φ],
  split,
  intro ij,
  cases ij with i j,
  rw ← comp_assoc,
  simp[← into_product_property_comp],
  intros ψ hψ,
  apply into_product_property_up,
  intro j,
  symmetry,
  apply into_product_property_up,
  intro i,
  rw hψ (i,j),
  rw comp_assoc,
end

theorem product_of_morphisms_exist {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] {I : Type uᵢ} 
  {f₁ f₂ : I → C} (φ : Π i : I, Mor (f₁ i) (f₂ i)) : ∃! ψ : Mor (Π₀ f₁).1 (Π₀ f₂).1, ∀ i : I,
  (Π₀ f₂).2 i ∘ₘ ψ = φ i ∘ₘ (Π₀ f₁).2 i :=
begin
  let ψ : Mor (Π₀ f₁).1 (Π₀ f₂).1,
    apply into_product,
    intro i,
    exact φ i ∘ₘ (Π₀ f₁).2 i,
  existsi ψ,
  simp[ψ], 
  split,
  simp[← into_product_property_comp],
  intros ϕ hϕ,
  apply into_product_property_up,
  simp [hϕ],
end

noncomputable def product_of_morphisms {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] 
  {I : Type uᵢ} {f₁ f₂ : I → C} (φ : Π i : I, Mor (f₁ i) (f₂ i)) : Mor (Π₀f₁).1 (Π₀f₂).1 := 
  some (product_of_morphisms_exist φ)

prefix `Πₘ`:110 := product_of_morphisms

theorem product_of_morphisms_property {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] 
  {I : Type uᵢ} {f₁ f₂ : I → C} (φ : Π i : I, Mor (f₁ i) (f₂ i))
  : (∀ i : I, (Π₀ f₂).2 i ∘ₘ Πₘ φ = φ i ∘ₘ (Π₀ f₁).2 i) ∧ (∀ ψ : Mor (Π₀f₁).1 (Π₀f₂).1,
  (∀ i : I, (Π₀ f₂).2 i ∘ₘ ψ  = φ i ∘ₘ (Π₀ f₁).2 i) → ψ = Πₘ φ) 
  := some_spec (product_of_morphisms_exist φ)

theorem product_of_morphisms_property_comp {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] 
  {I : Type uᵢ} {f₁ f₂ : I → C} (φ : Π i : I, Mor (f₁ i) (f₂ i))
  : ∀ i : I, (Π₀ f₂).2 i ∘ₘ Πₘ φ = φ i ∘ₘ (Π₀ f₁).2 i := (product_of_morphisms_property φ).1

theorem product_of_morphisms_property_up {C : Type u} [category.{v} C] [has_products.{v u uᵢ} C] 
  {I : Type uᵢ} {f₁ f₂ : I → C} (φ : Π i : I, Mor (f₁ i) (f₂ i))
  : ∀ ψ : Mor (Π₀f₁).1 (Π₀f₂).1, (∀ i : I, (Π₀ f₂).2 i ∘ₘ ψ  = φ i ∘ₘ (Π₀ f₁).2 i) 
  → ψ = Πₘ φ := (product_of_morphisms_property φ).2

def is_equaliser {C : Type u} [category.{v} C] {A B : C} (f₁ f₂ : Mor A B) : (Σ E, Mor E A) → Prop 
| ⟨E,f⟩ := f₁ ∘ₘ f = f₂ ∘ₘ f ∧ ∀ p : (Σ E, Mor E A), f₁ ∘ₘ p.2 = f₂ ∘ₘ p.2 
  → ∃! φ : Mor p.1 E, p.2 = f ∘ₘ φ

end category