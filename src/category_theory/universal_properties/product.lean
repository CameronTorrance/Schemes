import category_theory.basic
import category_theory.instances
import category_theory.universal_properties.colimit
import misc.graph
import misc.matrix

universes v u vᵢ uᵢ

namespace category

def is_product {C : Type u} [category.{v} C] {I : Type uᵢ} (f : I → C) : 
  (Σ p : C, Π i : I, Mor p (f i)) → Prop 
| ⟨p,j⟩ := ∀ pair : (Σ p : C, Π i : I, Mor p (f i)), ∃! φ : Mor pair.1 p, ∀ i : I, pair.2 i = (j i) ∘ₘ φ

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

class has_products (C : Type u) [category.{v} C]
(all_products_exist : ∀ {I : Type uᵢ} (f : I → C) ,∃ p : (Σ p : C, Π i : I, Mor p (f i)), 
  is_product f p)

def equaliser_edge : index.{u} 2 → index.{u} 2 → Type v
| index.zero (index.succ (index.zero)) := index 2
| _ _                                  := index 0


def equaliser_graph : graph.{v u} :=
{
  vertex_set := index.{u} 2,
  edge_set := equaliser_edge,
}


def is_limit {C : Type u} [category.{v} C] {I : Type uᵢ} [category.{vᵢ} I] 
  (F : I +→ C) : (Σ p : C, Π i : I, Mor p (F.map i) ) → Prop 
| ⟨p,j⟩ := is_colimit (op_functor F) 
  ⟨op p, Π i : (opposite I), ((j i.val) : Mor (op (F.map i.val)) (op p))⟩    



end category