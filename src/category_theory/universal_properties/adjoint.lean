import category_theory.basic
import category_theory.instances

universes v v₁ v₂ u u₁ u₂

namespace category

/-
  Will build theory about adjoint functors.
-/


def morphism_bifunctor (C : Type u) [category.{v} C] : ((opposite C) × C) +→ Type v :=
{
  map := λ p, Mor p.1.val p.2,
  fmap := λ p₁ p₂ pf, λ g, pf.2 ∘ₘ g ∘ₘ pf.1,
  fmap_prevs_id := 
    begin
      intro p,
      apply funext,
      intro g,
      have hrw : idₘ p.1 = 
        (idₘ p.1.val :Mor p.1.val p.1.val) := rfl,
      simp [hrw,prod_cat_id,id_comp_left,id_comp_right],
      refl,
    end,
  fmap_prevs_comp := 
    begin
      intros p₁ p₂ p₃ pf₁ pf₂,
      apply funext,
      intro φ,
      simp [prod_cat_comp,set_comp_app],
      simp [← comp_assoc],
      refl,
    end,
}

def insert_fuctor_in_mor_left {C₁ : Type u₁} {C₂ : Type u₂} [category.{v₁} C₁] [category.{v₂} C₂]
  (F : C₂ +→ C₁) : ((opposite C₂) × C₁) +→ Type v₁
  := (morphism_bifunctor C₁) ⊚ ((product_functor (op_functor F) (id_func C₁)) 
    : (opposite C₂ × C₁) +→ (opposite C₁ × C₁)) 

def insert_fuctor_in_mor_right {C₁ : Type u₁} {C₂ : Type u₂} [category.{v₁} C₁] [category.{v₂} C₂]
  (F : C₂ +→ C₁) : ((opposite C₁) × C₂) +→ Type v₁
  := (morphism_bifunctor C₁) ⊚ ((product_functor (op_functor (id_func C₁)) F)
    : (opposite C₁ × C₂) +→ (opposite C₁ × C₁))

structure adjunction {C₁ : Type u₁} {C₂ : Type u₂} [category.{v} C₁] [category.{v} C₂]
  (F : C₂ +→ C₁) (G : C₁ +→ C₂) := 
  (body: Mor (insert_fuctor_in_mor_left F) (insert_fuctor_in_mor_right G)) 
  (iso : isomorphism body)

infix ` ⊣ `:15 := adjunction

def adj_counit {C₁ : Type u₁} {C₂ : Type u₂} [category.{v} C₁] [category.{v} C₂]  
  {F : C₂ +→ C₁} {G : C₁ +→ C₂} (φ : F ⊣ G) : F ⊚ G →ₙ (id_func C₁)

end category