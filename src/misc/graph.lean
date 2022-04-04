
import category_theory.basic

universes u

/-
  defn enough graph theory for category theory purposes.
-/

structure graph :=
(vertex_set : Type u)
(edge_set :  Π v₁ v₂ : vertex_set, Type u)

namespace graph

inductive path {Γ : graph.{u}} : Γ.vertex_set → Γ.vertex_set → Type u 
| empty : Π v : Γ.vertex_set, path v v
| step  : Π {v₁ v₂ v₃ : Γ.vertex_set}, Γ.edge_set v₂ v₃ → path v₁ v₂ → path v₁ v₃


def concat {Γ : graph.{u}} : Π {v₁ v₂ v₃ : Γ.vertex_set}, path v₂ v₃ → path v₁ v₂ 
  → path v₁ v₃ 
| v₁ v₂ .(v₂) (path.empty .(v₂)) p  := p 
| v₁ v₂   v₃  (path.step e p₁)   p₂ := path.step e (concat p₁ p₂)

def path_cat (Γ : graph.{u}) : Type u := Γ.vertex_set 

instance path_category (Γ : graph.{u}) : category.{u} (path_cat Γ) :=
{
  Mor := λ v₁ v₂ : path_cat Γ,  path v₁ v₂,
  comp := λ v₁ v₂ v₃ f₁ f₂, concat f₁ f₂,
  idₘ := λ v, path.empty v,
  comp_assoc :=
    begin
      intros v₁ v₂ v₃ v₄ p₁ p₂ p₃,
      induction p₃ with v v₁ v₂ v e p ind,
      simp[concat],
      simp[concat],
      split,
      refl,
      rw ind p₂,
    end,
  id_comp_right :=
    begin
      intros v₁ v₂ p,
      induction p,
      refl,
      simp[concat],
      split,
      refl,
      rw p_ih,
    end,
  id_comp_left := λ _ _ _,rfl,
}


end graph
