import category_theory.basic
import misc.matrix

universes v u

/-
  defn enough graph theory for category theory purposes.
-/

structure graph :=
(vertex_set : Type u)
(edge_set :  Π v₁ v₂ : vertex_set, Type v)

namespace graph

inductive path {Γ : graph.{v u}} : Γ.vertex_set → Γ.vertex_set → Type (max v u) 
| empty : Π v : Γ.vertex_set, path v v
| step  : Π {v₁ v₂ v₃ : Γ.vertex_set}, Γ.edge_set v₂ v₃ → path v₁ v₂ → path v₁ v₃

def concat {Γ : graph.{v u}} : Π {v₁ v₂ v₃ : Γ.vertex_set}, path v₂ v₃ → path v₁ v₂ 
  → path v₁ v₃ 
| v₁ v₂ .(v₂) (path.empty .(v₂)) p  := p 
| v₁ v₂   v₃  (path.step e p₁)   p₂ := path.step e (concat p₁ p₂)

def path_cat (Γ : graph.{v u}) : Type u := Γ.vertex_set 

open category

instance path_category (Γ : graph.{v u}) : category.{max v u} (path_cat Γ) :=
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

theorem path_cat_id {Γ :graph.{v u} }: ∀ v : path_cat Γ , path.empty v = idₘ v := λ _, rfl

theorem path_cat_step_comp {Γ :graph.{v u} } {v₁ v₂ v₃ v₄: path_cat Γ} 
  : ∀ (e : Γ.edge_set v₃ v₄) (p : Mor v₂ v₃) (p': Mor v₁ v₂), 
  ((path.step e p) ∘ₘ p' :Mor v₁ v₄) = path.step e (p ∘ₘ p') := λ _ _ _, rfl

structure graph_mor (Γ₁ Γ₂ : graph.{v u}) : Type (max v u) :=
(vertex_map : Γ₁.vertex_set → Γ₂.vertex_set)
(edge_map : Π {v₁ v₂ : Γ₁.vertex_set}, 
  Γ₁.edge_set v₁ v₂ → Γ₂.edge_set (vertex_map v₁) (vertex_map v₂))

def id_graph_mor (Γ : graph.{v u}) : graph_mor Γ Γ :=
{
  vertex_map := id,
  edge_map := λ _ _,id,
}

def graph_mor_comp {Γ₁ Γ₂ Γ₃  : graph.{v u}} (φ₁ : graph_mor Γ₂ Γ₃) (φ₂ : graph_mor Γ₁ Γ₂) : graph_mor Γ₁ Γ₃ :=
{
  vertex_map := φ₁.vertex_map ∘ φ₂.vertex_map,
  edge_map   := λ _ _ e, φ₁.edge_map (φ₂.edge_map e),
}

instance graph_category : category.{(max v u)} graph.{v u} :=
{
  Mor := graph_mor,
  idₘ := id_graph_mor,
  comp := λ Γ₁ Γ₂ Γ₃, graph_mor_comp,
  comp_assoc :=
    begin
      intros Γ₁ Γ₂ Γ₃ Γ₄ φ₁ φ₂ φ₃,
      cases φ₁,
      cases φ₂,
      cases φ₃,
      simp [graph_mor_comp],
    end,
  id_comp_right :=
    begin
      intros Γ₁ Γ₂ φ,
      cases φ,
      simp[id_graph_mor,graph_mor_comp],
    end,
  id_comp_left := 
    begin
      intros Γ₁ Γ₂ φ,
      cases φ,
      simp[id_graph_mor,graph_mor_comp],
    end,
}

def image_path {Γ₁ Γ₂ : graph.{v u}} (φ : Mor Γ₁ Γ₂): Π {v₁ v₂ : Γ₁.vertex_set} (p : path v₁ v₂), 
  path (φ.vertex_map v₁) (φ.vertex_map v₂)
| v .(v) (path.empty .(v)) := path.empty (φ.vertex_map v)
| v₁ v₂ (path.step e p)    := path.step (φ.edge_map e) (image_path p)

theorem image_path_id {Γ : graph.{v u}} {v₁ v₂ : Γ.vertex_set} (p : path v₁ v₂) 
  : image_path (idₘ Γ) p = p :=
begin
  induction p,
  refl,
  simp[image_path,p_ih],
  split,
  refl,
  split,
  refl,
  refl,
end

def category_to_graph (C : Type u) [category.{v} C] : graph.{v u} :=
{
  vertex_set := C,
  edge_set := Mor, 
}

def path_to_mor {C : Type u} [category.{v} C] : Π {v₁ v₂ : C} 
  (p : @path (category_to_graph C) v₁ v₂), Mor (v₁:C) (v₂: C)
| v .(v) (path.empty .(v)) := idₘ v
| v₁ v₂ (path.step e p)    := e ∘ₘ (path_to_mor p)

def shape {Γ : graph.{v u}} {C : Type u} [category.{v} C] (φ : Mor Γ (category_to_graph C)) 
  : path_cat Γ +→ C :=
{
  map := φ.vertex_map,
  fmap := λ _ _ p, path_to_mor (image_path φ p),
  fmap_prevs_id :=
    begin
      intro v,
      split,
    end,
  fmap_prevs_comp :=
    begin
      intros v₁ v₂ v₃ p₁ p₂,
      induction p₁ with v ,
      simp[path_to_mor,image_path, path_cat_id,id_comp_left],
      simp[← path_cat_id,image_path,path_to_mor,id_comp_left],
      simp[image_path,path_to_mor,p₁_ih,path_cat_step_comp],
      rw comp_assoc,
    end,
}

def matrix_to_graph {n : ℕ} (M : matrix ℕ n n) : graph.{v u} :=
{
  vertex_set := index n,
  edge_set := λ i₁ i₂, index (M.entry i₁ i₂),
}

end graph
