import topology.basic
import topology.instances.basic
import misc.set

namespace topology

universe u

open set

def is_cover {X : Type u} : set (set X) → Prop
  := λ s, ∀ x : X , ∃ t : set X , t ∈ s ∧ x ∈ t

def is_subcover {X : Type u} (s : set (set X)) : set (set X) → Prop := λ t, is_cover t ∧ t ⊆ s

def all_open_set {X : Type u} [topology X] (s : set (set X)) : Prop := ∀ t : set X, t ∈ s → is_open t

def compact_space (X : Type u) [topology X] : Prop 
  := ∀ t : set (set X), (is_cover t) ∧ (all_open_set t) → ∃ xs : list (set X), (list_to_set xs) ⊆ t ∧ (is_subcover t (list_to_set xs))

def compact_set {X : Type u} [topology X] (S : set X) : Prop := compact_space (subtype S)

def hausdorff (X : Type u) [topology X] : Prop
  := ∀ x y : X, x ≠ y → ∃ U_x U_y : set X, (is_open U_x) ∧ (is_open U_y) ∧ (x ∈ U_x) ∧ (y ∈ U_y) ∧ (U_x ∩ U_y = ∅)

end topology