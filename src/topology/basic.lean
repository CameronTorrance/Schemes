import misc.set

namespace topology

open set
open classical

universes u v

class topology (X : Type u) :=
(is_open : set X → Prop)
(whole_space_open : is_open univ)
(empty_set_open : is_open ∅)
(arbitary_unions_open (s: set (set X)) : (∀ t : set X, t ∈ s → is_open t) → is_open (⋃₀ s))
(pairwise_inters_open : ∀ s t : set X, is_open s → is_open t → is_open (s ∩ t))

def is_open {X : Type u} [T_X: topology X] : set X → Prop := T_X.is_open


def is_continous_map {X : Type u} {Y : Type v}[T_X : topology X][T_Y : topology Y] (f : X → Y) : Prop :=
∀ s : set Y , is_open s → is_open (pre_image f s)

/-
  Alternative way of building topologies.
-/







/-
  Some results about the category of open sets 
-/



end topology