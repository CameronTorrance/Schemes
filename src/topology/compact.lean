import topology.basic
import topology.instances.basic
import topology.properties
import misc.set

namespace topology

universe u

open set

theorem finite_union_of_compact_sets_compact {X : Type u} [topology X] 
  : ∀ {l : list (set X)}, is_cover (list_to_set l) → (∀ {S}, S ∈ l → compact_set S) → compact_space X := sorry

end topology