import misc.prop

namespace set

universes u v

open inhabited
open classical
open subtype
open list

/-
  Useful set theortic operations not inculded in the standard libary that are needed to prove results about
  commuative rings and toplogical spaces. 
-/

-- This result was for some dumb reson a protected lemma in the subtype file.

lemma val_injective {X : Type u} {S : set X} : ∀ {a1 a2 : subtype S}, val a1 = val a2 → a1 = a2
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

@[reducible]
def choice_function {X : Type u} (f : {S : set X // ∃ x : X, x ∈ S} → X ) : Prop := ∀ S, f S ∈ S.val

@[reducible]
def sInter {α : Type u} (s : set (set α)) : set α := {t | ∀ a ∈ s, t ∈ a}
prefix `⋂₀`:110 := sInter

@[reducible]
def pre_image {X : Type u} {Y : Type v} (f : X → Y) (U_Y : set Y) : set X := λ x : X, f x ∈ U_Y

@[reducible]
def include_subset {X : Type u} {S : set X} : set (subtype S) → set X 
  := λ s, λ x : X, (∃ y : subtype S, y ∈ s ∧ y.val = x)

@[reducible]
def ghost_subset {X : Type u} (S : set X) : set X → set (subtype S)
  := λ T : set X, λ s : subtype S, ∃ x : X, x ∈ T ∧ s.val = x 

@[reducible]
def list_to_set {X : Type u} : list X → set X := λ xs, λ t, t ∈ xs

@[reducible]
def set_singleton {X: Type u} (x : X) : set X := λ a, a = x
/-
  Proof that there is a choice function.
-/

lemma there_is_choice_function {X : Type u} : ∃ f : {S : set X //  ∃ x : X, x ∈ S} → X, choice_function f :=
begin
  let fdat := λ S : {S : set X // ∃ x : X, x ∈ S}, subtype.mk (some S.property) (some_spec S.property),
  existsi (λ S, (fdat S).val),
  intro S,
  exact (fdat S).property,
end

/-
  Some trival results about subsets and set eqaulity so I'm not alway having to apply funext/propext
  to every lemma.
-/

theorem setext {X : Type u} {A B : set X} : (∀ x : X, (x ∈ A → x ∈ B) ∧ (x ∈ B → x ∈ A)) → A = B :=
begin
    intro h,
    apply funext,
    intro x,
    apply propext,
    exact ⟨and.left (h x), and.right (h x)⟩, 
end

theorem subset_reflexive {X : Type u} {A : set X} : A ⊆ A := λ x ha, ha

theorem subset_antisymmetric {X : Type u} {A B : set X} : A ⊆ B ∧ B ⊆ A → A = B := 
begin
  intro h,
  cases h with hAinB hBinA, 
  apply setext,
  intro x,
  exact ⟨λ ha, hAinB ha, λ hb, hBinA hb⟩, 
end

theorem subset_transitive {X : Type u} {A B C: set X} : (A ⊆ B) → (B ⊆ C) → A ⊆ C := 
begin
  intros hAinB hBinC,
  intros x h,
  exact hBinC (hAinB h),
end

theorem empty_set_subset {X : Type u} {A : set X} : ∅ ⊆ A :=
begin
  intros x hx,
  exact false.elim hx,
end

theorem set_subset_of_univ {X : Type u} {A : set X} : A ⊆ univ :=
begin
  intros a ha,
  trivial,
end

theorem not_empty_set_has_element {X : Type u} {S : set X} : S ≠ ∅ → ∃ x : X, x ∈ S :=
begin
  intro nS,
  by_contradiction hraw,
  let h := forall_not_of_not_exists hraw,
  have eS : S = ∅,
  apply setext,
  intro x,
  split,
  intro hx,
  exact (h x) hx,
  intro ab,
  exact false.elim ab,
  exact nS eS,
end

/-
  A couple of simple results about singletons
-/

theorem single_value_in_singleton {X : Type u} {x : X} : ∀ a : X, a ∈ set_singleton x → a = x :=
  λ a ha, ha

theorem nonempty_subset_singleton_equality {X : Type u} {x : X} : ∀ S : set X, S ⊆ set_singleton x ∧ S ≠ ∅ → S = set_singleton x :=
begin
  intros S hS,
  cases hS with hS nS,
  apply subset_antisymmetric,
  split,
  exact hS,
  let a := some (not_empty_set_has_element nS),
  let ha : a ∈ S := some_spec (not_empty_set_has_element nS),
  let hx : a = x := single_value_in_singleton a (hS ha),
  rw hx at ha,
  intros b hb,
  let hbisx : b = x := single_value_in_singleton b hb,
  rw ← hbisx at ha,
  exact ha,
end

/-
  Simple results involving the intersection and union operators.
-/

private lemma half_intersection_commuative {X : Type u} (A B : set X) : A ∩ B ⊆ B ∩ A :=
begin
  intros x hx,
  cases hx with hxinA hxinB,
  exact ⟨hxinB,hxinA⟩,
end

private lemma half_union_commuative {X : Type u} (A B : set X) : A ∪ B ⊆ B ∪ A :=
begin
  intros x hx,
  cases hx,
  right,
  exact hx,
  left,
  exact hx,
end

theorem intersection_commuative {X : Type u} (A B : set X) : A ∩ B = B ∩ A :=
begin
  apply subset_antisymmetric,
  exact ⟨half_intersection_commuative A B, half_intersection_commuative B A⟩, 
end

theorem union_commuative {X : Type u} {A B : set X} : A ∪ B = B ∪ A :=
begin
  apply subset_antisymmetric,
  exact ⟨half_union_commuative A B, half_union_commuative B A⟩, 
end

theorem intersection_in_set {X : Type u} {A B : set X} : A ∩ B ⊆ A :=
begin
  intros x hx,
  cases hx with hxinA hxinB,
  exact hxinA,
end

theorem bound_in_bounded_intersection {X : Type u} {α : set (set X)} {V : set X} : (∀ U : set X, U ∈ α → V ⊆ U) → V ⊆ ⋂₀ α :=
begin
  intros h x hx U hU,
  exact h U hU hx,
end

theorem intersection_lower_bound {X : Type u} {α : set (set X)} : ∀ U : set X, U ∈ α → ⋂₀ α ⊆ U :=
begin
  intros U hU x hx,
  exact hx U hU,
end

theorem set_in_union {X : Type u} {A B : set X} : A ⊆ A ∪ B :=
begin
  intros x hx,
  left,
  exact hx,
end

theorem bounded_union_in_bound {X : Type u} {α : set (set X)} {V : set X} : (∀ U : set X, U ∈ α → U ⊆ V) → ⋃₀ α ⊆ V :=
begin
  intros h x hx,
  cases hx with U hU,
  cases hU with hU hx,
  exact h U hU hx,
end

theorem union_upper_bound {X : Type u} {α : set (set X)} : ∀ U : set X, U ∈ α → U ⊆ ⋃₀ α :=
begin
  intros U hUinα x hxinU,
  existsi U,
  existsi hUinα,
  exact hxinU,
end


theorem intersection_subset {X : Type u} {A B : set X} : A ⊆ B → B ∩ A = A :=
begin
  intro h,
  rw intersection_commuative,
  apply subset_antisymmetric,
  split,
  apply intersection_in_set,
  intros x hx,
  exact ⟨hx,h hx⟩,
end

theorem intersection_empty_set {X : Type u} {A : set X} : ∅ ∩ A = ∅ :=
begin
  rw intersection_commuative,
  apply intersection_subset empty_set_subset,
end

theorem empty_intersection {X : Type u} : ⋂₀ (∅ : set (set X)) = univ :=
begin
  apply subset_antisymmetric,
  split,
  apply set_subset_of_univ,
  intros x trv,
  intros A hA,
  apply false.elim,
  exact hA,
end 

theorem empty_union {X : Type u} : ⋃₀ (∅ : set (set X)) = ∅ :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with A hA,
  cases hA with ab _,
  exact ab,
  apply empty_set_subset,
end

theorem union_subset {X : Type u} {A B : set X} : A ⊆ B → B ∪ A = B :=
begin
  intro h,
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx,
  exact hx,
  exact h hx,
  apply set_in_union,
end

lemma image_membership {X : Type u} {Y : Type v} {f : X → Y} {s : set X} : ∀ {x}, x ∈ s → f x ∈ image (λ y, f y) s :=
begin
  intros x hx,
  split,
  split,
  exact hx,
  refl,
end

lemma not_empty_image_not_empty {X : Type u} {Y : Type v} (f : X → Y) {s : set X} (ns : s ≠ ∅) 
  : (image f s) ≠ ∅ :=
begin
  let x := some (not_empty_set_has_element ns),
  have hx : x ∈ s := some_spec (not_empty_set_has_element ns),
  have hfx : f x ∈ image f s,
    existsi x,
    exact ⟨hx,rfl⟩,
  intro ab,
  rw ab at hfx,
  assumption,
end

theorem intersection_dis_over_union {X : Type u} (C : set (set X)) (A : set X) : (⋃₀ C) ∩ A = ⋃₀ (image (λ B, B ∩ A) C) :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with hxinU hxinA,
  cases hxinU with W hW,
  have hWinC := some hW,
  have hxinW := some_spec hW,
  split,
  have hxinI : x ∈ W ∩ A,
    split,
    exact hxinW,
    exact hxinA,
  have hWinim : W ∩ A ∈ image (λ B, B ∩ A) C,
    apply image_membership,
    exact hWinC,
  existsi hWinim,
  exact hxinI,
  intros x hx,
  cases hx with D hD,
  cases hD with hDinim hxinD,
  cases hDinim with B hB,
  cases hB with hBinC hBAisD,
  rw ← hBAisD at hxinD,
  cases hxinD with hxinB hxinA,
  split,
  split,
  existsi hBinC,
  exact hxinB,
  exact hxinA,
end


theorem set_int_set_set {X : Type u} (A : set X) : A ∩ A = A :=
begin
  apply subset_antisymmetric,
  split,
  apply intersection_in_set,
  intros a ha,
  exact ⟨ha,ha⟩,
end

theorem intersection_assoc {X : Type u} (A B C : set X) : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with hxinA hxinAB,
  cases hxinAB with hxinB hxinC,
  exact ⟨⟨hxinA, hxinB⟩,hxinC⟩,
  intros x hx,
  cases hx with hxinAB hxinC,
  cases hxinAB with hxinA hxinB,
  exact ⟨hxinA,hxinB,hxinC⟩,  
end

theorem list_to_set_pair_mem {X : Type u} (A B : set X) : A ∈ list_to_set [A,B] ∧ B ∈ list_to_set [A,B] :=
begin
  split,
  have trvA : A ∈ [A,B],
    simp,
  exact trvA,
  have trvB : B ∈ [A,B],
    simp,
  exact trvB,
end

@[simp]
theorem list_to_set_nil (X : Type u) : list_to_set nil = (∅ :set X) := rfl

@[simp]
theorem image_of_empty {A : Type u} {B : Type v} (f : A → B) : image f ∅ = ∅ := 
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with a ha,
  cases ha,
  apply false.elim,
  exact ha_left,
  apply empty_set_subset,
end

theorem image_dis_over_union {A : Type u} {B : Type v} (f : A → B) {A₁ A₂ : set A} : image f (A₁ ∪ A₂) = (image f A₁) ∪ (image f A₂) := 
begin
  apply subset_antisymmetric,
  split,
  intros b hb,
  cases hb with a ha,
  cases ha with ha hrw,
  rw ← hrw,
  cases ha,
  left,
  apply image_membership,
  exact ha,
  right,
  apply image_membership,
  exact ha,
  intros b hb,
  cases hb,
  cases hb with a ha,
  cases ha with ha hrw,
  rw ← hrw,
  apply image_membership,
  left,
  exact ha,
  cases hb with a ha,
  cases ha with ha hrw,
  rw ← hrw,
  apply image_membership,
  right,
  exact ha,
end

theorem image_of_singleton {A : Type u} {B : Type v} (f : A → B) (a : A) 
  : image f (λ x, x = a) = (λ x, x = f a) :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with y hy,
  cases hy with hy₁ hy₂,
  have trv : y = a := hy₁,
  rw trv at hy₂,
  exact symm hy₂,
  intros x hx,
  have trv : x = f a := hx,
  rw trv,
  apply image_membership,
  split,
end 

@[simp]
theorem list_to_set_cons {A : Type u} (a : A) (l : list A) : list_to_set (a :: l) = (λ x, x = a) ∪ (list_to_set l) := rfl

theorem image_of_list_to_set {A : Type u} {B : Type v} (f : A → B) (l: list A) 
  : image f (list_to_set l) = list_to_set (map f l) :=
begin
  induction l with a l hl,
  simp,
  simp [map],
  rw [image_dis_over_union,hl],
  rw image_of_singleton,
end

theorem sunion_to_union {X : Type u} {A B : set X} : ⋃₀ (list_to_set [A,B]) = A ∪ B :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with S hS,
  cases hS with hSlist hxinS,
  cases hSlist,
  left,
  rw ← hSlist,
  exact hxinS,
  cases hSlist,
  right,
  rw hSlist at hxinS,
  exact hxinS,
  apply false.elim,
  exact hSlist,
  intros x hx,
  cases hx,
  existsi A,
  existsi and.left (list_to_set_pair_mem A B),
  exact hx,
  existsi B,
  existsi and.right (list_to_set_pair_mem A B),
  exact hx,
end

theorem sinter_to_inter {X : Type u} {A B : set X} : ⋂₀ (list_to_set [A,B]) = A ∩ B :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  have trvA : x ∈ A,
    apply intersection_lower_bound,
    exact and.left (list_to_set_pair_mem A B),
    exact hx,
  have trvB : x ∈ B,
    apply intersection_lower_bound,
    exact and.right (list_to_set_pair_mem A B),
    exact hx,
  exact ⟨trvA,trvB⟩,
  intros x hx,
  cases hx with hxinA hxinB,
  intros S hS,
  cases hS,
  rw hS,
  exact hxinA,
  cases hS,
  rw hS,
  exact hxinB,
  apply false.elim,
  exact hS,
end


/-
  Results about set theoretic difference.
-/

theorem difference_in_numerator {X : Type u} (A : set X) (B : set X) : A \ B ⊆ A :=
begin
  intros x hx,
  cases hx,
  exact hx_left,
end

theorem single_element_diff_nonempty {X : Type u} {A : set X} {B : set X} {x : X} : x ∈ A ∧ x ∉ B → A \ B ≠ ∅ :=
begin
  intro h,
  cases h with h1 h2,
  have hx : x ∈ A \ B,
  split,
  exact h1,
  exact h2,
  intro hc,
  rw hc at hx,
  exact hx,
end 

theorem not_equal_in_terms_of_comp {X : Type u} {A : set X} {B : set X} : A ≠ B → (A \ B ≠ ∅ ) ∨ (B \ A ≠ ∅) :=
begin
  intro nAB,
  by_contradiction,
  have h1 := not_or_and_not h,
  cases h1 with hAraw hBraw,
  have hA := not_not hAraw,
  have hB := not_not hBraw,
  have ab : A = B,
  apply subset_antisymmetric,
  split,
  intros a hainA,
  by_contradiction haninB,
  have ha : a ∈ A \ B,
  exact ⟨hainA, haninB⟩,
  rw hA at ha,
  exact ha,
  intros b hbinB,
  by_contradiction hbninA,
  have hb : b ∈ B \ A,
  exact ⟨hbinB,hbninA⟩,
  rw hB at hb,
  exact hb, 
  exact nAB ab,
end

theorem empty_diff_implies_subset {X : Type u} {A : set X} {B : set X} : A \ B = ∅ → A ⊆ B :=
begin
  intros h1 a ha,
  by_contradiction,
  have ab : a ∈ A \ B,
  exact ⟨ha,h⟩,
  rw h1 at ab,
  exact ab 
end

theorem diff_of_univ_empty {X : Type u} (A : set X) : (A \ univ) = ∅ :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx,
  apply false.elim,
  apply hx_right,
  trivial,
  apply empty_set_subset,
end

theorem diff_by_subset_superset {X : Type u} {A : set X} {B : set X} {B' : set X} (hB'B : B' ⊆ B) : A \ B ⊆ A \ B' :=
begin
  intros x hx,
  cases hx with hxinA hxninB,
  split,
  exact hxinA,
  by_contradiction,
  apply hxninB,
  apply hB'B,
  exact h,
end

theorem empty_set_diff {X : Type u} (A : set X) : A \ ∅ = A :=
begin
  apply subset_antisymmetric,
  split,
  apply difference_in_numerator,
  intros a ha,
  split,
  assumption,
  simp,
  intro ab,
  exact ab,
end

theorem deMorgenUnion {X : Type u} (C : set (set X)) :  univ \ (⋃₀ C) = ⋂₀ image (λ A, univ \ A) C := 
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with trv nxinU,
  have nxinAinC : ∀ A, A ∈ C → x ∉ A,
     have int : ∀ A, ¬ (∃ h : A ∈ C, x ∈ A):= (forall_not_of_not_exists nxinU),
    intro a,
    apply forall_not_of_not_exists,
    exact int a,
  intros S hS,
  cases hS with A hA,
  cases hA with hAinC hrw,
  rw ← hrw,
  simp,
  split,
  trivial,
  apply nxinAinC,
  exact hAinC,
  intros x hx,
  split,
  trivial,
  intro hxinU,
  cases hxinU with A hA,
  cases hA with hAinC hxinA,
  have hcon : x ∈ univ \ A,
    apply intersection_lower_bound,
    have int: univ \ A ∈ image (λ B, univ \ B) C,
      apply image_membership,
      exact hAinC,
    exact int,
    exact hx,
  cases hcon,
  apply hcon_right,
  exact hxinA,
end

theorem deMorgenInter {X : Type u} (C : set (set X)) :  univ \ (⋂₀ C) = ⋃₀ image (λ A, univ \ A) C := 
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with trv₁ nxinI,
  have h₁ := exists_not_of_not_exists nxinI,
  simp at h₁,
  cases h₁ with A hA,
  rw not_implies at hA,
  cases hA with hAinC hxninA,
  existsi univ \ A,
  split,
  existsi A,
  split,
  exact hAinC,
  refl,
  split,
  trivial,
  exact hxninA,
  intros x hx,
  cases hx with A hA,
  cases hA with hAdiff hxinA,
  cases hAdiff with B hB,
  cases hB with hBinC hB,
  simp at hB,
  rw ← hB at hxinA,
  split,
  trivial,
  simp,
  intro hx,
  have hcon : x ∈ B,
    apply hx,
    exact hBinC,
  cases hxinA with h₁ h₂,
  apply h₂,
  exact hcon,
end

/-
  Various technical results about the inculde_subset and subset_ghost functions.
-/

lemma include_empty_is_empty {X : Type u} {S : set X} : @include_subset X S ∅ = ∅ :=
begin
  apply subset_antisymmetric,
  split,
  intros s hs,
  cases hs with sg hsg,
  exact false.elim (and.left hsg),
  apply empty_set_subset,
end

lemma ghost_empty_is_empty {X : Type u} {S : set X} : @ghost_subset X S ∅ = ∅ :=
begin
  apply subset_antisymmetric,
  split,
  intros a ha,
  cases ha with x hx,
  exact false.elim (and.left hx),
  apply empty_set_subset,
end

lemma include_set_in_set {X : Type u} {S : set X} {t : set (subtype S)} : include_subset t ⊆ S :=
begin
  intros x h,
  cases h with xin hxin,
  cases hxin,
  let h₀ := xin.property,
  rw hxin_right at h₀,
  exact h₀,
end

lemma include_univ_is_set {X : Type u} {S : set X} : @include_subset X S univ = S := 
begin
  apply subset_antisymmetric,
  split,
  apply include_set_in_set,
  intros s hs,
  existsi subtype.mk s hs,
  split,
  trivial,
  refl,
end

lemma ghost_set_is_univ {X : Type u} {S : set X} : ghost_subset S S = univ :=
begin
  apply subset_antisymmetric,
  split,
  apply set_subset_of_univ,
  intros x trv,
  existsi x.val,
  split,
  exact x.property,
  refl,
end

lemma include_set_prevs_subset {X : Type u} {S : set X} {α β : set (subtype S)} : α ⊆ β → include_subset α ⊆ include_subset β :=
begin
  intros h s hs,
  cases hs with gs hgs,
  existsi gs,
  exact ⟨h (and.left hgs), and.right hgs⟩,
end

lemma ghost_subset_prev_subset {X : Type u} {S T₁ T₂ : set X} : T₁ ⊆ T₂ → ghost_subset  S T₁ ⊆ ghost_subset S T₂ :=
begin
  intros h s hs,
  cases hs with x hx,
  existsi x,
  exact ⟨h (and.left hx), and.right hx⟩, 
end

lemma include_ghost_id {X : Type u} {S : set X} {α : set (subtype S)} : ghost_subset S (include_subset α) = α :=
begin
  apply subset_antisymmetric,
  split,
  intros s hs,
  cases hs with x hx,
  cases hx with hx svalx,
  cases hx with t ht,
  cases ht with htinα tvalx,
  have hts : t = s,
  apply val_injective,
  rw ← svalx at tvalx,
  exact tvalx,
  rw ← hts,
  exact htinα,
  intros a ha,
  existsi a.val,
  split,
  existsi a,
  exact ⟨ha,rfl⟩,
  refl,
end

lemma ghost_include_id {X : Type u} {S : set X} {T : set X} : T ⊆ S → include_subset (ghost_subset S T) = T :=
begin
  intro h,
  apply subset_antisymmetric,
  split,
  intros y hy,
  cases hy with s hs,
  cases hs with hs svaly,
  cases hs with x hx,
  cases hx with hxinT svalx,
  rw svaly at svalx,
  rw svalx,
  exact hxinT,
  intros x hx,
  existsi subtype.mk x (h hx),
  split,
  existsi x,
  exact ⟨hx, rfl⟩,
  refl, 
end

lemma include_set_prevs_union {X : Type u} {S : set X} (β : set (set (subtype S))) : ⋃₀ (image include_subset β) = include_subset (⋃₀ β) := 
begin
  apply subset_antisymmetric,
  split,
  apply bounded_union_in_bound,
  intros U hU,
  cases hU with V hV,
  cases hV with hVinβ hVincU,
  rw ← hVincU,
  apply include_set_prevs_subset,
  apply union_upper_bound,
  exact hVinβ,
  intros x hx,
  cases hx with t ht,
  cases ht with ht tvalx,
  cases ht with s hs,
  cases hs with hsinβ htins,
  existsi include_subset s,
  split,
  existsi s,
  exact ⟨hsinβ,rfl⟩,
  existsi t,
  exact ⟨htins, tvalx⟩,
end

lemma include_set_prevs_pair_intersection {X : Type u} {S : set X} (A : set (subtype S)) (B : set (subtype S)) 
  : include_subset (A ∩ B) = (include_subset A) ∩ (include_subset B) :=
begin
  apply subset_antisymmetric,
  split,
  intros x hx,
  cases hx with xg hxg,
  cases hxg with hxginint hxgisx,
  cases hxginint with hxginA hxginB,
  split,
  existsi xg,
  exact ⟨hxginA,hxgisx⟩,
  existsi xg,
  exact ⟨hxginB,hxgisx⟩,
  intros x hx,
  cases hx with hxinAinc hxinBinc,
  cases hxinAinc with xg1 hxg1,
  cases hxinBinc with xg2 hxg2,
  cases hxg1 with hxg1inA xg1val,
  cases hxg2 with hxg2inB xg2val,
  have hrw : xg1 = xg2,
    apply val_injective,
    rw [xg1val,xg2val],
  existsi xg1,
  split,
  split,
  exact hxg1inA,
  rw ← hrw at hxg2inB,
  exact hxg2inB,
  exact xg1val,
end

end set