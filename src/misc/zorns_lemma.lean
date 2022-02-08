import misc.set

universes u

open set
open subtype
open classical

/-
  These are the definations assocated with zorns lemma that I want the rest of 
  the project to see.
-/

@[reducible]
def is_chain {P : Type u} [partial_order P] (A : set P) : Prop 
  := ∀ a b : P , a ∈ A ∧ b ∈ A → a ≤ b ∨ b ≤ a

theorem every_pair_is_bounded_in_chain {P : Type u} [partial_order P] {A : set P} (hA : is_chain A) 
  : ∀ {a b}, a ∈ A ∧ b ∈ A → ∃ c, c ∈ A ∧ (a ≤ c ∧ b ≤ c) :=
begin
  intros a b hab,
  cases (hA a b hab),
  existsi b,
  exact ⟨and.right hab,h,le_refl b⟩,
  existsi a,
  exact ⟨and.left hab,le_refl a,h⟩,
end 

@[reducible]
def maximal_element {P : Type u} [partial_order P] (m : P) : Prop := ∀ a : P, m ≤ a → a = m

@[reducible]
def bounds_subset {P : Type u} [partial_order P] (A : set P) (m : P) : Prop 
  := ∀ a : P, a ∈ A → a ≤ m

@[reducible]
def all_chains_bounded (P : Type u) [partial_order P] : Prop := ∀ A : set P, is_chain A → ∃ ma : P , bounds_subset A ma

@[reducible]
def strict_upper_bounds {P : Type u} [partial_order P] (C: set P) : set P := λ p : P, p ∉ C ∧ (∀ c : P, c ∈ C → c ≤ p)

@[reducible]
def has_min {P : Type u} [partial_order P] (S : set P) : Prop := ∃ l : P, l ∈ S ∧ ∀ a : P, a ∈ S → l ≤ a 

@[reducible]
def is_min {P : Type u} [partial_order P] (S : set P) (l : P) : Prop := l ∈ S ∧ ∀ a : P, a ∈ S → l ≤ a 

/- You could make this defintion more constructive by making well ordered sets a data structure, consisting of :
  a subset S of P,
  a proof S is a chain,
  a function min : noempty subsets of S → P
  a proof that min sends S' to the minimum element of S'.
-/

@[reducible]
def well_ordered {P : Type u} [partial_order P] (S : set P) : Prop := is_chain S ∧ ∀ S' : set P, S' ⊆ S → S' ≠ ∅ → has_min S'

@[reducible]
def initial_segment {P : Type u} [partial_order P] (S : set P) (a : P) : set P := λ x, x ∈ S ∧ x ≠ a ∧ x ≤ a

/-
  Some helpful results about well ordered sets.
-/

noncomputable def min {P : Type u} [partial_order P] {S : set P} (hwo : well_ordered S) (S' : set P) 
  (hS' : S' ⊆ S) (nS' : S' ≠ ∅) : P := some ((and.right hwo) S' hS' nS') 

theorem min_property {P : Type u} [partial_order P] {S : set P} (hwo : well_ordered S) {S' : set P} (hS' : S' ⊆ S) (nS' : S' ≠ ∅)
  : (min hwo S' hS' nS') ∈ S' ∧ ∀ a : P, a ∈ S' → (min hwo S' hS' nS') ≤ a := some_spec ((and.right hwo) S' hS' nS')

theorem min_unquie {P : Type u} [partial_order P] {S : set P} (hwo : well_ordered S) (S' : set P) (hS' : S' ⊆ S) (nS' : S' ≠ ∅) 
  : ∀ l : P, (l ∈ S' ∧ ∀ a : P, a ∈ S' → l ≤ a) → l = min hwo S' hS' nS' :=
begin
  intros l hl,
  apply le_antisymm,
  apply and.right hl,
  exact and.left (min_property hwo hS' nS'),
  apply and.right (min_property hwo hS' nS'),
  exact and.left hl,
end

theorem min_of_complement {P: Type u} [partial_order P] {A : set P} {B : set P} {x : P} (hx : x ∈ A \ B ∧ ∀ a, a ∈ A \ B → x ≤ a)
  : ∀ {a}, a ∈ A → a ≠ x → a ≤ x → a ∈ B := 
begin
  intros a hainA nax halessx,
  by_contradiction,
  apply nax,
  apply le_antisymm,
  exact halessx,
  apply and.right hx,
  split,
  exact hainA,
  exact h,
end

theorem min_of_subset_greater {P: Type u} [partial_order P] {A B: set P} {mA mB : P} (hAB : B ⊆ A) (hmB : is_min B mB) (hmA : is_min A mA) : mA ≤ mB :=
begin
  apply and.right hmA,
  apply hAB,
  exact and.left hmB,
end

lemma subset_of_chain_is_chain {P :Type u} [partial_order P] {S : set P} (hS : is_chain S) {S' : set P} (hS' : S' ⊆ S) : is_chain S' :=
begin
  intros a b hab,
  have h : a ∈ S ∧ b ∈ S,
  split,
  exact hS' (and.left hab),
  exact hS' (and.right hab),
  apply hS,
  exact h,
end

lemma negation_of_le {P :Type u} [partial_order P] {S : set P} (hS : is_chain S) {a b : P} (hab : a ∈ S ∧ b ∈ S)  : ¬ (a ≤ b) → b ≤ a ∧ a ≠ b :=
begin
  intro h1,
  cases (hS a b hab),
  apply false.elim,
  apply h1,
  exact h,
  split,
  exact h,
  intro ab,
  rw ab at h1,
  apply h1,
  apply le_refl,
end

lemma subset_of_well_ordered_well_ordered {P :Type u} [partial_order P] {S : set P} (hS : well_ordered S) {S' : set P} (hS' : S' ⊆ S) : well_ordered S' :=
begin
  split,
  exact subset_of_chain_is_chain (and.left hS) hS',
  intros U hUinS' nU,
  have hUinS : U ⊆ S,
  apply subset_transitive,
  exact hUinS',
  exact hS',
  apply (and.right hS),
  exact hUinS,
  exact nU,
end

/-
  Some helpful results about initial segments.
-/

theorem initial_segment_chain {P : Type u} [partial_order P] {S : set P} {a : P} (hwo : well_ordered S): is_chain (initial_segment S a) :=
begin
  intros p q hpq,
  cases hpq with hp hq,
  cases hp with pinS,
  cases hq with qinS,
  cases hwo with h,
  exact h p q ⟨pinS,qinS⟩,
end

theorem initial_segment_subset {P : Type u} [partial_order P] (S : set P) (a : P) : initial_segment S a ⊆ S :=
begin
  intros x hx,
  cases hx,
  exact hx_left,
end

theorem initial_segment_preserves_order {P : Type u} [partial_order P] (S : set P) {a b : P} (halessb : a ≤ b) : initial_segment S a ⊆ initial_segment S b :=
begin
  intros x hx,
  cases hx,
  split,
  exact hx_left,
  split,
  intro h,
  rw h at hx_right,
  cases hx_right with h1 h2,
  apply h1,
  apply le_antisymm,
  exact h2,
  exact halessb,
  apply le_trans,
  exact and.right hx_right,
  exact halessb, 
end

lemma not_maximal_element_strictly_greater {P :Type u} [partial_order P] : ∀ p : P, ¬ maximal_element p → ∃ m : P, p ≤ m ∧ p ≠ m := 
begin
  intros p hp,
  by_contradiction h1,
  suffices hrd : maximal_element p,
  exact hp hrd,
  intros q hq,
  symmetry,
  by_contradiction h2,
  apply h1,
  existsi q,
  exact ⟨hq,h2⟩,
end

private lemma all_chains_bounded_implies_SUBs_non_empty_when_no_me {P : Type u} [partial_order P] 
  (hcb : all_chains_bounded P) (hno_me : ∀ p : P, ¬ (maximal_element p))
  : ∀ C : set P, is_chain C → ∃ p : P, p ∈ strict_upper_bounds C :=
begin
  intros C hC,
  let h_C_bounded := hcb C hC,
  let y := some h_C_bounded,
  let hy : bounds_subset C y := some_spec h_C_bounded,
  cases em (y ∈ C),
  let hy_not_me := hno_me y,
  let m := some (not_maximal_element_strictly_greater y hy_not_me),
  let hm : y ≤ m ∧ y ≠ m := some_spec (not_maximal_element_strictly_greater y hy_not_me),
  have hmninC : m ∉ C,
  intro hcon,
  apply and.right hm,
  apply le_antisymm,
  exact and.left hm,
  exact hy m hcon,
  existsi m,
  split,
  exact hmninC,
  intros c hc,
  let hcley : c ≤ y := hy c hc,
  apply le_trans hcley,
  exact and.left hm,
  existsi y,
  split,
  exact h,
  exact hy,
end

/-
  The following stuff is useing the conforming_set
-/

@[reducible]
private def conforming_set {P: Type u} [partial_order P] (hcb : all_chains_bounded P) (hno_me : ∀ p : P, ¬ (maximal_element p)) 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  (hf : choice_function f) (A : set P) := ∃ hA : well_ordered A, ∀ {a : P}, a ∈ A → a = f ⟨strict_upper_bounds (initial_segment A a), all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me (initial_segment A a) (initial_segment_chain  hA)⟩

private lemma conforming_set_well_ordered {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} : conforming_set hcb hno_me hf A → well_ordered A := λ h, some h

private lemma conforming_set_chain {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} : conforming_set hcb hno_me hf A → is_chain A := λ h, and.left (conforming_set_well_ordered h)

@[reducible]
private def conforming_set_extension {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) : set P := λ a : P, a ∈ A 
  ∨ a = f ⟨strict_upper_bounds A, all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me A  (and.left (some hA))⟩

private lemma conforming_set_extension_well_ordered {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) : well_ordered (conforming_set_extension hA) :=
begin
  let hdata := hf ⟨strict_upper_bounds A,_⟩,
  let hAwo := some hA,
  split,
  intros a b hab,
  cases hab with ha hb,
  cases ha,
  cases hb,
  exact (and.left hAwo) a b ⟨ha,hb⟩,
  rw ← hb at hdata,
  cases hdata with hbnotinA hbboundsA,
  left,
  exact hbboundsA a ha,
  cases hb,
  rw ← ha at hdata,
  cases hdata with hanotinA haboundsA,
  right,
  exact haboundsA b hb,
  left, 
  rw ha,
  rw hb,
  intros S hS nS,
  cases em (A ∩ S = ∅) with hinter,
  existsi f ⟨strict_upper_bounds A, _⟩,
  split,
  by_contradiction,
  have ab : S = ∅,
    apply subset_antisymmetric,
    split,
    intros x hx,
    cases hS hx with hx1,
    let hcontra : x ∈ A ∩ S := ⟨hx1,hx⟩, 
    rw hinter at hcontra,
    exact hcontra,
    rw h_1 at hx,
    exact false.elim (h hx),
    exact empty_set_subset,
  exact nS ab,
  intros a ha,
  cases hS ha,
  let h₁ : a ∈ A ∩ S := ⟨h,ha⟩,
  rw hinter at h₁,
  exact false.elim h₁,
  rw h,
  existsi min hAwo (A ∩ S) intersection_in_set  h,
  split,
  exact and.right (and.left (min_property hAwo intersection_in_set h)),
  intros a ha,
  cases em (a ∈ A),
  apply and.right (min_property hAwo intersection_in_set h),
  exact ⟨h_1,ha⟩,
  cases hS ha with h_3,
  exact false.elim (h_1 h_3),
  rw h_2,
  cases hf ⟨strict_upper_bounds A,_⟩ with notinA boundsA,
  apply boundsA,
  apply @intersection_in_set P A S,
  exact and.left (min_property hAwo intersection_in_set h),
end

private lemma conforming_set_extension_initial_segments_by_elms_in_set {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) : ∀ {a}, a ∈ A → initial_segment (conforming_set_extension hA) a = initial_segment A a := 
begin
  intros a hainA,
  apply subset_antisymmetric,
  split,
  intros b hb,
  cases hb with hbinex h,
  cases h with nba hblessa,
  cases hbinex,
  exact ⟨hbinex,⟨nba,hblessa⟩⟩,
  apply false.elim,
  apply nba,
  apply le_antisymm,
  exact hblessa,
  cases hf ⟨strict_upper_bounds A,_⟩,
  rw ← hbinex at right,
  apply right,
  exact hainA,
  intros b hb,
  split,
  left,
  exact and.left hb,
  cases hb,
  exact hb_right,
end

private lemma initial_segment_by_extension {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) : initial_segment (conforming_set_extension hA) (f ⟨strict_upper_bounds A, all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me A  (and.left (some hA))⟩) = A :=
begin
  apply subset_antisymmetric,
  split,
  intros h hb,
  cases hb with hbinex hb,
  cases hb with nb hless,
  cases hbinex,
  exact hbinex,
  apply false.elim,
  apply nb,
  exact hbinex,
  intros b hb,
  split,
  left,
  exact hb,
  cases hf ⟨strict_upper_bounds A,_⟩,
  split,
  intros ab,
  rw ← ab at left,
  apply left,
  exact hb,
  apply right b,
  exact hb,
end

private lemma conforming_set_extension_initial_segments_by_extension {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) : initial_segment (conforming_set_extension hA) (f ⟨strict_upper_bounds A, all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me A  (and.left (some hA))⟩) = A :=
begin
  apply subset_antisymmetric,
  split,
  intros a ha,
  cases ha with hainex ha,
  cases ha with na haless,
  cases hainex,
  exact hainex,
  cases hf ⟨strict_upper_bounds A,_⟩,
  apply false.elim,
  apply na,
  exact hainex,
  apply all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me,
  apply conforming_set_chain,
  exact hA,
  intros a ha,
  split,
  left,
  exact ha,
  cases hf ⟨strict_upper_bounds A,_⟩,
  split,
  intro ab,
  rw ab at ha,
  apply left,
  exact ha,
  apply right,
  exact ha,
end

/-
  Most of this lemma is fighting the type checker to acknowledge that the previous 3 lemmas
  give the result.
-/ 

private lemma conforming_set_extension_conforming_set {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) : conforming_set hcb hno_me hf (conforming_set_extension hA) :=
begin
  split,
  intros a ha,
  have n₁ : ∃ b, b ∈ strict_upper_bounds (initial_segment (conforming_set_extension hA) a),
    apply all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me,
    apply initial_segment_chain,
    apply conforming_set_extension_well_ordered,
  let α₁ : {S : set P //  ∃ x : P, x ∈ S} := ⟨strict_upper_bounds (initial_segment (conforming_set_extension hA) a),n₁⟩,
  have hval1 : α₁.val =  strict_upper_bounds (initial_segment (conforming_set_extension hA) a) := rfl,
  have trv₁ : f ⟨strict_upper_bounds (initial_segment (conforming_set_extension hA) a), _⟩ = f α₁ := rfl,
  have n₂ : ∃ b, b ∈ strict_upper_bounds (initial_segment A a),
    apply all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me,
    apply initial_segment_chain,
    apply conforming_set_well_ordered hA,
  let α₂ : {S : set P //  ∃ x : P, x ∈ S} := ⟨strict_upper_bounds (initial_segment A a), n₂⟩,
  have hval2 : α₂.val = strict_upper_bounds (initial_segment A a) := rfl,
  have trv₂ : f ⟨strict_upper_bounds (initial_segment A a), _⟩ = f α₂ := rfl,
  have n₃ : ∃ b, b ∈ strict_upper_bounds A,
    apply all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me,
    apply conforming_set_chain hA,
  let α₃ : {S : set P //  ∃ x : P, x ∈ S} := ⟨ strict_upper_bounds A,n₃⟩,
  have hval3 : α₃.val = strict_upper_bounds A := rfl,
  have trv₃ : f ⟨strict_upper_bounds A,_⟩ = f α₃ := rfl,
  cases ha,
  have hα1α2 : α₁ = α₂,
    apply val_injective,
    rw [hval1, hval2, conforming_set_extension_initial_segments_by_elms_in_set hA ha],
  rw [trv₁,hα1α2,← trv₂],
  apply some_spec hA,
  exact ha,
  have hα1α3 : α₁ = α₃,
    apply val_injective,
    rw [hval1, hval3, ha, initial_segment_by_extension hA],
  rw [trv₁,hα1α3,← trv₃,ha],
  exact conforming_set_extension_well_ordered hA,
end

private lemma half_csisocs {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) {B : set P}  (hB : conforming_set hcb hno_me hf B) (nAminusB : A \ B ≠ ∅ ) : ∃ a, B = initial_segment A a := 
begin
  let x := min (conforming_set_well_ordered hA) (A \ B) (difference_in_numerator A B) nAminusB,
  have hx : x ∈ A \ B ∧ ∀ a, a ∈ A \ B → x ≤ a := min_property (conforming_set_well_ordered hA) (difference_in_numerator A B) nAminusB,
  existsi x,
  apply subset_antisymmetric,
  rw and_comm,
  split,
  intros a hainIx,
  apply min_of_complement hx,
  exact and.left hainIx,
  exact and.left (and.right hainIx),
  exact and.right(and.right hainIx),
  apply empty_diff_implies_subset,
  by_contradiction,
  let y := min (conforming_set_well_ordered hB) (B \ (initial_segment A x)) (difference_in_numerator B (initial_segment A x)) h,
  have hy : y ∈ B \ (initial_segment A x) ∧ ∀ a, a ∈ B \ (initial_segment A x) → y ≤ a := min_property _ _ _,
  have hIByinIAx : initial_segment B y ⊆ initial_segment A x,
    intros u hu,
    apply min_of_complement hy,
    exact and.left hu,
    exact and.left (and.right hu),
    exact and.right (and.right hu),
  have bound_test : ∀ {u v : P}, u ∈ initial_segment B y → v ∈ A → v ≠ u → v ≤ u → v ∈ initial_segment B y,
    intros u v hu hv nvu hvlessu,
    have hvinB : v ∈ B,
    apply min_of_complement hx,
    exact hv,
    intro ab,
    apply nvu,
    apply le_antisymm,
    exact hvlessu,
    rw ab,
    exact and.right (and.right (hIByinIAx hu)),
    apply le_trans,
    exact hvlessu,
    exact and.right (and.right (hIByinIAx hu)),
    split,
    exact hvinB,
    split,
    intro ab,
    apply nvu,
    apply le_antisymm,
    exact hvlessu,
    rw ab,
    exact and.right (and.right hu),
    apply le_trans,
    exact hvlessu,
    exact and.right (and.right hu),
  have hbz : A \ (initial_segment B y) ≠ ∅,
    have hbzsub : A \ B ⊆ A \ (initial_segment B y),
      apply diff_by_subset_superset,
      apply initial_segment_subset,
      intro ab,
    rw ab at hbzsub,
    exact hbzsub (some_spec (not_empty_set_has_element nAminusB)),
  let z := min (conforming_set_well_ordered hA) (A \ (initial_segment B y)) (difference_in_numerator A (initial_segment B y)) hbz,
  have hz : z ∈ A \ (initial_segment B y) ∧ ∀ a, a ∈ A \ (initial_segment B y) → z ≤ a := min_property _ _ _,
  have hzlessx : z ≤ x,
    apply and.right hz,
    apply diff_by_subset_superset,
    exact hIByinIAx,
    split,
    exact and.left (and.left hx),
    intro ab,
    cases ab,
    exact and.left ab_right rfl,
  have hAxinAz : initial_segment A z ⊆ initial_segment A x,
    apply initial_segment_preserves_order,
    exact hzlessx,
  have hrw : initial_segment B y = initial_segment A z,
    symmetry,
    apply subset_antisymmetric,
    split,
    intros α hα,
    cases hα with hα₁ hα₂,
    cases hα₂ with hα₂ hα₃,
    apply min_of_complement hz,
    exact hα₁,
    exact hα₂,
    exact hα₃,
    intros β hβ,
    cases hβ with hβ₁ hβ₂,
    cases hβ₂ with hβ₂ hβ₃,
    split,
    apply initial_segment_subset,
    apply min_of_complement hy,
    exact hβ₁,
    exact hβ₂,
    exact hβ₃,
    split,
    by_contradiction,
    apply and.right (and.left hz),
    rw ← h,
    exact ⟨hβ₁,⟨hβ₂,hβ₃⟩⟩,
    by_contradiction,
    have h1 : z ≤ β ∧ β ≠ z,
      apply negation_of_le,
      apply conforming_set_chain,
      exact hA,
    split,
    apply initial_segment_subset,
    apply min_of_complement hy,
    exact hβ₁,
    exact hβ₂,
    exact hβ₃,
    exact and.left (and.left hz),
    exact h,
    apply and.right (and.left hz),
    apply bound_test,
    exact ⟨hβ₁,⟨hβ₂,hβ₃⟩⟩,
    exact and.left (and.left hz),
    intro h2,
    rw h2 at h1,
    apply and.right h1,
    refl,
    exact and.left h1,
  have hyisz : y = z,
    let α₁ := subtype.mk (strict_upper_bounds (initial_segment B y)) (all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me (initial_segment B y) (initial_segment_chain  (some hB))),
    let α₂ := subtype.mk (strict_upper_bounds (initial_segment A z)) (all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me (initial_segment A z) (initial_segment_chain  (some hA))),
    let hy1 : y = f α₁ := (some_spec hB) (and.left (and.left hy)),
    let hz1 : z = f α₂ := (some_spec hA) (and.left (and.left hz)),
    have hrw1 : α₁ = α₂,
      apply val_injective,
      have trv₁ : α₁.val = strict_upper_bounds (initial_segment B y) := rfl,
      have trv₂ : α₂.val = strict_upper_bounds (initial_segment A z) := rfl,
      rw hrw at trv₁,
      rw ← trv₁ at trv₂,
      symmetry,
      exact trv₂,
    rw [hrw1,← hz1] at hy1,
    exact hy1,
  apply and.right (and.left hy),
  rw hyisz,
  split,
  exact and.left (and.left hz),
  split,
  intro ab,
  rw ab at hyisz,
  apply and.right (and.left hx),
  rw ← hyisz,
  exact and.left (and.left hy),
  exact hzlessx,  
end

private lemma conforming_sets_overlap_and_is {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {A : set P} (hA : conforming_set hcb hno_me hf A) {B : set P} (hB : conforming_set hcb hno_me hf B) (nAB : A ≠ B) : (∃ a, A = initial_segment B a) ∨ (∃ a, B = initial_segment A a) := 
begin
  cases (not_equal_in_terms_of_comp nAB),
  right,
  apply half_csisocs,
  exact hA,
  exact hB,
  exact h,
  left,
  apply half_csisocs,
  exact hB,
  exact hA,
  exact h,
end

@[reducible]
private def union_of_conforming_sets {P: Type u} [partial_order P] (hcb : all_chains_bounded P) (hno_me : ∀ p : P, ¬ (maximal_element p)) 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  (hf : choice_function f) : set P := λ p : P, ∃ A : set P, p ∈ A ∧ (conforming_set hcb hno_me hf A)

private lemma le_test_for_being_in_conforming_set {P: Type u} [partial_order P] {hcb : all_chains_bounded P} {hno_me : ∀ p : P, ¬ (maximal_element p)} 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P}
  {hf : choice_function f} {C : set P} (hC : conforming_set hcb hno_me hf C) {x : P} {hxinC : x ∈ C} : ∀ {y}, y ∈ union_of_conforming_sets hcb hno_me hf → y ≤ x → y ∈ C :=
begin
  intros y hyinuoc hylessx,
  cases hyinuoc with Cy hCy,
  cases hCy with hyinCy hCy,
  by_cases C = Cy,
  rw ← h at hyinCy,
  exact hyinCy,
  cases (conforming_sets_overlap_and_is hC hCy h) with h1,
  let a := some h1,
  have hCis : C = initial_segment Cy a := some_spec h1,
  rw hCis at hxinC,
  rw hCis,
  cases hxinC,
  cases hxinC_right with hxnota hxlessa,
  split,
  exact hyinCy,
  split,
  intro ab,
  apply hxnota,
  rw ← ab,
  rw ← ab at hxlessa,
  apply le_antisymm,
  exact hxlessa,
  exact hylessx,
  apply le_trans,
  exact hylessx,
  exact hxlessa,
  rw some_spec h_1 at hyinCy,
  exact and.left hyinCy,
end

private lemma union_of_conforming_sets_well_ordered {P: Type u} [po:partial_order P] (hcb : all_chains_bounded P) (hno_me : ∀ p : P, ¬ (maximal_element p)) 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P} (hf : choice_function f) : well_ordered (union_of_conforming_sets hcb hno_me hf) := 
begin
  have uoc_chain : is_chain (union_of_conforming_sets hcb hno_me hf),
    intros a b hab,
    cases hab with ha hb,
    cases ha with Ca hCa,
    cases hCa with hainCa hCa,
    cases hb with Cb hCb,
    cases hCb with hbinCb hCb,
    cases em (Ca = Cb) with h,
    apply and.left (some (hCb)),
    rw h at hainCa,
    exact ⟨hainCa,hbinCb⟩,
    have h1 := conforming_sets_overlap_and_is hCa hCb h,
    cases h1,
    apply and.left (some hCb),
    have h2 := some_spec h1,
    rw h2 at hainCa,
    split,
    apply initial_segment_subset,
    exact hainCa,
    exact hbinCb,
    apply and.left (some hCa),
    have h2 := some_spec h1,
    rw h2 at hbinCb,
    split,
    exact hainCa,
    apply initial_segment_subset,
    exact hbinCb,
  split,
  exact uoc_chain,
  intros S hS nS,
  let x := some (not_empty_set_has_element nS),
  have hx : x ∈ S := some_spec (not_empty_set_has_element nS),
  cases hS hx with Cx hCx,
  cases hCx with hxinCx hCx,
  have nCxS : Cx ∩ S ≠ ∅,
    let h2 : x ∈ Cx ∩ S := ⟨hxinCx, hx⟩,
    intro ab,
    rw ab at h2,
    exact h2,
  existsi (min (conforming_set_well_ordered hCx) (Cx ∩ S) (intersection_in_set) nCxS),
  let min_prop := min_property (conforming_set_well_ordered hCx) (intersection_in_set) nCxS,
  split,
  apply intersection_in_set,
  rw @intersection_commuative P S Cx,
  exact and.left (min_prop),
  intros a hainS,
  have sub : x ≤ a ∨ a ≤ x,
    apply uoc_chain,
    split, 
    apply hS,
    exact hx,
    apply hS,
    exact hainS,
  cases sub,
  apply le_trans,
  apply and.right min_prop,
  exact ⟨hxinCx,hx⟩,
  exact sub,
  have hainCx : a ∈ Cx,
    apply le_test_for_being_in_conforming_set,
    exact hCx,
    exact hxinCx,
    apply hS,
    exact hainS,
    exact sub,
  apply and.right min_prop,
  exact ⟨hainCx,hainS⟩,
end

private lemma union_of_conforming_sets_conforming_sets {P: Type u} [partial_order P] (hcb : all_chains_bounded P) (hno_me : ∀ p : P, ¬ (maximal_element p)) 
  {f : {S : set P //  ∃ p : P, p ∈ S} → P} (hf : choice_function f) : conforming_set hcb hno_me hf (union_of_conforming_sets hcb hno_me hf) := 
begin
  split,
  intros a hainuoc,
  let Ca := some hainuoc,
  have hCa : a ∈ Ca ∧ conforming_set hcb hno_me hf Ca := some_spec hainuoc,
  cases hCa with hainCa hCa,
  have hrw : initial_segment (union_of_conforming_sets hcb hno_me hf) a = initial_segment Ca a,
    apply subset_antisymmetric,
    split,
    intros b hb,
    split,
    apply le_test_for_being_in_conforming_set,
    exact hCa,
    exact hainCa,
    apply initial_segment_subset,
    exact hb,
    exact and.right (and.right hb),
    exact and.right hb,
    intros b hb,
    cases hb with hbinCa hb,
    split,
    existsi Ca,
    exact ⟨hbinCa,hCa⟩,
    exact hb,
  have n₁ : ∃ b, b ∈ strict_upper_bounds (initial_segment (union_of_conforming_sets hcb hno_me hf) a),
    apply all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me,
    apply initial_segment_chain,
    apply union_of_conforming_sets_well_ordered,
  let α₁ : {S : set P //  ∃ x : P, x ∈ S} := ⟨strict_upper_bounds (initial_segment (union_of_conforming_sets hcb hno_me hf) a),n₁⟩,
  have hval1 : α₁.val = strict_upper_bounds (initial_segment (union_of_conforming_sets hcb hno_me hf) a) := rfl,
  have trv₁ : f ⟨strict_upper_bounds (initial_segment (union_of_conforming_sets hcb hno_me hf) a),n₁⟩ = f α₁ := rfl,
  have n₂ : ∃ b, b ∈ strict_upper_bounds (initial_segment Ca a),
    apply all_chains_bounded_implies_SUBs_non_empty_when_no_me hcb hno_me,
    apply initial_segment_chain,
    exact conforming_set_well_ordered hCa,
  let α₂ : {S : set P //  ∃ x : P, x ∈ S} := ⟨strict_upper_bounds (initial_segment Ca a),n₂⟩,
  have hval2 : α₂.val = strict_upper_bounds (initial_segment Ca a) := rfl,
  have trv₂ : f ⟨strict_upper_bounds (initial_segment Ca a),n₂⟩ = f α₂ := rfl,
  have hα₁α₂ : α₁ = α₂,
    apply val_injective,
    rw [hval1,hval2,hrw],
  rw [trv₁,hα₁α₂,← trv₂],
  apply some_spec hCa,
  exact hainCa,
  apply union_of_conforming_sets_well_ordered,
end

theorem zorns_lemma {P : Type u} [po:partial_order P] : all_chains_bounded P → ∃ m : P, maximal_element m :=
begin
  intro hcb,
  by_contradiction raw_hno_me,
  let hno_me := forall_not_of_not_exists raw_hno_me,
  let f := some (@there_is_choice_function P),
  let hf : choice_function f := some_spec there_is_choice_function,
  let uoc : set P := union_of_conforming_sets hcb hno_me hf,
  let huoc : conforming_set hcb hno_me  hf uoc := union_of_conforming_sets_conforming_sets hcb hno_me hf,
  let exuoc : set P := conforming_set_extension huoc,
  let hexuoc : conforming_set hcb hno_me hf exuoc := conforming_set_extension_conforming_set huoc,
  let a := f ⟨strict_upper_bounds uoc,_⟩,
  let ha : a ∈ strict_upper_bounds uoc := hf ⟨strict_upper_bounds uoc,_⟩,
  have hainex : a ∈ exuoc,
    right,
    refl,
  have hainuoc : a ∈ uoc,
    existsi exuoc,
    split,
    exact hainex,
    exact hexuoc,
  exact (and.left ha) hainuoc,
end