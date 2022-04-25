universes uₜ u 

inductive index : ℕ → Type u 
| zero : Π {n : ℕ}, index n.succ 
| succ : Π {n : ℕ}, index n → index n.succ

def to_index  : Π {n m : ℕ}, n < m → index m 
| 0 (nat.succ m) h             := index.zero
| (nat.succ n) (nat.succ m) h  := index.succ (to_index (nat.lt_of_succ_lt_succ h))
| 0 0 h := 
  begin
    apply false.elim,
    cases h,
  end
| (nat.succ n) 0 h :=
  begin
    apply false.elim,
    cases h,
  end

inductive vec (T : Type u) : ℕ → Type u 
| nil  : vec 0 
| cons : ∀ {n : ℕ}, T → vec n → vec n.succ

infixr ` :: `:67 := vec.cons
notation `[` l:(foldr `, ` (h t, vec.cons h t) vec.nil `]`) := l

def access {T : Type u} : ∀ {n : ℕ},  vec T n → index n → T 
| (nat.succ n)  (vec.cons t ts) index.zero     := t 
| (nat.succ n)  (vec.cons t ts) (index.succ i) := access ts i

structure matrix (T : Type uₜ) (n m : ℕ) :=
  (entry : (index.{u} n) → (index.{u} m) → T)

def double_vec_to_matrix {T : Type u} {n m : ℕ} : vec (vec T m) n → matrix T n m 
  := λ vec : vec (vec T m) n, {entry := λ i₁ i₂, access (access vec i₁) i₂}

def list_to_vec {T : Type u} : Π l : list T, vec T (list.length l)
| list.nil         := vec.nil 
| (list.cons t ts) := vec.cons t (list_to_vec ts) 

def nat_to_index : Π {n : ℕ} , ℕ → index n.succ := 
  λ n m : ℕ , to_index (nat.mod_lt m (nat.zero_lt_succ n)) 

def index_to_nat : Π {n : ℕ}, index n → ℕ 
| (nat.succ n) index.zero     := 0
| (nat.succ n) (index.succ i) := (index_to_nat i).succ


instance index_has_zero (n : ℕ) : has_zero (index (n.succ)) := ⟨index.zero⟩
instance index_has_add (n : ℕ)  : has_add (index (n.succ)) 
  := ⟨λ i₁ i₂, nat_to_index (index_to_nat i₁ + index_to_nat i₂)⟩  