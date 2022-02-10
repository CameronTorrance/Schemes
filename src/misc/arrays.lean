import algebra.comm_rings.basic

universe u

open comm_ring

inductive finType : ℕ → Type 
| zero : Π {n : ℕ} , finType (nat.succ n)
| succ : Π {n : ℕ} , finType n → finType (nat.succ n)

inductive vec (T : Type u) : ℕ → Type u
| nil  : vec nat.zero
| cons : Π {n : ℕ}, T → vec n → vec (nat.succ n)

infixr ` :: `:67 := vec.cons
notation `[` l:(foldr `, ` (h t, vec.cons h t) vec.nil `]`) := l

namespace finType

def finType_to_nat : Π {n : ℕ} , finType n → ℕ
| (nat.succ n) zero     := 0
| (nat.succ n) (succ m) := nat.succ (finType_to_nat m) 

protected def finType.repr : Π {n : ℕ }, finType n → string
| (nat.succ n) m         := repr (finType_to_nat m)

instance finType_repr {n : ℕ} : has_repr (finType n) :=
⟨finType.repr⟩

instance finType_to_string {n : ℕ}: has_to_string (finType n) :=
⟨finType.repr⟩

--def nat_to_finType : Π {m : ℕ} {n : ℕ} (h : m < (nat.succ n) ), finType (nat.succ n) 
--| nat.zero n _ := zero
--| (nat.succ m) n h := succ (nat_to_finType )

end finType

namespace vec

open finType

def shift {T : Type u} [inhabited T] : Π {n : ℕ}, vec T n → vec T (nat.succ n) 
| 0 []                 := [default]
| (nat.succ n) (a::as) := a :: (shift as) 

def access {T : Type u} : Π {n : ℕ}, finType n → vec T n → T
| (nat.succ n) zero (a::as)     := a
| (nat.succ n) (succ m) (a::as) := access m as

def seq_to_vec {T : Type u} (f : ℕ → T) : Π n : ℕ , vec T n
| 0            := [] 
| (nat.succ n) := (f n) :: (seq_to_vec n)

end vec

def matrix (T : Type u) (n : ℕ) (m : ℕ) := vec (vec T m) n

namespace matrix

def access { T : Type u} : Π (n m : ℕ), finType n → finType m → matrix T n m → T 
  := λ n m i₁ i₂ M, vec.access i₂ (vec.access i₁ M)  


end matrix