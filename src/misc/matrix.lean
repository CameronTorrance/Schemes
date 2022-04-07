universes u 

inductive index : ℕ → Type u 
| zero : Π {n : ℕ}, index n.succ 
| succ : Π {n : ℕ}, index n → index n.succ