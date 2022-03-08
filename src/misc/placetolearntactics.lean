/-
  Currently using this file as a playground to learn about meta programming in 
  LEAN but eventally I will implement a tactic that normalises simple ring expressions.

  Monads in LEAN :

  consider a function summing the 2/5/7 elements of a list, returning the value
  rapped in some if there are enough elements in the list and none otherwise. 
  A naive implementation is the following,

-/

def sum₂₅₇1 (l: list ℕ) : option ℕ :=
match list.nth l 1 with 
| option.none    := option.none 
| option.some n₂ := match list.nth l 4 with 
                    | option.none    := option.none
                    | option.some n₅ := match list.nth l 6 with 
                                        | option.none    := option.none 
                                        | option.some n₇ := option.some (n₂ + n₅ + n₇)
                                        end
                    end
end

/-
  If we had a function that allow us to update the internal value of a option α via
  a fn on the left we could rewrite this in a more imperative manner. 
-/

def connect {α β : Type} : option α → (α → option β) → option β 
| option.none _    := option.none 
| (option.some a) f := f a


def sum₂₅₇2 (l: list ℕ) : option ℕ := connect (list.nth l 1) 
                                      (λ n₂, connect (list.nth l 4) 
                                      (λ n₅, connect (list.nth l 6)
                                      (λ n₇, option.some (n₂ + n₅ +n₇))))

/-
  connect is rewritten as >>= and pronounced "bind". 
  the function n ↦ some n is rewritten as "pure"
-/

def sum₂₅₇3 (l: list ℕ) : option ℕ := 
  (list.nth l 1) >>= (λ n₂, 
  (list.nth l 4) >>= (λ n₅, 
  (list.nth l 6) >>= (λ n₇, 
  pure (n₂ + n₅ + n₇))))

/-
  this looks a lot like the imperative program
  let n₂ = l[1];
  let n₅ = l[4];
  let n₆ = l[5];
  return n₂ + n₅ + n₇

  Functional programming languages the following notation
  do x ← ma, t    is equiv to    ma >>= (λ x, t) 
-/

def sum₂₅₇4 (l: list ℕ) : option ℕ := do n₂ ← list.nth l 1,
                                      (do n₅ ← list.nth l 4,
                                      (do n₇ ← list.nth l 6,
                                          pure (n₂ + n₅ + n₇)))

 
/-
  This look even more like an imperative program.

  we can check that the following laws hold for option:
  (*)
  pure a >>= f = f a
  m >>= pure = m
  (m >>= f) >>= g = m >>= (λ x, (f x) >>= g)

  so do x ← (pure a), pure (f x) = pure a >>= (λ x, pure (f x)) = pure (f a)
  so we can think of the last term as the return value. (m >>= f) >>= g = m >>= (λ x, (f x) >>= g)
  means we don't really care how the do's are bracketed in sum₂₅₇ so we can just drop them. 
-/

def sum₂₅₇5 (l: list ℕ) : option ℕ :=
  do n₂ ← list.nth l 1,
     n₅ ← list.nth l 5,
     n₇ ← list.nth l 7,
     pure (n₂ + n₅ + n₇)


/-
  any fn m : Type u → Type u with similar operations >>= and pure satifying (*)
  is called a monad. Using >>= and pure we can defn m₁ >> m₂ = m₁ >>= (λ a, m₂).
  do s, t is sugar for s >> t. <|> : m a → m a → m a trys the 1st arg then tries the
  2nd.
-/

/-
  The following stuff is from a meta programming paper.

  Framework :

  Add metaconstants -- to the axiomatic foundation are just opaque constants but when the
  bytecode is evaluates them they are assoicted with internally defn gadgets. 

  A example is tactic_state which represents the internal elaborator state i the contex where
  the tatic is invoked. 

  The metaprogramming API provides access to fns that operate on these. 

  the keyword meta gives access to these extensions.

  Using these primatives a tactics monad is defined. This is also an instance of 
  the alternative type class so <|> can be used. 

  (a bit about names that I don't really understand)

  Expressions in LEAN are represented using the following data types. 

  inductive level
  | zero  : level
  | succ  : level → level
  | max   : level → level → level
  | imax  : level → level → level
  | param : name → level
  | mvar  : name → level

  inductive expr
  | var    : nat → expr
  | lconst : name → name → expr
  | mvar   : name → expr → expr
  | sort   : level → expr
  | const  : name → list level → expr
  | app    : expr → expr → expr
  | lam    : name → binfo → expr → expr → expr
  | pi     : name → binfo → expr → expr → expr
  | elet   : name → expr → expr → expr → expr

  the nats are de brujin indies, lconst/mvar should never be in any proof terms.

-/