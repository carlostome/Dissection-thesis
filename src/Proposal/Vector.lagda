\begin{code}
module Proposal.Vector where
  open import Data.Sum
  open import Data.Product
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Maybe
  open import Induction.WellFounded

  -- type of vectors of length n
  data Vec (A : Set) : ℕ → Set where
    []   : Vec A 0
    _::_  : ∀ {n} → A → Vec A n → Vec A (1 + n)

  -- type of vectors of at most length (1 + n)
  data FVec (A : Set) : ℕ → Set where
    fvzero : ∀ {n} →                FVec A (1 + n)
    fvsucc : ∀ {n} → A → FVec A n → FVec A (1 + n)

  -- given an FVec A n we can calculate how far is from 0
  diffFℕ : ∀ {A : Set} {n} → FVec A n → ℕ
  diffFℕ {n = zero} ()
  diffFℕ {n = suc n} (fvzero)     = n
  diffFℕ {n = suc n} (fvsucc _ x) = diffFℕ x


  -- a decomposition is a FVec A (1 + n) plus the rest of elements
  Decomposition : Set → ℕ → Set
  Decomposition A n = Σ (FVec A (1 + n)) λ fv → Vec A (diffFℕ fv)

  -- some examples of decompositions of vectors of length 3

  -- ([ 1 , 2 , 3 ] + [])₃                   = [ 1 , 2 , 3  ]₃
  -- fvsucc 1 (fvsucc 2 (fvsucc 3 fvzero)) + []

  -- ([ 1 , 2 ] + [ 3 ])₃                    = [ 1 , 2 , 3  ]₃
  -- fvsucc 1 (fvsucc 2 fvzero)) + 3 :: []

  -- ([ 1 ] + [ 2 , 3 ])₃                    = [ 1 , 2 , 3  ]₃
  -- fvsucc 1 fvzero + 2 :: 3 :: []

  -- ([ ] + [ 2 , 3 ])₃                      = [ 1 , 2 , 3  ]₃
  -- fvzero + 1 :: 2 :: 3 :: []

  plug' : ∀ {n} {A : Set} → (fv : FVec A (1 + n)) → Vec A (diffFℕ fv) → Vec A n
  plug' {zero} fvzero  v         = v
  plug' {zero} (fvsucc x ()) v
  plug' {suc n} fvzero  v        = v
  plug' {suc n} (fvsucc x fv)  v = x :: plug' fv v

  -- we can plug "back" a decomposition to make a full vector again
  plug : ∀ {n} {A : Set} → Decomposition A n → Vec A n
  plug (fv , v) = plug' fv v

  -- we can lift a FVec appending one more A
  lift : ∀ {n} {A : Set} → A → FVec A n → FVec A (1 + n)
  lift a fvzero        = fvsucc a fvzero
  lift a (fvsucc x fv) = fvsucc x (lift a fv)

  -- we can reverse an FVec
  revFV : ∀ {A : Set} {n} → FVec A n → FVec A n
  revFV fvzero = fvzero
  revFV (fvsucc x xs) = lift x (revFV xs)
\end{code}
