\begin{code}
module Proposal.WellFounded.Fin where

  open import Data.Nat
  open import Induction.WellFounded
  open import Proposal.WellFounded.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Empty
  open import Data.Unit
  open import Data.Maybe

  data Fin : ℕ → Set where
    fzero : ∀ {n : ℕ} → Fin (suc n)
    fsucc : ∀ {n : ℕ} → Fin n → Fin (suc n)

  data [_]_<Fin_ : (n : ℕ) → Fin n → Fin n → Set where
    Base : ∀ {n : ℕ} {fm : Fin n}    →                    [ suc n ] fzero    <Fin fsucc fm
    Step : ∀ {n : ℕ} {fn fm : Fin n} → [ n ] fn <Fin fm → [ suc n ] fsucc fn <Fin fsucc fm

  accesible : ∀ {n} (f : Fin n) → Acc [ n ]_<Fin_ f
                                → (∀ y → [ suc n ] y <Fin (fsucc f) → Acc [ suc n ]_<Fin_ y)
  accesible f x .fzero Base                    = acc λ {_ ()}
  accesible f (acc ac) .(fsucc _) (Step p) = acc (accesible _ (ac _ p))

  <Fin-WF : ∀ n → Well-founded [ n ]_<Fin_
  <Fin-WF n x = acc (aux n x)
    where
      aux : ∀ (n : ℕ) → (x y : Fin n) → [ n ] y <Fin x → Acc ([_]_<Fin_ n) y
      aux .(suc _) .(fsucc _) .fzero Base                                       = acc λ { y ()}
      aux .(suc n) .(fsucc fm) .(fsucc fn) (Step {n = n} {fn = fn} {fm = fm} p) = acc (accesible fn (<Fin-WF n fn))

\end{code}
