\begin{code}
module Proposal.WellFounded.Fin where

  open import Data.Nat
  open import Proposal.WellFounded.WellFounded
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

  accesible : ∀ {n} (f : Fin n) → WF.Acc [ n ]_<Fin_ f
                                → (∀ y → [ suc n ] y <Fin (fsucc f) → WF.Acc [ suc n ]_<Fin_ y)
  accesible f x .fzero Base                    = WF.acc λ {_ ()}
  accesible f (WF.acc acc) .(fsucc _) (Step p) = WF.acc (accesible _ (acc _ p))

  <Fin-WF : ∀ n → WF.WellFounded [ n ]_<Fin_
  <Fin-WF n x = WF.acc (aux n x)
    where
      aux : ∀ (n : ℕ) → (x y : Fin n) → [ n ] y <Fin x → WF.Acc ([_]_<Fin_ n) y
      aux .(suc _) .(fsucc _) .fzero Base                                       = WF.acc λ { y ()}
      aux .(suc n) .(fsucc fm) .(fsucc fn) (Step {n = n} {fn = fn} {fm = fm} p) = WF.acc (accesible fn (<Fin-WF n fn))

  diff : ∀ (n : ℕ) → (fn : Fin n) → ℕ
  diff zero ()
  diff (suc n) fzero      = n
  diff (suc n) (fsucc fn) = diff n fn

  module WFFin2 ( n : ℕ ) where
    open Inverse-image-Well-founded {Fin n} (_<ℕ2_) (diff n) public renaming (_⊰_ to _⊰_; ii-wf to ii-wfFin2)

    <Fin2-WF : WF.WellFounded _⊰_
    <Fin2-WF = ii-wfFin2 <ℕ2-WF

  [_]_<Fin2_ : (n : ℕ) → Fin n → Fin n → Set
  [ n ] fn <Fin2 fm = WFFin2._⊰_ n fn fm

  <Fin2-WF : ∀ n → WF.WellFounded [ n ]_<Fin2_
  <Fin2-WF n x = WFFin2.<Fin2-WF n x

  incr : ∀ {n} → Fin n → Fin (1 + n)
  incr fzero     = fsucc fzero
  incr (fsucc x) = fsucc (incr x)

  decr : ∀ {n} → Fin n → Maybe (Fin n)
  decr {zero} ()
  decr {suc zero} fzero        = nothing
  decr {suc zero} (fsucc ())
  decr {suc (suc n)} fzero     = just (fsucc fzero)
  decr {suc (suc n)} (fsucc x) with decr x
  decr {suc (suc n)} (fsucc x) | just y = just (fsucc y)
  decr {suc (suc n)} (fsucc x) | nothing = nothing


  lift : ∀ {n} → Fin n → Fin (1 + n)
  lift fzero     = fzero
  lift (fsucc x) = fsucc (lift x)
  -- data [_]_<Fin3_ : (n : ℕ) → Fin n → Fin n → Set where
  --   Base : ∀ {n} {fn}                        → [ suc n ] fsucc fn <Fin3 fzero
  --   Step : ∀ {n} {fn fm} → [ n ] fn <Fin3 fm → [ suc n ] fsucc fn <Fin3 fsucc fm

  -- <Fin3-WF : ∀ n → WF.WellFounded [ n ]_<Fin3_
  -- <Fin3-WF n x = WF.acc (aux n x)
  --   where
  --     aux : (n : ℕ) (x y : Fin n) → [ n ] y <Fin3 x → WF.Acc ([_]_<Fin3_ n) y
  --     aux .(suc _) fzero .(fsucc _) Base          = {!!}
  --     aux .(suc _) (fsucc x) .(fsucc _) (Step x₂) = {!!}

\end{code}
