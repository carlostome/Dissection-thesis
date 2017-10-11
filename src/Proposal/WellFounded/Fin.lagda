\begin{code}
module Proposal.WellFounded.Fin where

  open import Data.Nat
  open import Proposal.WellFounded.Indexed

  data Fin : ℕ → Set where
    fzero : ∀ {n : ℕ} → Fin (suc n)
    fsucc : ∀ {n : ℕ} → Fin n → Fin (suc n)

  data [_]_<Fin_ (n : ℕ) (fm : Fin (suc n)) : Fin n → Set where

    -- Base : ∀ {n : ℕ} {fm : Fin n}    → [ n ] fm <Fin fsucc fm
    -- Step : ∀ {n : ℕ} {fn fm : Fin n} → [ n ] fn <Fin fm → [ suc n ] fsucc fm <Fin fsucc fm

  -- <Fin-wf : WFIx.Well-founded-Ix [_]_<Fin_
  -- <Fin-wf zero ()
  -- <Fin-wf (suc n) x = WFIx.accIx (aux x)
  --   where
  --     aux : ∀ x y -> [ suc n ] y <Fin x -> WFIx.AccIx [_]_<Fin_ (suc n) y
  --     aux = {!!}
  --     -- aux zero () y
  --     -- aux (suc i) fzero y ()
  --     -- aux (suc i) (fsucc x) .fzero Base         = {!!}

  --     -- aux (suc i) (fsucc x) .(fsucc _) (Step p) = {!!}
  -- -- aux .(Succ y) y Base = <-wf y
  -- -- aux _ y (Step p)     = aux _ _ pTerminating General RecursionTerminating General RecursionTerminating General Recursion

  -- example₁ : [ 10 ] fzero <Fin fsucc fzero
  -- example₁ = {!!}


\end{code}
