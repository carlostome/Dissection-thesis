\begin{code}
module Proposal.WellFounded.Nat where

  open import Data.Nat
  open import Proposal.WellFounded.WellFounded

  data _<ℕ_ (m : ℕ) : ℕ → Set where
    Base :                    m <ℕ suc m
    Step : {n : ℕ} → m <ℕ n → m <ℕ suc n

  <ℕ-WF : WF.WellFounded _<ℕ_
  <ℕ-WF x = WF.acc (aux x)
    where
      aux : ∀ x y → y <ℕ x → WF.Acc _<ℕ_ y
      aux .(suc y) y Base     = <ℕ-WF y
      aux .(suc _) y (Step p) = aux _ y p

  -- module Version-2 where

  --   data _<ℕ_ : ℕ → ℕ → Set where
  --     Base : ∀ {n}            → zero  <ℕ suc n
  --     Step : ∀ {n m} → n <ℕ m → suc n <ℕ suc m

  --   <ℕ-WF : WF.Well-founded _<ℕ_
  --   <ℕ-WF x = WF.acc (aux x)
  --     where
  --       aux : ∀ x y → y <ℕ x → WF.Acc _<ℕ_ y
  --       aux .(suc _) .0 Base           = WF.acc λ {y ()}
  --       aux .(suc m) .(suc n) (Step {n} {m} p) with aux _ _ p | <ℕ-WF m
  --       ... | WF.acc wf | WF.acc wfm = {!!}
