\begin{code}
module Proposal.WellFounded.Nat where

  open import Data.Nat
  open import Proposal.WellFounded.WellFounded
  open import Relation.Binary.PropositionalEquality
  open import Data.Sum
  open import Data.Product
  open import Data.Empty

  data _<ℕ_ (m : ℕ) : ℕ → Set where
    Base :                    m <ℕ suc m
    Step : {n : ℕ} → m <ℕ n → m <ℕ suc n

  <ℕ-WF : WF.WellFounded _<ℕ_
  <ℕ-WF x = WF.acc (aux x)
    where
      aux : ∀ x y → y <ℕ x → WF.Acc _<ℕ_ y
      aux .(suc y) y Base     = <ℕ-WF y
      aux .(suc n) y (Step {n} p) = aux n y p

  data _<ℕ2_ : ℕ → ℕ → Set where
    B : ∀ {n : ℕ}   → 0 <ℕ2 suc n
    S : ∀ {n m : ℕ} → n <ℕ2 m      → suc n <ℕ2 suc m

  lemma : ∀ n m → n <ℕ2 suc m → n ≡ m ⊎ n <ℕ2 m
  lemma .0 zero B = inj₁ refl
  lemma .0 (suc m) B = inj₂ B
  lemma .(suc n) zero (S {n} {.0} ())
  lemma .(suc n) (suc m) (S {n} {.(suc m)} x) with lemma _ _ x
  lemma .(suc m) (suc m) (S {.m} {.(suc m)} x) | inj₁ refl = inj₁ refl
  lemma .(suc n) (suc m) (S {n} {.(suc m)} x) | inj₂ y = inj₂ (S y)

  <ℕ2-WF : WF.WellFounded _<ℕ2_
  <ℕ2-WF x = WF.acc (aux x)
    where
      aux : (x y : ℕ) → y <ℕ2 x → WF.Acc _<ℕ2_ y
      aux zero y ()
      aux (suc x) y p with lemma _ _ p
      aux (suc x) .x p | inj₁ refl = <ℕ2-WF x
      aux (suc x) y p  | inj₂ i    = aux x y i

  data _≤ℕ_ : ℕ → ℕ → Set where
    Base : ∀ {n : ℕ}   → 0 ≤ℕ n
    Step : ∀ {n m : ℕ} → n ≤ℕ m → suc n ≤ℕ suc m

  _<ℕ3_ : ℕ → ℕ → Set
  x <ℕ3 y = suc x ≤ℕ y

  -- lemma₁ : ∀ n m → n ≤ℕ m → suc n ≡ m ⊎ suc n <ℕ3 m
  -- lemma₁ .0 zero Base = {!!}
  -- lemma₁ .0 (suc m) Base = {!!}
  -- lemma₁ .(suc _) .(suc _) (Step x) = {!!}

  -- <ℕ3-WF : WF.WellFounded _<ℕ3_
  -- <ℕ3-WF x = WF.acc (aux x)
  --   where
  --     aux : (x y : ℕ) → y <ℕ3 x → WF.Acc _<ℕ3_ y
  --     aux .(suc m) .n (Step {n} {m} x₂) = {!!}
  
