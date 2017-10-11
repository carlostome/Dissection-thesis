\begin{code}
module Proposal.Bove-Capretta.QuickSort where

  open import Data.List hiding (filter; length)
  open import Data.Nat  hiding (_<_)
  open import Data.Bool
  open import Function

  open import Proposal.WellFounded.WellFounded

  data _<ℕ_ (n : ℕ) : ℕ → Set where
    Base : n <ℕ suc n
    Step : ∀ {m : ℕ} → n <ℕ m → n <ℕ suc m

  <ℕ-WellFounded : WF.WellFounded _<ℕ_
  <ℕ-WellFounded x = WF.acc (aux x)
    where
      aux : ∀ x y → y <ℕ x → WF.Acc _<ℕ_ y
      aux .(suc y) y Base     = <ℕ-WellFounded y
      aux .(suc _) y (Step p) = aux _ y p

  _<ℕ-Bool_ : ℕ → ℕ → Bool
  x <ℕ-Bool zero      = false
  zero <ℕ-Bool suc y  = true
  suc x <ℕ-Bool suc y = x <ℕ-Bool y

  filter : (ℕ → Bool) → List ℕ → List ℕ
  filter p [] = []
  filter p (x ∷ xs) with p x
  filter p (x ∷ xs) | false = filter p xs
  filter p (x ∷ xs) | true  = x ∷ filter p xs

  length : List ℕ → ℕ
  length [] = zero
  length (x ∷ xs) = suc (length xs)

  data qsAcc : List ℕ → Set where
    qsNil  : qsAcc []
    qsCons : ∀ x xs → qsAcc (filter (_<ℕ-Bool x) xs) → qsAcc (filter (not ∘ _<ℕ-Bool x) xs) → qsAcc (x ∷ xs)

  quickSort-BC : (inp : List ℕ) → qsAcc inp → List ℕ
  quickSort-BC .[] qsNil = []
  quickSort-BC .(x ∷ xs) (qsCons x xs smaller bigger) =
    quickSort-BC ( (filter (_<ℕ-Bool x) xs)) smaller ++ [ x ] ++ quickSort-BC (filter (not ∘ (_<ℕ-Bool x)) xs) bigger

  module <-on-length-well-founded where
    open Inverse-image-Well-founded { List ℕ } _<ℕ_ length public

    wf : WF.WellFounded _⊰_
    wf = ii-wf <ℕ-WellFounded

  s<ℕs : ∀ {a b} → a <ℕ b → suc a <ℕ suc b
  s<ℕs Base     = Base
  s<ℕs (Step n) = Step (s<ℕs n)

  module FilterLemma where
    _≼_ : Rel (List ℕ)
    x ≼ y = length x <ℕ suc (length y)

    filter-size : (p : ℕ → Bool) → (xs : List ℕ) → filter p xs ≼ xs
    filter-size p [] = Base
    filter-size p (x ∷ xs) with p x
    filter-size p (x ∷ xs) | false = Step (filter-size p xs)
    filter-size p (x ∷ xs) | true  = s<ℕs (filter-size p xs)

  open <-on-length-well-founded
  open FilterLemma

  DomQuickSort : ∀ (xs : List ℕ) → WF.Acc _⊰_ xs → qsAcc xs
  DomQuickSort [] _                = qsNil
  DomQuickSort (x ∷ xs) (WF.acc p) =
    qsCons x xs (DomQuickSort (filter (_<ℕ-Bool x) xs) (p (filter (λ z → z <ℕ-Bool x) xs) (filter-size (_<ℕ-Bool x) xs)))
                (DomQuickSort (filter (not ∘ (_<ℕ-Bool x)) xs) (p (filter (not ∘ (_<ℕ-Bool x)) xs) (filter-size (not ∘ (_<ℕ-Bool x)) xs)))

  quickSort : List ℕ → List ℕ
  quickSort xs = quickSort-BC xs (DomQuickSort xs (wf xs))
\end{code}
