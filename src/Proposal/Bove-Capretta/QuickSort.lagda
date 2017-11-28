\begin{code}
module Proposal.Bove-Capretta.QuickSort where

  open import Data.List hiding (filter; length)
  open import Data.Nat  hiding (_<_)
  open import Data.Bool
  open import Function

  open import Induction.WellFounded

  data _<ℕ_ (n : ℕ) : ℕ → Set where
    Base : n <ℕ suc n
    Step : ∀ {m : ℕ} → n <ℕ m → n <ℕ suc m

  <ℕ-WellFounded : Well-founded _<ℕ_
  <ℕ-WellFounded x = acc (aux x)
    where
      aux : ∀ x y → y <ℕ x → Acc _<ℕ_ y
      aux .(suc y) y Base     = <ℕ-WellFounded y
      aux .(suc _) y (Step p) = aux _ y p

  _<ℕ-Bool_ : ℕ → ℕ → Bool
  x <ℕ-Bool zero      = false
  zero <ℕ-Bool suc y  = true
  suc x <ℕ-Bool suc y = x <ℕ-Bool y

  filter : {A : Set} → (A → Bool) → List A → List A
  filter p [] = []
  filter p (x ∷ xs) with p x
  filter p (x ∷ xs) | false = filter p xs
  filter p (x ∷ xs) | true  = x ∷ filter p xs

  length : {A : Set} → List A → ℕ
  length [] = zero
  length (x ∷ xs) = suc (length xs)
\end{code}

%<*DP>
\begin{code}
  data qsAcc {A : Set} (p : A → A → Bool) : List A → Set where
    qsNil  : qsAcc p []
    qsCons : ∀ x xs → qsAcc p (filter (p x) xs)
                    → qsAcc p (filter (not ∘ p x) xs) → qsAcc p (x ∷ xs)
\end{code}
%</DP>


%<*BC>
\begin{code}
  quickSort : ∀ {A} (p : A → A → Bool) → (i : List A) → qsAcc p i → List A
  quickSort p .[] qsNil = []
  quickSort p .(x ∷ xs) (qsCons x xs smaller bigger) =
    quickSort p ((filter (p x) xs)) smaller
    ++ [ x ] ++
    quickSort p (filter (not ∘ (p x)) xs) bigger
\end{code}
%</BC>

\begin{code}
  module <-on-length-well-founded {A : Set} where
    open Inverse-image {A = List A} {B = ℕ} {_<_ = _<ℕ_}  length public

    _⊰_ = _<ℕ_ on (length {A})

    wf : Well-founded (_⊰_)
    wf = well-founded <ℕ-WellFounded

  s<ℕs : ∀ {a b} → a <ℕ b → suc a <ℕ suc b
  s<ℕs Base     = Base
  s<ℕs (Step n) = Step (s<ℕs n)

  module FilterLemma {A : Set} where
    _≼_ :  List A → List A → Set
    x ≼ y = length x <ℕ suc (length y)

    filter-size : (p : A → Bool) → (xs : List A) → filter p xs ≼ xs
    filter-size p [] = Base
    filter-size p (x ∷ xs) with p x
    filter-size p (x ∷ xs) | false = Step (filter-size p xs)
    filter-size p (x ∷ xs) | true  = s<ℕs (filter-size p xs)

  module QuickSort {A : Set} where
    open <-on-length-well-founded
    open FilterLemma

    DomQuickSort : ∀ (p : A → A → Bool) → (xs : List A) → Acc _⊰_ xs → qsAcc p xs
    DomQuickSort p [] _                = qsNil
    DomQuickSort p (x ∷ xs) (acc rs) =
      qsCons x xs (DomQuickSort p (filter (p x) xs) (rs (filter (λ z → p x z) xs) (filter-size (p x) xs)))
                  (DomQuickSort p (filter (not ∘ (p x)) xs) (rs (filter (not ∘ (p x)) xs) (filter-size (not ∘ (p x)) xs)))

    well-f = <-on-length-well-founded.wf

  open QuickSort {ℕ}

  -- quickSort : List ℕ → List ℕ
  -- quickSort xs = quickSort-BC _<ℕ-Bool_ xs (DomQuickSort _<ℕ-Bool_ xs (well-f xs))
\end{code}
