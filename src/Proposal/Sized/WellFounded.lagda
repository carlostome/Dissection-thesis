\begin{code}
module Proposal.Sized.WellFounded where

  open import Size

  module WF {A : Set} (_<_ : A → A → Set) where

    data Acc (x : A) : {_ : Size} → Set where
      acc : ∀ {i} → (∀ y → y < x → Acc y {i}) → Acc x {↑ i}

    WellFounded : Set
    WellFounded = ∀ x → Acc x

    wfr : ∀ (P : A → Set) (a : A) → Acc a → (∀ x → (∀ y → y < x → P y) → P x) → P a
    wfr P a (acc x) e = e a λ y p → wfr P y (x y p) e

\end{code}
