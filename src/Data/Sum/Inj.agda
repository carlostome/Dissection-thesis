
module Data.Sum.Inj where

  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Function using (_∋_)

  data Is-inj₁ {A B : Set} : A ⊎ B → Set where
    is-inj₁ : ∀ {x} → Is-inj₁ (inj₁ x)

  data Is-inj₂ {A B : Set} : A ⊎ B → Set where
    is-inj₂ : ∀ {x} → Is-inj₂ (inj₂ x)


