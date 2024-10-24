module Data.Sum.Extra where

  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Function using (_∋_)

  ⊎-injective₁ : ∀ {A B : Set} {x y : A} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  ⊎-injective₁ refl = refl

  ⊎-injective₂ : ∀ {A B : Set} {x y : B} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  ⊎-injective₂ refl = refl
