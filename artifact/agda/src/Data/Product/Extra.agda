module Data.Product.Extra where

  open import Data.Product
  open import Relation.Binary.PropositionalEquality

  ×-injective : ∀ {A B : Set} → {x₁ x₂ : A} {y₁ y₂ : B} → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂ × y₁ ≡ y₂
  ×-injective refl = refl , refl
