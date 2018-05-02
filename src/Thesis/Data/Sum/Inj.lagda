\begin{code}
module Thesis.Data.Sum.Inj where

  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Function using (_∋_)

  data Is-inj₁ {A B : Set} : A ⊎ B → Set where
    is-inj₁ : ∀ {x} → Is-inj₁ (inj₁ x)

  data Is-inj₂ {A B : Set} : A ⊎ B → Set where
    is-inj₂ : ∀ {x} → Is-inj₂ (inj₂ x)

  ⊎-injective₁ : ∀ {A B : Set} {x y : A} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  ⊎-injective₁ refl = refl


  ⊎-injective₂ : ∀ {A B : Set} {x y : B} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  ⊎-injective₂ refl = refl
\end{code}
