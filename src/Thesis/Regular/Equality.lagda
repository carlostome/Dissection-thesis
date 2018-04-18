\begin{code}
module Thesis.Regular.Equality where

  open import Data.Unit
  open import Data.Product
  open import Data.Sum
  open import Data.Empty
  open import Relation.Binary.PropositionalEquality as P using (_≡_)

  open import Thesis.Regular.Core
  
  data [_]-[_]_≈[_]_ : (R : Reg) → (X : Set) → ⟦ R ⟧ X
                                 → (Y : Set) → ⟦ R ⟧ Y → Set₁ where
    ≈-1′  : ∀ {X : Set} {Y : Set}                    → [ 1′  ]-[ X ] tt ≈[ Y ] tt
    ≈-K   : ∀ {A : Set} {a : A} {X : Set} {Y : Set}  → [ K A ]-[ X ] a  ≈[ Y ] a
    ≈-I   : ∀ {X : Set} {x}                          → [ I ]-[ X ] x ≈[ X ] x
    ≈-⨁₁ : ∀ {R Q : Reg} {X Y : Set} {x y} → [ R ]-[ X ] x ≈[ Y ] y → [ R ⨁ Q ]-[ X ] (inj₁ x) ≈[ Y ] (inj₁ y)
    ≈-⨁₂ : ∀ {R Q : Reg} {X Y : Set} {x y} → [ Q ]-[ X ] x ≈[ Y ] y → [ R ⨁ Q ]-[ X ] (inj₂ x) ≈[ Y ] (inj₂ y)
    ≈-⨂  : ∀ {R Q : Reg} {X Y : Set} {x₁ x₂ y₁ y₂}  → [ R ]-[ X ] x₁ ≈[ Y ] x₂ → [ Q ]-[ X ] y₁ ≈[ Y ] y₂ → [ R ⨂ Q ]-[ X ] (x₁ , y₁) ≈[ Y ] (x₂ , y₂)

  private
    refl : ∀ {X : Set} {R : Reg} {x} → [ R ]-[ X ] x ≈[ X ] x
    refl {R = 0′} {()}
    refl {R = 1′} {tt} = ≈-1′
    refl {R = I}       = ≈-I
    refl {R = K A}     = ≈-K
    refl {R = R ⨁ Q} {inj₁ x} = ≈-⨁₁ refl
    refl {R = R ⨁ Q} {inj₂ y} = ≈-⨁₂ refl
    refl {R = R ⨂ Q} {_ , _}  = ≈-⨂  refl refl

    sym : ∀ {X Y : Set} {R : Reg} {x y} → [ R ]-[ X ] x ≈[ Y ] y → [ R ]-[ Y ] y ≈[ X ] x
    sym ≈-1′ = ≈-1′
    sym ≈-K  = ≈-K
    sym ≈-I  = ≈-I
    sym (≈-⨁₁ eq)     = ≈-⨁₁ (sym eq)
    sym (≈-⨁₂ eq)     = ≈-⨁₂ (sym eq)
    sym (≈-⨂ eq₁ eq₂) = ≈-⨂ (sym eq₁) (sym eq₂)

    trans : ∀ {X Y Z : Set} {R : Reg} {x y z} → [ R ]-[ X ] x ≈[ Y ] y → [ R ]-[ Y ] y ≈[ Z ] z → [ R ]-[ X ] x ≈[ Z ] z
    trans ≈-1′ ≈-1′ = ≈-1′
    trans ≈-K ≈-K   = ≈-K
    trans ≈-I eq₂   = eq₂
    trans (≈-⨁₁ eq₁) (≈-⨁₁ eq₂)       = ≈-⨁₁ (trans eq₁ eq₂)
    trans (≈-⨁₂ eq₁) (≈-⨁₂ eq₂)       = ≈-⨁₂ (trans eq₁ eq₂)
    trans (≈-⨂ eq₁ eq₃) (≈-⨂ eq₂ eq₄) = ≈-⨂  (trans eq₁ eq₂) (trans eq₃ eq₄)

--  ≈-to-≡ : ∀ {X Y : Set} {R : Reg} {x y} → X ≡ Y → [ R ]-[ X ] x ≈[ Y ] y → x ≡ y
--  ≈-to-≡ = ?
