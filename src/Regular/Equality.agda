
module Regular.Equality where

  open import Data.Unit
  open import Data.Product
  open import Data.Sum
  open import Data.Empty
  open import Relation.Binary.PropositionalEquality
    renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; proof-irrelevance to ≡-proof-irrelevance)

  open import Regular.Core

  ----------------------------------------------------------------------------------------
  --                Heterogeneous equality over regular Functors
  
  data [_]-[_]_≈[_]_ : (R : Reg) → (X : Set) → ⟦ R ⟧ X
                                 → (Y : Set) → ⟦ R ⟧ Y → Set₁ where
    ≈-1′  : ∀ {X : Set} {Y : Set}                    → [ 1′  ]-[ X ] tt ≈[ Y ] tt
    ≈-K   : ∀ {A : Set} {a : A} {X : Set} {Y : Set}  → [ K A ]-[ X ] a  ≈[ Y ] a
    ≈-I   : ∀ {X : Set} {x}                          → [ I ]-[ X ] x ≈[ X ] x
    ≈-⨁₁ : ∀ {R Q : Reg} {X Y : Set} {x y} → [ R ]-[ X ] x ≈[ Y ] y → [ R ⨁ Q ]-[ X ] (inj₁ x) ≈[ Y ] (inj₁ y)
    ≈-⨁₂ : ∀ {R Q : Reg} {X Y : Set} {x y} → [ Q ]-[ X ] x ≈[ Y ] y → [ R ⨁ Q ]-[ X ] (inj₂ x) ≈[ Y ] (inj₂ y)
    ≈-⨂  : ∀ {R Q : Reg} {X Y : Set} {x₁ x₂ y₁ y₂}  → [ R ]-[ X ] x₁ ≈[ Y ] x₂ → [ Q ]-[ X ] y₁ ≈[ Y ] y₂ → [ R ⨂ Q ]-[ X ] (x₁ , y₁) ≈[ Y ] (x₂ , y₂)

  ----------------------------------------------------------------------------------------
  --                Heterogeneous equality is an equivalence relation

  -- equality is reflexive
  refl : ∀ {X : Set} {R : Reg} {x} → [ R ]-[ X ] x ≈[ X ] x
  refl {R = 0′} {()}
  refl {R = 1′} {tt} = ≈-1′
  refl {R = I}       = ≈-I
  refl {R = K A}     = ≈-K
  refl {R = R ⨁ Q} {inj₁ x} = ≈-⨁₁ refl
  refl {R = R ⨁ Q} {inj₂ y} = ≈-⨁₂ refl
  refl {R = R ⨂ Q} {_ , _}  = ≈-⨂  refl refl

  -- symmetric
  sym : ∀ {X Y : Set} {R : Reg} {x y} → [ R ]-[ X ] x ≈[ Y ] y → [ R ]-[ Y ] y ≈[ X ] x
  sym ≈-1′ = ≈-1′
  sym ≈-K  = ≈-K
  sym ≈-I  = ≈-I
  sym (≈-⨁₁ eq)     = ≈-⨁₁ (sym eq)
  sym (≈-⨁₂ eq)     = ≈-⨁₂ (sym eq)
  sym (≈-⨂ eq₁ eq₂) = ≈-⨂ (sym eq₁) (sym eq₂)

  -- and transitive
  trans : ∀ {X Y Z : Set} {R : Reg} {x y z} → [ R ]-[ X ] x ≈[ Y ] y → [ R ]-[ Y ] y ≈[ Z ] z → [ R ]-[ X ] x ≈[ Z ] z
  trans ≈-1′ ≈-1′ = ≈-1′
  trans ≈-K ≈-K   = ≈-K
  trans ≈-I eq₂   = eq₂
  trans (≈-⨁₁ eq₁) (≈-⨁₁ eq₂)       = ≈-⨁₁ (trans eq₁ eq₂)
  trans (≈-⨁₂ eq₁) (≈-⨁₂ eq₂)       = ≈-⨁₂ (trans eq₁ eq₂)
  trans (≈-⨂ eq₁ eq₃) (≈-⨂ eq₂ eq₄) = ≈-⨂  (trans eq₁ eq₂) (trans eq₃ eq₄)

  -- Heterogeneous equality is proof-irrelevant
  proof-irrelevance : ∀ {X Y : Set} {R : Reg} {x y} → (a : [ R ]-[ X ] x ≈[ Y ] y) → (b : [ R ]-[ X ] x ≈[ Y ] y) → a ≡ b
  proof-irrelevance ≈-1′ ≈-1′ = ≡-refl
  proof-irrelevance ≈-K ≈-K = ≡-refl
  proof-irrelevance ≈-I ≈-I = ≡-refl
  proof-irrelevance (≈-⨁₁ a) (≈-⨁₁ b)     = cong ≈-⨁₁ (proof-irrelevance a b)
  proof-irrelevance (≈-⨁₂ a) (≈-⨁₂ b)     = cong ≈-⨁₂ (proof-irrelevance a b)
  proof-irrelevance (≈-⨂ a a₁) (≈-⨂ b b₁) = cong₂ ≈-⨂ (proof-irrelevance a b) (proof-irrelevance a₁ b₁)

  -- In the special case where the type parameter of both Functors coincide
  -- we can recover Propositional equality
  ≈-to-≡ : ∀ {X : Set} {R : Reg} {x y} → [ R ]-[ X ] x ≈[ X ] y → x ≡ y
  ≈-to-≡ ≈-1′ = ≡-refl
  ≈-to-≡ ≈-K  = ≡-refl
  ≈-to-≡ ≈-I  = ≡-refl
  ≈-to-≡ (≈-⨁₁ x₁)   = cong inj₁ (≈-to-≡ x₁)
  ≈-to-≡ (≈-⨁₂ x₁)   = cong inj₂ (≈-to-≡ x₁)
  ≈-to-≡ (≈-⨂ x₁ x₂) = cong₂ _,_ (≈-to-≡ x₁) (≈-to-≡ x₂)

