\begin{code}
module Thesis.Regular.Core where

  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty

  open import Relation.Binary.PropositionalEquality renaming (proof-irrelevance to ≡-proof-irrelevance)
  data Reg : Set₁ where
    0′    : Reg
    1′    : Reg
    I     : Reg
    K     : (A : Set) → Reg
    _⨁_  : (r₁ r₂ : Reg) → Reg
    _⨂_  : (r₁ r₂ : Reg) → Reg

  infixl 30 _⨁_
  infixl 40 _⨂_

  ⟦_⟧ : Reg → (Set → Set)
  ⟦ 0′ ⟧ X  = ⊥
  ⟦ 1′ ⟧ X  = ⊤
  ⟦ K A ⟧ X = A 
  ⟦ I ⟧  X  = X
  ⟦ F ⨁ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
  ⟦ F ⨂ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

  fmap : ∀ {A B : Set} (R : Reg) → (A → B) → ⟦ R ⟧ A → ⟦ R ⟧ B
  fmap 0′ f ()
  fmap 1′ f tt   = tt
  fmap I f x     = f x
  fmap (K A) f x = x 
  fmap (R ⨁ Q) f (inj₁ x)  = inj₁ (fmap R f x)
  fmap (R ⨁ Q) f (inj₂ y)  = inj₂ (fmap Q f y)
  fmap (R ⨂ Q) f (x , y)   = (fmap R f x) , (fmap Q f y)

  data Fmap {A B : Set} (f : A → B) : (R : Reg) → ⟦ R ⟧ A → ⟦ R ⟧ B → Set where
    Fmap-1′  : Fmap f 1′ tt tt
    Fmap-I   : ∀ {x} → Fmap f I x (f x)
    Fmap-K   : ∀ {A : Set} {a}  → Fmap f (K A) a a
    Fmap-⨁₁ : ∀ {R Q} {r} {r′} → Fmap f R r r′ → Fmap f (R ⨁ Q) (inj₁ r) (inj₁ r′)
    Fmap-⨁₂ : ∀ {R Q} {q} {q′} → Fmap f Q q q′ → Fmap f (R ⨁ Q) (inj₂ q) (inj₂ q′)
    Fmap-⨂  : ∀ {R Q} {r q} {r′ q′} → Fmap f R r r′ → Fmap f Q q q′ → Fmap f (R ⨂ Q) (r , q) (r′ , q′)

  -- Fmap is proof-irrelevant
  proof-irrelevance : ∀ {A B : Set} {f : A → B} {R : Reg} {i o} → (f₁ f₂ : Fmap f R i o) → f₁ ≡ f₂
  proof-irrelevance Fmap-1′ Fmap-1′ = refl
  proof-irrelevance Fmap-I Fmap-I = refl
  proof-irrelevance Fmap-K Fmap-K = refl
  proof-irrelevance (Fmap-⨁₁ f₁) (Fmap-⨁₁ f₂)     = cong Fmap-⨁₁ (proof-irrelevance f₁ f₂)
  proof-irrelevance (Fmap-⨁₂ f₁) (Fmap-⨁₂ f₂)     = cong Fmap-⨁₂ (proof-irrelevance f₁ f₂)
  proof-irrelevance (Fmap-⨂ f₁ f₃) (Fmap-⨂ f₂ f₄) = cong₂ Fmap-⨂ (proof-irrelevance f₁ f₂) (proof-irrelevance f₃ f₄)


  data μ (R : Reg) : Set where
    In : ⟦ R ⟧ (μ R) → μ R
\end{code}
