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

  Fmap-to-fmap : ∀ {A B : Set} {f : A → B} {R : Reg} {x : ⟦ R ⟧ A} {y : ⟦ R ⟧ B}
               → Fmap f R x y → y ≡ fmap R f x
  Fmap-to-fmap Fmap-1′ = refl
  Fmap-to-fmap Fmap-I  = refl
  Fmap-to-fmap Fmap-K  = refl
  Fmap-to-fmap (Fmap-⨁₁ p)   = cong inj₁ (Fmap-to-fmap p)
  Fmap-to-fmap (Fmap-⨁₂ p)   = cong inj₂ (Fmap-to-fmap p)
  Fmap-to-fmap (Fmap-⨂ p p₁) = cong₂ _,_ (Fmap-to-fmap p) (Fmap-to-fmap p₁)
  
  -- Fmap is proof-irrelevant
  Fmap-proof-irrelevance : ∀ {A B : Set} {f : A → B} {R : Reg} {i o} → (f₁ f₂ : Fmap f R i o) → f₁ ≡ f₂
  Fmap-proof-irrelevance Fmap-1′ Fmap-1′ = refl
  Fmap-proof-irrelevance Fmap-I Fmap-I = refl
  Fmap-proof-irrelevance Fmap-K Fmap-K = refl
  Fmap-proof-irrelevance (Fmap-⨁₁ f₁) (Fmap-⨁₁ f₂)     = cong Fmap-⨁₁ (Fmap-proof-irrelevance f₁ f₂)
  Fmap-proof-irrelevance (Fmap-⨁₂ f₁) (Fmap-⨁₂ f₂)     = cong Fmap-⨁₂ (Fmap-proof-irrelevance f₁ f₂)
  Fmap-proof-irrelevance (Fmap-⨂ f₁ f₃) (Fmap-⨂ f₂ f₄) = cong₂ Fmap-⨂ (Fmap-proof-irrelevance f₁ f₂) (Fmap-proof-irrelevance f₃ f₄)

  Fmap-unicity : ∀ {A B : Set} {f : A → B} {R : Reg} {i o o′} → Fmap f R i o → Fmap f R i o′ → o ≡ o′
  Fmap-unicity Fmap-1′ Fmap-1′ = refl
  Fmap-unicity Fmap-I Fmap-I   = refl
  Fmap-unicity Fmap-K Fmap-K   = refl
  Fmap-unicity (Fmap-⨁₁ x) (Fmap-⨁₁ x₁)     = cong inj₁ (Fmap-unicity x x₁)
  Fmap-unicity (Fmap-⨁₂ x) (Fmap-⨁₂ x₁)     = cong inj₂ (Fmap-unicity x x₁)
  Fmap-unicity (Fmap-⨂ x x₂) (Fmap-⨂ x₁ x₃) = cong₂ _,_ (Fmap-unicity x x₁) (Fmap-unicity x₂ x₃)
  data All (A : Set) (P : A → Set) : (R : Reg) → ⟦ R ⟧ A → Set₁ where
    All-I       : ∀ {x : A} → P x → All A P I x
    All-⨂      : ∀ {R Q : Reg} {r : ⟦ R ⟧ A} {q : ⟦ Q ⟧ A} → All A P R r → All A P Q q → All A P (R ⨂ Q) (r , q)
    All-⨁₁     : ∀ {R Q : Reg} {r : ⟦ R ⟧ A} → All A P R r → All A P (R ⨁ Q) (inj₁ r)
    All-⨁₂     : ∀ {R Q : Reg} {q : ⟦ Q ⟧ A} → All A P Q q → All A P (R ⨁ Q) (inj₂ q)
    All-1′      : All A P 1′ tt
    All-K       : ∀ {B : Set} {b : B} → All A P (K B) b  

  data μ (R : Reg) : Set where
    In : ⟦ R ⟧ (μ R) → μ R
\end{code}
