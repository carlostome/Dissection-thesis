module Example.Mobile where

  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Bool
  open import Regular.Core
  open import Regular
  open import Data.Maybe
  open import Data.Sum
  open import Data.Product
  open import Function

  _≟ℕ_ : ℕ → ℕ → Bool
  zero ≟ℕ zero   = true
  zero ≟ℕ suc m  = false
  suc n ≟ℕ zero  = false
  suc n ≟ℕ suc m = n ≟ℕ m 

  data Mobile : Set where
    OBJ : ℕ → Mobile
    BAR : ℕ → Mobile → Mobile → Mobile 

  m₁ : Mobile
  m₁ = BAR 1 (BAR 1 (OBJ 2) (OBJ 2)) (OBJ 5)

  m₂ : Mobile
  m₂ = BAR 1 (OBJ 6) (BAR 1 (OBJ 2) (OBJ 9))
  
  weight : Mobile → ℕ
  weight (OBJ n) = n
  weight (BAR n m₁ m₂) = n + weight m₁ + weight m₂
  
  p₁ : weight m₁ ≡ 11
  p₁ = refl

  p₂  : weight m₂ ≡ 19
  p₂ = refl

  -- check whether a Mobile is equilibrated
  equil : Mobile → Bool
  equil (OBJ x) = true
  equil (BAR _ m₁ m₂) = weight m₁ ≟ℕ weight m₂ ∧ equil m₁ ∧ equil m₂

  -- Generic construction
  MobileF : Reg
  MobileF = K ℕ ⨁ (K ℕ ⨂ (I ⨂ I))
  
  Mobileᴳ : Set
  Mobileᴳ = μ MobileF

  

  φ : ⟦ MobileF ⟧ (Maybe ℕ) → Maybe ℕ
  φ (inj₁ n)            = just n
  φ (inj₂ (n , just m₁ , just m₂))  = if m₁ ≟ℕ m₂ then just (n + m₁ + m₂) else nothing
  φ (inj₂ (n , _ , _))             = nothing

  from : Mobile → Mobileᴳ
  from (OBJ n)      = In (inj₁ n)
  from (BAR n m₁ m₂) = In (inj₂ (n , from m₁ , from m₂))
  
  equilᴳ : Mobile → Bool
  equilᴳ = is-just ∘ tail-rec-cata MobileF φ ∘ from

  prop₁ : equilᴳ m₁ ≡ true
  prop₁ = refl

  prop₂ : equilᴳ m₂ ≡ false
  prop₂ = refl
