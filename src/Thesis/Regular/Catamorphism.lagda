\begin{code}
module Thesis.Regular.Catamorphism where

  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty

  open import Thesis.Regular.Core
    
  mapFold : ∀ {A : Set} (R Q : Reg) → (⟦ Q ⟧ A -> A) -> ⟦ R ⟧ (μ Q) -> ⟦ R ⟧ A
  mapFold 0′ Q alg ()
  mapFold 1′ Q alg tt    = tt
  mapFold I Q alg (In x) = alg (mapFold Q Q alg x)
  mapFold (K A) Q alg x  = x
  mapFold (R ⨁ Q) P alg (inj₁ x) = inj₁ (mapFold R P alg x)
  mapFold (R ⨁ Q) P alg (inj₂ y) = inj₂ (mapFold Q P alg y)
  mapFold (R ⨂ Q) P alg (x , y)  = (mapFold R P alg x) , (mapFold Q P alg y)

  data MapFold {X : Set} (Q : Reg) (alg : ⟦ Q ⟧ X → X) : (R : Reg) → ⟦ R ⟧ (μ Q) → ⟦ R ⟧ X → Set where
    MapFold-1′  : MapFold Q alg 1′ tt tt
    MapFold-I   : ∀ {i o} → MapFold Q alg Q i o → MapFold Q alg I (In i) (alg o)
    MapFold-K   : ∀ {A} {a} → MapFold Q alg (K A) a a
    MapFold-⨁₁ : ∀ {R P} {i o} → MapFold Q alg R i o → MapFold Q alg (R ⨁ P) (inj₁ i) (inj₁ o)
    MapFold-⨁₂ : ∀ {R P} {i o} → MapFold Q alg P i o → MapFold Q alg (R ⨁ P) (inj₂ i) (inj₂ o)
    MapFold-⨂  : ∀ {R P} {i₁ i₂} {o₁ o₂} → MapFold Q alg R i₁ o₁ → MapFold Q alg P i₂ o₂ → MapFold Q alg (R ⨂ P) (i₁ , i₂) (o₁ , o₂)

  cata : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A -> A) → μ R -> A
  cata  R alg (In x) = alg (mapFold R R alg x)
  
  data Catamorphism {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) : μ R → X → Set where
    Cata : ∀ {i o} → MapFold R alg R i o → Catamorphism R alg (In i) (alg o)
