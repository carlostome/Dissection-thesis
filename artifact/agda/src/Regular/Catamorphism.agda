
module Regular.Catamorphism where

  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty
  open import Relation.Binary.PropositionalEquality

  open import Regular.Core

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
    MapFold-I   : ∀ {i : ⟦ Q ⟧ (μ Q)} {o : ⟦ Q ⟧ X} → MapFold Q alg Q i o → MapFold Q alg I (In i) (alg o)
    MapFold-K   : ∀ {A} {a} → MapFold Q alg (K A) a a
    MapFold-⨁₁ : ∀ {R P} {i o} → MapFold Q alg R i o → MapFold Q alg (R ⨁ P) (inj₁ i) (inj₁ o)
    MapFold-⨁₂ : ∀ {R P} {i o} → MapFold Q alg P i o → MapFold Q alg (R ⨁ P) (inj₂ i) (inj₂ o)
    MapFold-⨂  : ∀ {R P} {i₁ : ⟦ R ⟧ (μ Q)} {i₂ : ⟦ P ⟧ (μ Q)} {o₁ : ⟦ R ⟧ X} {o₂ : ⟦ P ⟧ X} → MapFold Q alg R i₁ o₁ → MapFold Q alg P i₂ o₂ → MapFold Q alg (R ⨂ P) (i₁ , i₂) (o₁ , o₂)

  cata : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A -> A) → μ R -> A
  cata  R alg (In x) = alg (mapFold R R alg x)
  
  data Catamorphism {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) : μ R → X → Set where
    Cata : ∀ {i o} → MapFold R alg R i o → Catamorphism R alg (In i) (alg o)

  MapFold-to-mapFold : ∀ {X : Set} (Q : Reg) (alg : ⟦ Q ⟧ X → X) (R : Reg) (t : ⟦ R ⟧ (μ Q))
                     → ∀ (x : ⟦ R ⟧ X) → MapFold Q alg R t x → mapFold R Q alg t ≡ x
  MapFold-to-mapFold Q alg .1′ .tt .tt MapFold-1′ = refl
  MapFold-to-mapFold Q alg .I .(In i) .(alg o) (MapFold-I {i} {o} p) = cong alg (MapFold-to-mapFold Q alg Q i o p)
  MapFold-to-mapFold Q alg .(K _) t .t MapFold-K = refl
  MapFold-to-mapFold Q alg .(_ ⨁ _) .(inj₁ _) .(inj₁ _) (MapFold-⨁₁ p)  = cong inj₁ (MapFold-to-mapFold Q alg _ _ _ p)
  MapFold-to-mapFold Q alg .(_ ⨁ _) .(inj₂ _) .(inj₂ _) (MapFold-⨁₂ p)  = cong inj₂ (MapFold-to-mapFold Q alg _ _ _ p)
  MapFold-to-mapFold Q alg .(_ ⨂ _) .(_ , _) .(_ , _) (MapFold-⨂ p₁ p₂) = cong₂ _,_ (MapFold-to-mapFold Q alg _ _ _ p₁)
                                                                                      (MapFold-to-mapFold Q alg _ _ _ p₂)
  Cata-to-cata : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R)
               → ∀ (x : X) → Catamorphism R alg t x → cata R alg t ≡ x
  Cata-to-cata R alg .(In i) .(alg o) (Cata {i} {o} x) = cong alg (MapFold-to-mapFold R alg R i o x)
