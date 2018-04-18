\begin{code}
module Thesis.Regular.NonRec where
  
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty

  open import Thesis.Regular.Core
  open import Thesis.Regular.Equality

  data NonRec {X : Set} : (R : Reg) → ⟦ R ⟧ X → Set where
    NonRec-1′ : NonRec 1′ tt
    NonRec-K  : (B : Set) → (b : B) → NonRec (K B) b
    NonRec-⨁-inj₁ : (R Q : Reg) → (r : ⟦ R ⟧ X) → NonRec R r → NonRec (R ⨁ Q) (inj₁ r)
    NonRec-⨁-inj₂ : (R Q : Reg) → (q : ⟦ Q ⟧ X) → NonRec Q q → NonRec (R ⨁ Q) (inj₂ q)
    NonRec-⨂      : (R Q : Reg) → (r : ⟦ R ⟧ X) → (q : ⟦ Q ⟧ X) → NonRec R r → NonRec Q q
                                                                 → NonRec (R ⨂ Q) (r , q)

  coerce : ∀ {X : Set} {R : Reg} → (x : ⟦ R ⟧ X) → NonRec R x
         → ∀ {Y : Set} → ⟦ R ⟧ Y
  coerce .tt NonRec-1′ {Y}     = tt
  coerce x (NonRec-K B .x) {Y} = x
  coerce .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr) {Y} = inj₁ (coerce r nr)
  coerce .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr) {Y} = inj₂ (coerce q nr)
  coerce .(r , q) (NonRec-⨂ R Q r q nr nr₁) {Y} = coerce r nr , coerce q nr₁

  coerce-NonRec : ∀ {X : Set} {R : Reg} (x : ⟦ R ⟧ X) → (nr : NonRec R x)
                → ∀ {Y : Set} → NonRec {Y} R (coerce x nr)
  coerce-NonRec .tt NonRec-1′ = NonRec-1′
  coerce-NonRec x (NonRec-K B .x) = NonRec-K B x
  coerce-NonRec .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr) = NonRec-⨁-inj₁ R Q (coerce r nr) (coerce-NonRec r nr)
  coerce-NonRec .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr) = NonRec-⨁-inj₂ R Q (coerce q nr) (coerce-NonRec q nr)
  coerce-NonRec .(r , q) (NonRec-⨂ R Q r q nr nr₁) = NonRec-⨂ R Q (coerce r nr) (coerce q nr₁) (coerce-NonRec r nr) (coerce-NonRec q nr₁)

  coerce-≈ : ∀ {X : Set} {R : Reg} (x : ⟦ R ⟧ X) → (nr : NonRec R x)
           → ∀ {Y : Set} → [ R ]-[ X ] x ≈[ Y ] (coerce x nr)
  coerce-≈ .tt NonRec-1′     = ≈-1′
  coerce-≈ x (NonRec-K B .x) = ≈-K
  coerce-≈ .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr) = ≈-⨁₁ (coerce-≈ r nr)
  coerce-≈ .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr) = ≈-⨁₂ (coerce-≈ q nr)
  coerce-≈ .(r , q) (NonRec-⨂ R Q r q nr nr₁) = ≈-⨂  (coerce-≈ r nr) (coerce-≈ q nr₁)
