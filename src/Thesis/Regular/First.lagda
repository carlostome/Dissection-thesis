\begin{code}
module Thesis.Regular.First where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)

  open import Thesis.Regular.Core
  open import Thesis.Regular.Dissection
    renaming ( Lt to Dissection-Lt
             ; IxLt to Dissection-IxLt
             ; Lt-to-IxLt to Dissection-Lt-to-IxLt
             ; IxLt-WF to Dissection-IxLt-WF
             ; proof-irrelevance to Plug-proof-irrelevance)
  open import Thesis.Regular.NonRec
    renaming (proof-irrelevance to NonRec-proof-irrelevance)
 
  -- First indicates that a ⟦ R ⟧ X has a leftmost hole
  data First {X Y : Set} : (R : Reg) → ⟦ R ⟧ X → ∇ R Y X × X → Set where
    First-⨁-inj₁ : ∀ {R Q} {r} {rx x} → First R r (rx , x) → First (R ⨁ Q) (inj₁ r) (inj₁ rx , x)
    First-⨁-inj₂ : ∀ {R Q} {q} {qx x} → First Q q (qx , x) → First (R ⨁ Q) (inj₂ q) (inj₂ qx , x)
    First-I       : ∀ {x} → First I x (tt , x)
    First-⨂₁     : ∀ {R Q} {rx x} {r q} → First R r (rx , x) → First (R ⨂ Q) (r , q) (inj₁ (rx , q) , x)
    First-⨂₂     : ∀ {R Q} {qx x} {r q} → (isl : NonRec R r) → First Q q (qx , x) → First  (R ⨂ Q) (r , q) (inj₂ (coerce r isl , qx) , x)

  -- Given a proof that we can dissect some tree, it can not be non-recursive
  First-NonRec : ∀ {X Y : Set} {R : Reg} {r : ⟦ R ⟧ X} {rx : ∇ R Y X} {x : X}
               → First R r (rx , x) → NonRec R r → ⊥
  First-NonRec () NonRec-1′
  First-NonRec () (NonRec-K B b)
  First-NonRec (First-⨁-inj₁ x₁) (NonRec-⨁-inj₁ R Q r x₂) = First-NonRec x₁ x₂
  First-NonRec (First-⨁-inj₂ x₁) (NonRec-⨁-inj₂ R Q q x₂) = First-NonRec x₁ x₂
  First-NonRec (First-⨂₁ x₁) (NonRec-⨂ R Q r q x₂ x₃)     = First-NonRec x₁ x₂
  First-NonRec (First-⨂₂ isl x₁) (NonRec-⨂ R Q r q x₂ x₃) = First-NonRec x₁ x₃

  -- First is a functional relation
  First-unicity : ∀ {X Y : Set} {R : Reg} {r : ⟦ R ⟧ X} {x y : ∇ R Y X × X} → First R r x → First R r y → x ≡ y
  First-unicity (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) with First-unicity f₁ f₂
  First-unicity (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) | refl = refl
  First-unicity (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) with First-unicity f₁ f₂
  First-unicity (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) | refl = refl
  First-unicity First-I First-I = refl
  First-unicity (First-⨂₁ f₁) (First-⨂₁ f₂) with First-unicity f₁ f₂
  First-unicity (First-⨂₁ f₁) (First-⨂₁ f₂) | refl = refl
  First-unicity (First-⨂₁ f₁) (First-⨂₂ x f₂) = ⊥-elim (First-NonRec f₁ x)
  First-unicity (First-⨂₂ x f₁) (First-⨂₁ f₂) = ⊥-elim (First-NonRec  f₂ x)
  First-unicity (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) with First-unicity f₁ f₂
  First-unicity (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) | refl with NonRec-proof-irrelevance x x′
  ... | refl = refl

\end{code}

