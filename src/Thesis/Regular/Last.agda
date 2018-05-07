
module Thesis.Regular.Last where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  
  open import Thesis.Regular.Core
  open import Thesis.Regular.Dissection
    renaming ( Lt to Dissection-Lt
             ; IxLt to Dissection-IxLt
             ; Lt-to-IxLt to Dissection-Lt-to-IxLt
             ; IxLt-WF to Dissection-IxLt-WF
             ; proof-irrelevance to Plug-proof-irrelevance)
  open import Thesis.Regular.NonRec
    renaming (proof-irrelevance to NonRec-proof-irrelevance)
 
  -- Predicate to test if a dissection has only one hole left
  data Last {X Y : Set} : (R : Reg) → ∇ R Y X → Set where
    Last-⨁-inj₁ : ∀ {R Q} {rx} → Last R rx → Last (R ⨁ Q) (inj₁ rx)
    Last-⨁-inj₂ : ∀ {R Q} {qx} → Last Q qx → Last (R ⨁ Q) (inj₂ qx)
    Last-I       : Last I tt
    Last-⨂₁     : ∀ {R Q} {rx} {q} → (isl : NonRec Q q) → Last R rx → Last (R ⨂ Q) (inj₁ (rx , q))
    Last-⨂₂     : ∀ {R Q} {qx} {r} → Last Q qx          → Last (R ⨂ Q) (inj₂ (r , qx))

  -- Last is a decidable predicate
  Last-Dec : ∀ {X Y : Set} (R : Reg) → (x : ∇ R Y X) → Dec (Last R x)
  Last-Dec 0′ ()
  Last-Dec 1′ ()
  Last-Dec I tt   = yes Last-I
  Last-Dec (K A) ()
  Last-Dec (R ⨁ Q) (inj₁ x) with Last-Dec R x
  Last-Dec (R ⨁ Q) (inj₁ x) | yes p = yes (Last-⨁-inj₁ p)
  Last-Dec (R ⨁ Q) (inj₁ x) | no ¬p = no λ { (Last-⨁-inj₁ x) → ¬p x}
  Last-Dec (R ⨁ Q) (inj₂ y) with Last-Dec Q y
  Last-Dec (R ⨁ Q) (inj₂ y) | yes p = yes (Last-⨁-inj₂ p)
  Last-Dec (R ⨁ Q) (inj₂ y) | no ¬p = no λ { (Last-⨁-inj₂ x) → ¬p x}
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) with Last-Dec R dr
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | yes p with NonRec-Dec Q q
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | yes p | yes p₁ = yes (Last-⨂₁ p₁ p)
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | yes p | no ¬p  = no λ { (Last-⨂₁ isl x) → ¬p isl}
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | no ¬p          = no λ { (Last-⨂₁ isl x) → ¬p x}
  Last-Dec (R ⨂ Q) (inj₂ (r , dq)) with Last-Dec Q dq
  Last-Dec (R ⨂ Q) (inj₂ (r , dq)) | yes p = yes (Last-⨂₂ p)
  Last-Dec (R ⨂ Q) (inj₂ (r , dq)) | no ¬p = no λ { (Last-⨂₂ x) → ¬p x}

