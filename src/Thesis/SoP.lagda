\begin{code}
module Thesis.SoP where

  open import Data.List
  open import Data.Empty
  open import Data.Unit
  open import Data.Product hiding (map)
  open import Data.Sum hiding (map)
  open import Function

  data Atom : Set where
    0′ : Atom
    1′ : Atom
    I  : Atom

  Prod : Set
  Prod = List Atom

  Sum : Set
  Sum = List Prod

  ⟦_⟧ₐ : Atom → (Set → Set)
  ⟦ 0′ ⟧ₐ X = ⊥
  ⟦ 1′ ⟧ₐ X = ⊤
  ⟦ I  ⟧ₐ X = X

  ⟦_⟧ₚ : Prod → (Set → Set)
  ⟦ [] ⟧ₚ X     = ⊤
  ⟦ x ∷ xs ⟧ₚ X = ⟦ x ⟧ₐ X × ⟦ xs ⟧ₚ X

  ⟦_⟧ₛ : Sum → (Set → Set)
  ⟦ [] ⟧ₛ X     = ⊥
  ⟦ x ∷ xs ⟧ₛ X = ⟦ x ⟧ₚ X × ⟦ xs ⟧ₛ X

  -- What is a one-hole context in the SoP universe?
  -- This is not a good representation because:
  -- the resulting derivative of a product has to have for each new generated
  -- product at most one I.

  data Fix (σ : Sum) : Set where
    ⟨_⟩ : ⟦ σ ⟧ₛ (Fix σ) → Fix σ

  natF : Sum
  natF = [ 1′ ] ∷ (I ∷ []) ∷ []

  natF-ϑ : Sum
  natF-ϑ = [ 0′ ] ∷ ( 1′ ∷ []) ∷ []

  binF : Sum
  binF = [ 1′ ] ∷ (I ∷ I ∷ []) ∷ []

  binF-ϑ : Sum
  binF-ϑ = [ 0′ ] ∷ (I ∷ 1′ ∷ []) ∷ (1′ ∷ I ∷ []) ∷ []

  ϑₐ : Atom → Atom
  ϑₐ 0′ = 0′
  ϑₐ 1′ = 0′
  ϑₐ I  = 1′

  ϑₚ : Prod → List Prod
  ϑₚ = proj₁
     ∘ foldr (λ {x (ys , xs) → (ϑₐ x ∷ xs) ∷ map (x ∷_) ys  , x ∷ xs})
             ([] , [])

  ϑₛ : Sum → Sum
  ϑₛ = concatMap ϑₚ

  plugₐ : (α : Atom) → (Set → Set)
  plugₐ 0′ x = {!!}
  plugₐ 1′ x = x
  plugₐ I x  = {!!} -- this is bogus

  plug : ∀ {X : Set} → (σ : Sum) → ⟦ ϑₛ σ ⟧ₛ X → X → ⟦ σ ⟧ₛ X
  plug [] () x
  plug (x₁ ∷ σ) S x = {!!}

  vin = ϑₛ binF

  nat = Fix natF
