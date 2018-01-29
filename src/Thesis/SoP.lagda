\begin{code}
module Thesis.SoP where

  open import Data.List
  open import Data.Empty
  open import Data.Unit
  open import Data.Product hiding (map)
  open import Data.Sum hiding (map)
  open import Function
  open import Data.Fin
  open import Data.Vec
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  module Raw-SoP where

    data Atom : Set where
      0′ : Atom
      1′ : Atom
      I  : Atom

    Atom-dec : (x y : Atom) → Dec (x ≡ y)
    Atom-dec 0′ 0′ = yes refl
    Atom-dec 0′ 1′ = no (λ ())
    Atom-dec 0′ I  = no (λ ())
    Atom-dec 1′ 0′ = no (λ ())
    Atom-dec 1′ 1′ = yes refl
    Atom-dec 1′ I  = no (λ ())
    Atom-dec I 0′  = no (λ ())
    Atom-dec I 1′  = no (λ ())
    Atom-dec I I   = yes refl

    Prod : Set
    Prod = List Atom

    Prod-dec : (x y : Prod) → Dec (x ≡ y)
    Prod-dec [] [] = yes refl
    Prod-dec [] (x ∷ y) = no (λ ())
    Prod-dec (x ∷ x₁) [] = no (λ ())
    Prod-dec (x ∷ xs) (y ∷ ys) with Atom-dec x y | Prod-dec xs ys
    Prod-dec (x ∷ xs) (.x ∷ .xs) | yes refl | yes refl = yes refl
    Prod-dec (x ∷ xs) (.x ∷ ys) | yes refl | no ¬p = no λ { refl → ¬p refl}
    Prod-dec (x ∷ xs) (y ∷ ys) | no ¬p | pd        = no λ { refl → ¬p refl}

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
    ⟦ x ∷ xs ⟧ₛ X = ⟦ x ⟧ₚ X ⊎ ⟦ xs ⟧ₛ X

    ⟦_⟧ₚ₂ : (p : Prod) → Fin (length p) → (Set → Set → Set)
    ⟦ []  ⟧ₚ₂ () X Y
    ⟦ x ∷ p ⟧ₚ₂ zero X Y = ⟦ x ⟧ₐ X × ⟦ p ⟧ₚ Y
    ⟦ x ∷ p ⟧ₚ₂ (suc f) X Y = ⟦ x ⟧ₐ X × ⟦ p ⟧ₚ₂ f X Y

    Prod₂ = Σ Prod λ p → Fin (length p)
    Sum₂  = List Prod₂

    ⟦_⟧ₛ₂ : Sum₂ → (Set → Set → Set)
    ⟦ [] ⟧ₛ₂ X Y     = ⊥
    ⟦ (p , f) ∷ ps ⟧ₛ₂ X Y = ⟦ p ⟧ₚ₂ f X Y ⊎ ⟦ ps ⟧ₛ₂ X Y

  -- we can only compare two products when they are equal bu fin n changes
    Rel₂ₚ : ∀ {X Y : Set} (p : Prod₂) → Set 
    Rel₂ₚ (p , proj₄) x x₁ = {!!}

  -- What is a one-hole context in the SoP universe?
  -- This is not a good representation because:
  -- the resulting derivative of a product has to have for each new generated
  -- product at most one I.

    data Fix (σ : Sum) : Set where
      ⟨_⟩ : ⟦ σ ⟧ₛ (Fix σ) → Fix σ

    -- natF : Sum
    -- natF = ( 1′ ∷ [] ) ∷ (I ∷ []) ∷ []

    -- natF-ϑ : Sum
    -- natF-ϑ = [ 0′ ] ∷ ( 1′ ∷ []) ∷ []

    -- binF : Sum
    -- binF = [ 1′ ] ∷ (I ∷ I ∷ []) ∷ []

    -- binF-ϑ : Sum
    -- binF-ϑ = [ 0′ ] ∷ (I ∷ 1′ ∷ []) ∷ (1′ ∷ I ∷ []) ∷ []

    -- ϑₐ : Atom → Atom
    -- ϑₐ 0′ = 0′
    -- ϑₐ 1′ = 0′
    -- ϑₐ I  = 1′

    -- ϑₚ : Prod → List Prod
    -- ϑₚ = proj₁
    --    ∘ foldr (λ {x (ys , xs) → (ϑₐ x ∷ xs) ∷ map (x ∷_) ys  , x ∷ xs})
    --            ([] , [])

    -- ϑₛ : Sum → Sum
    -- ϑₛ = concatMap ϑₚ

    -- plugₐ : (α : Atom) → (Set → Set)
    -- plugₐ 0′ x = {!!}
    -- plugₐ 1′ x = x
    -- plugₐ I x  = {!!} -- this is bogus

    -- plug : ∀ {X : Set} → (σ : Sum) → ⟦ ϑₛ σ ⟧ₛ X → X → ⟦ σ ⟧ₛ X
    -- plug [] () x
    -- plug (x₁ ∷ σ) S x = {!!}

  module Bi-SoP where

    data Atom : Set where
      0′ : Atom
      1′ : Atom
      I  : Atom
      
    Prod : Set
    Prod = List Atom

    Sum : Set
    Sum = List (Prod × Prod)

    ⟦_⟧ₐ : Atom → (Set → Set)
    ⟦ 0′ ⟧ₐ X = ⊥
    ⟦ 1′ ⟧ₐ X = ⊤
    ⟦ I  ⟧ₐ X = X

    ⟦_⟧ₚ : Prod → (Set → Set)
    ⟦ [] ⟧ₚ X     = ⊤
    ⟦ x ∷ xs ⟧ₚ X = ⟦ x ⟧ₐ X × ⟦ xs ⟧ₚ X

    ⟦_⟧ₛ : Sum → (Set → Set → Set)
    ⟦ [] ⟧ₛ X Y           = ⊥
    ⟦ (x , y) ∷ xs ⟧ₛ X Y = ⟦ x ⟧ₚ X × ⟦ y ⟧ₚ Y ⊎ ⟦ xs ⟧ₛ X Y

    Rel : ∀ {X Y : Set} → (s : Sum) → ⟦ s ⟧ₛ X Y → ⟦ s ⟧ₛ X Y → Set
    Rel [] () y
    Rel ((p₁ , p₂) ∷ s) x y = {!!}
