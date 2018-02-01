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

    data Atom  : Set where
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

  module SSoP where
    open import Data.Nat
    
    data Atom (n : ℕ) : Set where
      0′ : Atom n
      1′ : Atom n
      I  : Fin n → Atom n

    ⟦_⟧ₐ : ∀ {n} → Atom n → Vec Set n → Set
    ⟦ 0′ ⟧ₐ V  = ⊥
    ⟦ 1′ ⟧ₐ V  = ⊤
    ⟦ I x ⟧ₐ V = lookup x V

    Prod : ℕ → Set
    Prod n = List (Atom n)

    ⟦_⟧ₚ : ∀ {n} → Prod n → Vec Set n → Set
    ⟦ [] ⟧ₚ V     = ⊤
    ⟦ x ∷ xs ⟧ₚ V = (⟦ x ⟧ₐ V) × (⟦ xs ⟧ₚ V)

    Sum : ℕ → Set
    Sum n = List (Prod n)

    ⟦_⟧ₛ : ∀ {n} → Sum n → Vec Set n → Set
    ⟦ [] ⟧ₛ V     = ⊥
    ⟦ x ∷ xs ⟧ₛ V = ⟦ x ⟧ₚ V ⊎ ⟦ xs ⟧ₛ V

    SSoP : ℕ → Set
    SSoP n = List (Sum n)

    ⟦_⟧ₛₒₚ : ∀ {n} → SSoP n → Vec Set n → Set
    ⟦ [] ⟧ₛₒₚ V    = ⊥
    ⟦ x ∷ s ⟧ₛₒₚ V = ⟦ x ⟧ₛ V ⊎ ⟦ s ⟧ₛₒₚ V

    Rel : ∀ {n} → Sum n → Sum n → Set
    Rel [] [] = {!!}
    Rel [] (x ∷ x₁) = {!!}
    Rel (x ∷ x₂) x₁ = {!!}
