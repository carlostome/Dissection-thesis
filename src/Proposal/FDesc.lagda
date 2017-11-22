\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module Proposal.FDesc where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; _,_)
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
  open import Relation.Binary.PropositionalEquality
  open import Function
\end{code}

%<*FDesc>
\begin{code}
  data FDesc : Set₁ where
    I₁    :                  FDesc
    K₁    : (A : Set)      → FDesc
    _+₁_  : (P Q : FDesc)  → FDesc
    _×₁_  : (P Q : FDesc)  → FDesc

  ⟦_⟧₁ : FDesc → (Set → Set)
  ⟦ I₁      ⟧₁  X  = X
  ⟦ K₁ A    ⟧₁  X  = A
  ⟦ P +₁ Q  ⟧₁  X  = (⟦ P ⟧₁ X) ⊎ (⟦ Q ⟧₁ X)
  ⟦ P ×₁ Q  ⟧₁  X  = (⟦ P ⟧₁ X) × (⟦ Q ⟧₁ X)
\end{code}
%</FDesc>

\begin{code}
  infixl 30 _+₁_
  infixl 40 _×₁_
\end{code}

\begin{code}
  module Maybe-Example where
\end{code}

%<*Maybe>
\begin{code}
    data Maybe (A : Set) : Set where
      Just     : A → Maybe A
      Nothing  : Maybe A

    fmap : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
    fmap f (Just x) = Just (f x)
    fmap f Nothing  = Nothing


    Maybe-FDesc : FDesc
    Maybe-FDesc = I₁ +₁ K₁ ⊤

    Maybe′ : Set -> Set
    Maybe′ = ⟦ Maybe-FDesc ⟧₁

    pattern Just′ x  = inj₁ x
    pattern Nothing′ = inj₂ tt

    from : ∀ {A : Set} -> Maybe A → Maybe′ A
    from (Just x)  = Just′ x
    from Nothing   = Nothing′

    to : ∀ {A : Set} -> Maybe′ A → Maybe A
    to (Just′ x)  = Just x
    to Nothing′   = Nothing
\end{code}
%</Maybe>

%<*fmap>
\begin{code}
  fmap : ∀ {A B : Set} (F : FDesc) → (A → B) → ⟦ F ⟧₁ A → ⟦ F ⟧₁ B
  fmap I₁       f x         = f x
  fmap (K₁ A)   f x         = x
  fmap (P +₁ Q) f (inj₁ x)  = inj₁ (fmap P f x)
  fmap (P +₁ Q) f (inj₂ y)  = inj₂ (fmap Q f y)
  fmap (P ×₁ Q) f (x , y)   = fmap P f x , fmap Q f y

  law₁ : ∀ (F : FDesc) (X : Set) → ∀ (x : ⟦ F ⟧₁ X) → fmap F id x ≡ x
  law₁ I₁ X x     = refl
  law₁ (K₁ A) X x = refl
  law₁ (F +₁ G) X (inj₁ x)        = cong inj₁ (law₁ F X x)
  law₁ (F +₁ G) X (inj₂ y)        = cong inj₂ (law₁ G X y)
  law₁ (F ×₁ G) X (proj₁ , proj₂) = cong₂ _,_ (law₁ F X proj₁) (law₁ G X proj₂)

  law₂ : ∀ (F : FDesc) (X Y Z : Set) → ∀ (f : Y → Z) (g : X →  Y)
       → ∀ (x : ⟦ F ⟧₁ X) → fmap F (f ∘′ g) x ≡ (fmap F f ∘′ fmap F g) x
  law₂ I₁ X Y Z f g x     = refl
  law₂ (K₁ A) X Y Z f g x = refl
  law₂ (F +₁ G) X Y Z f g (inj₁ x) = {!!}
  law₂ (F +₁ G) X Y Z f g (inj₂ y) = {!!}
  law₂ (F ×₁ G) X Y Z f g (proj₁ , proj₂) = {!!}
\end{code}
%</fmap>

%<*mu>
\begin{code}
  data μ (F : FDesc) : Set where
    μ-in : ⟦ F ⟧₁ (μ F) → μ F

  μ-out : ∀ {F : FDesc} → μ F → ⟦ F ⟧₁ (μ F)
  μ-out (μ-in x) = x
\end{code}
%</mu>

\begin{code}
  module Nat-Example where
\end{code}

%<*nat>
\begin{code}
    data Nat : Set where
      zero : Nat
      suc  : Nat → Nat

    NatFDesc : FDesc
    NatFDesc = I₁ +₁ K₁ ⊤

    Nat′ : Set
    Nat′ = μ NatFDesc

    pattern suc′ x  = μ-in (inj₁ x)
    pattern zero′   = μ-in (inj₂ tt)

    from :  Nat → Nat′
    from zero    = zero′
    from (suc x) = suc′ (from x)

    to : Nat′ → Nat
    to zero′    = zero
    to (suc′ x) = suc (to x)
\end{code}
%</nat>

%<*cata-nt>
\begin{code}
  {-# TERMINATING #-}
  cata-nt : ∀ {a} (F : FDesc) → (⟦ F ⟧₁ a -> a) → μ F → a
  cata-nt F ϕ (μ-in x) = ϕ (fmap F (cata-nt F ϕ) x)
\end{code}
%</cata-nt>

%<*cata>
\begin{code}
  mapFold : ∀ {a} (F G : FDesc) → (⟦ G ⟧₁ a -> a) -> ⟦ F ⟧₁ (μ G) -> ⟦ F ⟧₁ a
  mapFold I₁        G ϕ (μ-in x)  = ϕ (mapFold G G ϕ x)
  mapFold (K₁ A)    G ϕ x         = x
  mapFold (P +₁ Q)  G ϕ (inj₁ x)  = inj₁ (mapFold P G ϕ x)
  mapFold (P +₁ Q)  G ϕ (inj₂ y)  = inj₂ (mapFold Q G ϕ y)
  mapFold (P ×₁ Q)  G ϕ (x , y)   = mapFold P G ϕ x , mapFold Q G ϕ y

  cata : ∀ {A : Set} (F : FDesc) → (⟦ F ⟧₁ A -> A) → μ F -> A
  cata  F ϕ (μ-in x) = ϕ (mapFold F F ϕ x)
\end{code}
%</cata>
