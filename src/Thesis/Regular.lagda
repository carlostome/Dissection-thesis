\begin{code}
module Thesis.Regular where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
  open import Relation.Binary.PropositionalEquality
  open import Function
  open import Data.List
  open import Data.Nat
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Induction.WellFounded
  open import Data.Maybe

  data Reg : Set where
    0′    : Reg
    1′    : Reg
    V     : Reg
    _⨁_  : (r₁ r₂ : Reg) → Reg
    _⨂_  : (r₁ r₂ : Reg) → Reg

  infixl 30 _⨁_
  infixl 40 _⨂_

  ⟦_⟧ : Reg → (Set → Set)
  ⟦ 0′ ⟧ X  = ⊥
  ⟦ 1′ ⟧ X  = ⊤
  ⟦ V ⟧  X  = X
  ⟦ F ⨁ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
  ⟦ F ⨂ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

  fmap : ∀ {A B : Set} (R : Reg) → (A → B) → ⟦ R ⟧ A → ⟦ R ⟧ B
  fmap 0′ f ()
  fmap 1′ f tt  = tt
  fmap V f x    = f x
  fmap (R ⨁ Q) f (inj₁ x)  = inj₁ (fmap R f x)
  fmap (R ⨁ Q) f (inj₂ y)  = inj₂ (fmap Q f y)
  fmap (R ⨂ Q) f (x , y)   = (fmap R f x) , (fmap Q f y)

  data μ (R : Reg) : Set where
    In : ⟦ R ⟧ (μ R) → μ R

  ϑ : Reg → Reg
  ϑ 0′  = 0′
  ϑ 1′  = 0′
  ϑ V   = 1′
  ϑ (f ⨁ g) = ϑ f ⨁ ϑ g
  ϑ (f ⨂ g) = ϑ f ⨂ g ⨁ f ⨂ ϑ g

  -- first : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → Maybe (⟦ ϑ R ⟧ X × X)
  first : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → (⟦ ϑ R ⟧ X × X) ⊎ ⟦ R ⟧ ⊥
  first 0′ x = inj₂ x
  first 1′ x = inj₂ tt
  first V x  = inj₁ (tt , x)
  first (R ⨁ Q) (inj₁ x) with first R x
  first (R ⨁ Q) (inj₁ x) | inj₁ (dR , x′ ) = inj₁ (inj₁ dR , x′)
  first (R ⨁ Q) (inj₁ x) | inj₂ y          = inj₂ (inj₁ y)
  first (R ⨁ Q) (inj₂ y) = {!!}
  first (R ⨂ Q) x = {!!}

  first-μ : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ (μ R) → (List (⟦ ϑ R ⟧ (μ R)) × ⟦ R ⟧ ⊥) ⊎ ⟦ R ⟧ ⊥
  first-μ R x with first R x
  first-μ R x | inj₁ (ctx , In mu) = {!!}
  first-μ R x | inj₂ y = {!!}

  data Reg₂ : Set where
    0′   :  Reg₂
    1′   :  Reg₂
    F    :  Reg₂
    S    :  Reg₂
    C    :  Reg → Reg₂
    J    :  Reg → Reg₂
    _⨁_  : (P Q : Reg₂)  → Reg₂
    _⨂_  : (P Q : Reg₂)  → Reg₂

  ⟦_⟧₂ : Reg₂ → (Set → Set → Set)
  ⟦ 0′  ⟧₂ X Y = ⊥
  ⟦ 1′  ⟧₂ X Y = ⊤
  ⟦ F   ⟧₂ X Y = X
  ⟦ S   ⟧₂ X Y = Y
  ⟦ C R ⟧₂ X Y  = ⟦ R ⟧ X
  ⟦ J R ⟧₂ X Y  = ⟦ R ⟧ Y
  ⟦ R ⨁ Q ⟧₂ X Y = ⟦ R ⟧₂ X Y ⊎ ⟦ Q ⟧₂ X Y
  ⟦ R ⨂ Q ⟧₂ X Y = ⟦ R ⟧₂ X Y × ⟦ Q ⟧₂ X Y

  ∇ : Reg → Reg₂
  ∇ 0′ = 0′
  ∇ 1′ = 0′
  ∇ V  = 1′
  ∇ (R ⨁ Q) = ∇ R ⨁ ∇ Q
  ∇ (R ⨂ Q) = (∇ R ⨂ J Q) ⨁ (C R ⨂ ∇ Q)

  Rel₂ : ∀ {X Y : Set} → (R : Reg₂) → ⟦ R ⟧₂ X Y → ⟦ R ⟧₂ X Y → Set
  Rel₂ 0′ () y
  Rel₂ 1′ x y = ⊥
  Rel₂ F x y  = ⊥
  Rel₂ S x y  = ⊥
  Rel₂ (C R) x y    = ⊥
  Rel₂ (J R) x y    = ⊥
  Rel₂ (R ⨁ Q) (inj₁ x) (inj₁ y)  = Rel₂ R x y
  Rel₂ (R ⨁ Q) (inj₁ x) (inj₂ y)  = ⊥
  Rel₂ (R ⨁ Q) (inj₂ x) (inj₁ y)  = ⊤
  Rel₂ (R ⨁ Q) (inj₂ x) (inj₂ y) = Rel₂ Q x y
  Rel₂ (R ⨂ Q) x y = {!!}

  Zipper : Reg → (Set → Set)
  Zipper R X = μ R × List (⟦ ∇ R ⟧₂ (μ R × X) (μ R))

  Rel : ∀ {X : Set} (R : Reg) → Zipper R X → Zipper R X → Set
  Rel R  (t₁ , []) (t₂ , [])      = ⊥
  Rel 0′ (t₁ , []) (t₂ , () ∷ s₂)
  Rel 1′ (t₁ , []) (t₂ , () ∷ s₂)
  Rel V  (t₁ , [])  (t₂ , x ∷ s₂) = {!!}
  Rel (R ⨁ R₁) (t₁ , []) (t₂ , inj₁ x ∷ s₂) = {!!}
  Rel (R ⨁ R₁) (t₁ , []) (t₂ , inj₂ y ∷ s₂) = {!!}
  Rel (R ⨂ Q)  (t₁ , []) (t₂ , inj₁ (dr , q) ∷ s₂) = {!!} -- we need to be able to say that t₁ contains recursive positions
  Rel (R ⨂ Q) (t₁ , []) (t₂ , inj₂ (r , dq) ∷ s₂) = {!!}
  Rel R (t₁ , x ∷ s₁) (t₂ , s₂) = {!s₂!}

  module Normal-Form where
  
    data Reg-A : Set where
                         
    data Reg-⨂ : Set where
      _⨂-c_ : (r₁ r₂ : Reg-⨂) → Reg-⨂
      ⨂-l_  : Reg-A → Reg-⨂

    data Reg-⨁ : Set where
      _⨁-c_  : (r₁ r₂ : Reg-⨁) → Reg-⨁
      _⨁-l_  : (r₁ r₁ : Reg-⨂)  → Reg-⨁

  -- first 1′ x = {!!}
  -- first V x  = just (tt , x)
  -- first (u ⨁ v) (inj₁ x) with first u x
  -- first (u ⨁ v) (inj₁ x) | just (du , x′) = just (inj₁ du , x′)
  -- first (u ⨁ v) (inj₁ x) | nothing        = nothing
  -- first (u ⨁ v) (inj₂ y) with first v y
  -- first (u ⨁ v) (inj₂ y) | just (x′ , dv) = just (inj₂ x′ , dv)
  -- first (u ⨁ v) (inj₂ y) | nothing        = nothing
  -- first (u ⨂ v) (u′ , v′) with first u u′
  -- first (u ⨂ v) (u′ , v′) | just (du , x) = just (inj₁ (du , v′) , x)
  -- first (u ⨂ v) (u′ , v′) | nothing with first v v′
  -- first (u ⨂ v) (u′ , v′) | nothing | just (dv , x) = just ((inj₂ (u′ , dv)) , x)
  -- first (u ⨂ v) (u′ , v′) | nothing | nothing       = nothing

  -- first-μ : {X : Set} (R : Reg) → (μ R × ⟦ ϑ R ⟧ (μ R))
  -- first-μ 0′ k (In ())
  -- first-μ 1′ k (In tt) = nothing
  -- first-μ V k (In x) = k x tt
  -- first-μ (R ⨁ Q) k (In (inj₁ x)) = first-μ R (λ mu ctx → k {!!} {!!}) {!x!}
  -- first-μ (R ⨁ Q) k (In (inj₂ y)) = {!!}
  -- first-μ (R ⨂ Q) k (In (x , y)) = {!!}

-- \begin{code}
--       where ∙∙∙ : (R : Reg) → μ R → Maybe (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
--             ∙∙∙ = {!!}
-- \end{code}
-- \begin{code}
--   module Differentiation where
--     open import Data.Maybe
-- \end{code}
--   %<*Differentiation>
--   \begin{code}
--   \end{code}
--   %</Differentiation>

-- %<*Plug>
-- \begin{co

-- de}

--     plug : ∀ {X : Set} → (R : Reg) → ⟦ ϑ R ⟧ X → X → ⟦ R ⟧ X
--     plug 0′ () x
--     plug 1′ () x
--     plug V tt x = x
--     plug (u ⨁ v) (inj₁ u′) x  = inj₁ (plug u u′ x)
--     plug (u ⨁ v) (inj₂ v′) x  = inj₂ (plug v v′ x)
--     plug (u ⨂ v) (inj₁ (du , v′)) x = plug u du x  , v′
--     plug (u ⨂ v) (inj₂ (u′ , dv)) x = u′           , plug v dv x
-- \end{code}
-- %</Plug>


-- %<*Plug-Mu>
-- \begin{code}
--     plug-μ : ∀ (R : Reg) → μ R → List (⟦ ϑ R ⟧ (μ R)) → μ R
--     plug-μ u t []         = t
--     plug-μ 0′ t (() ∷ xs)
--     plug-μ 1′ t (() ∷ xs)
--     plug-μ V t (tt ∷ xs)  = t
--     plug-μ (u ⨁ v) t (inj₁ du ∷ xs)         = In (inj₁ (plug u du (plug-μ (u ⨁ v) t xs)))
--     plug-μ (u ⨁ v) t (inj₂ dv ∷ xs)         = In (inj₂ (plug v dv (plug-μ (u ⨁ v) t xs)))
--     plug-μ (u ⨂ v) t (inj₁ (du , v′) ∷ xs)  = In ((plug u du (plug-μ (u ⨂ v) t xs)) , v′)
--     plug-μ (u ⨂ v) t (inj₂ (u′ , dv) ∷ xs)  = In (u′ , (plug v dv (plug-μ (u ⨂ v) t xs )))
-- \end{code}
-- %</Plug-Mu>

-- %<*First>
-- \begin{code}
--     first : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → Maybe (⟦ ϑ R ⟧ X × X)
--     first 0′ ()
--     first 1′ x = nothing
--     first V x  = just (tt , x)
--     first (u ⨁ v) (inj₁ x) with first u x
--     first (u ⨁ v) (inj₁ x) | just (du , x′) = just (inj₁ du , x′)
--     first (u ⨁ v) (inj₁ x) | nothing        = nothing
--     first (u ⨁ v) (inj₂ y) with first v y
--     first (u ⨁ v) (inj₂ y) | just (x′ , dv) = just (inj₂ x′ , dv)
--     first (u ⨁ v) (inj₂ y) | nothing        = nothing
--     first (u ⨂ v) (u′ , v′) with first u u′
--     first (u ⨂ v) (u′ , v′) | just (du , x) = just (inj₁ (du , v′) , x)
--     first (u ⨂ v) (u′ , v′) | nothing with first v v′
--     first (u ⨂ v) (u′ , v′) | nothing | just (dv , x) = just ((inj₂ (u′ , dv)) , x)
--     first (u ⨂ v) (u′ , v′) | nothing | nothing       = nothing
-- \end{code}
-- %</First>

-- %<*First-Mu>
-- \begin{code}
--     first-μ : (R : Reg) → μ R → Maybe (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
--     first-μ = ∙∙∙
-- \end{code}
-- %</First-Mu>

-- \begin{code}
--       where ∙∙∙ : (R : Reg) → μ R → Maybe (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
--             ∙∙∙ = {!!}
-- \end{code}

-- %<*Right>
-- \begin{code}
--     right : ∀ {X : Set} → (R : Reg) → ⟦ ϑ R ⟧ X × X → (⟦ ϑ R ⟧ X × X) ⊎ (⟦ R ⟧ X)
--     right 0′ (() , _)
--     right 1′ (() , _)
--     right V (tt , x) = inj₂ x
--     right (u ⨁ v) (inj₁ du , x) with right u (du , x)
--     right (u ⨁ v) (inj₁ du , x) | inj₁ (du′ , x′) = inj₁ ((inj₁ du′) , x′)
--     right (u ⨁ v) (inj₁ du , x) | inj₂ u′         = inj₂ (inj₁ u′)
--     right (u ⨁ v) (inj₂ dv , x) with right v (dv , x)
--     right (u ⨁ v) (inj₂ dv , x) | inj₁ (dv′ , x′) = inj₁ ((inj₂ dv′) , x′)
--     right (u ⨁ v) (inj₂ dv , x) | inj₂ v′         = inj₂ (inj₂ v′)
--     right (u ⨂ v) (inj₁ (du , v′) , x) with right u (du , x)
--     right (u ⨂ v) (inj₁ (du , v′) , x) | inj₁ (du′ , x′) = inj₁ ((inj₁ (du′ , v′)) , x′)
--     right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ with first v v′
--     right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ | just (dv , x′′) = inj₁ (inj₂ (u′ , dv) , x′′)
--     right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ | nothing         = inj₂ (u′ , v′)
--     right (u ⨂ v) (inj₂ (u′ , dv) , x) with right v (dv , x)
--     right (u ⨂ v) (inj₂ (u′ , dv) , x) | inj₁ (dv′ , x′) = inj₁ (inj₂ (u′ , dv′) , x′)
--     right (u ⨂ v) (inj₂ (u′ , dv) , x) | inj₂ v′         = inj₂ (u′ , v′)
-- \end{code}
-- %</Right>

-- %<*Right-Mu>
-- \begin{code}
--     right-μ : (R : Reg) → μ R → (List (⟦ ϑ R ⟧ (μ R)) × (μ R)) → (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
--     right-μ = ∙∙∙
-- \end{code}
-- %</Right-Mu>
-- \begin{code}
--       where ∙∙∙ : (R : Reg) → μ R → (List (⟦ ϑ R ⟧ (μ R)) × (μ R)) → (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
--             ∙∙∙ = {!!}
-- \end{code}

-- \begin{code}
--   module Cata where
--     {-# TERMINATING #-}
-- \end{code}
-- %<*Cata-nt>
-- \begin{code}
--     cata : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A → A) → μ R → A
--     cata R ϕ (In x) = ϕ (fmap R (cata R ϕ) x)
-- \end{code}
-- %</Cata-nt>

-- %<*Cata>
-- \begin{code}
--   cata : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A → A) → μ R → A
--   cata  R ϕ (In x) = ϕ (mapFold R R ϕ x)
--     where
--       mapFold : ∀ {a} (Q R : Reg) → (⟦ R ⟧ a → a) → ⟦ Q ⟧ (μ R) → ⟦ Q ⟧ a
--       mapFold 0′ R ϕ ()
--       mapFold 1′ R ϕ tt    = tt
--       mapFold V R ϕ (In x) = ϕ (mapFold R R ϕ x)
--       mapFold (P ⨁ Q)  R ϕ (inj₁ x)  = inj₁ (mapFold P R ϕ x)
--       mapFold (P ⨁ Q)  R ϕ (inj₂ y)  = inj₂ (mapFold Q R ϕ y)
--       mapFold (P ⨂ Q)  R ϕ (x , y)   = mapFold P R ϕ x , mapFold Q R ϕ y
-- \end{code}
-- %</Cata>




-- \begin{code}
--   -- infixr 50 C J
-- \end{code}

-- \begin{code}
--   module Dissection where
--     open import Data.Maybe
-- \end{code}

-- %<*Dissection>
-- \begin{code}
-- \end{code}
-- %</Dissection>
-- %<*R2-first>
-- \begin{code}
--     first : ∀ {X Y : Set} → (R : Reg) → ⟦ R ⟧ X → ⟦ R ⟧ Y ⊎ (⟦ ∇ R ⟧₂ Y X × X)
--     first 0′ ()
--     first 1′ tt = inj₁ tt
--     first V x   = inj₂ (tt , x)
--     first (R ⨁ Q) (inj₁ x) with first R x
--     first (R ⨁ Q) (inj₁ x) | inj₂ (dr , x′)  = inj₂ (inj₁ dr , x′)
--     first (R ⨁ Q) (inj₁ x) | inj₁ em         = inj₁ (inj₁ em)
--     first (R ⨁ Q) (inj₂ y) with first Q y
--     first (R ⨁ Q) (inj₂ y) | inj₂ (dq , y′)  = inj₂ (inj₂ dq , y′)
--     first (R ⨁ Q) (inj₂ y) | inj₁ em         = inj₁ (inj₂ em)
--     first (R ⨂ Q) (r , q) with first R r
--     first (R ⨂ Q) (r , q) | inj₂ (dr , x) = inj₂ ((inj₁ (dr , q)) , x)
--     first (R ⨂ Q) (r , q) | inj₁ em₁ with first Q q
--     first (R ⨂ Q) (r , q) | inj₁ em₁ | inj₂ (dr , x)  = inj₂ (inj₂ (em₁ , dr) , x)
--     first (R ⨂ Q) (r , q) | inj₁ em₁ | inj₁ em₂       = inj₁ (em₁ , em₂)
-- \end{code}
-- %</R2-first>

-- \begin{code}
--     mutual
-- \end{code}
-- %<*R2-right>
-- \begin{code}
--       right : ∀ {c j : Set} (P : Reg)
--             → (⟦ P ⟧ j ⊎ (⟦ ∇ P ⟧₂ c j × c)) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧ c)
--       right = ∙∙∙
-- \end{code}
-- %</R2-right>
-- \begin{code}
--       ∙∙∙ : ∀ {c j : Set} (P : Reg)
--           → (⟦ P ⟧ j ⊎ (⟦ ∇ P ⟧₂ c j × c)) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧ c)

--       ∙∙∙ 0′ (inj₁ ())
--       ∙∙∙ 0′ (inj₂ (() , _))
--       ∙∙∙ 1′ (inj₁ tt) = inj₂ tt
--       ∙∙∙ 1′ (inj₂ (() , _))
--       ∙∙∙ V (inj₁ j)         = inj₁ (j , tt)
--       ∙∙∙ V (inj₂ (tt , c))  = inj₂ c
--       ∙∙∙ (P ⨁ Q) (inj₁ (inj₁ pj)) with ∙∙∙ P (inj₁ pj)
--       ... | inj₁ (j , pd)  = inj₁ (j , inj₁ pd)
--       ... | inj₂ pc        = inj₂ (inj₁ pc)
--       ∙∙∙ (P ⨁ Q) (inj₁ (inj₂ qj)) with ∙∙∙ Q (inj₁ qj)
--       ... | inj₁ (j , qd′)  = inj₁ (j , (inj₂ qd′))
--       ... | inj₂ qc         = inj₂ (inj₂ qc)
--       ∙∙∙ (P ⨁ Q) (inj₂ (inj₁ pd , c))    with ∙∙∙ P (inj₂ (pd , c))
--       ... | inj₁ (j , pd′)  = inj₁ (j , inj₁ pd′)
--       ... | inj₂ pc         = inj₂ (inj₁ pc)
--       ∙∙∙ (P ⨁ Q) (inj₂ (inj₂ qd , c)) with ∙∙∙ Q (inj₂ (qd , c))
--       ... | inj₁ (j , qd′)  = inj₁ (j , (inj₂ qd′))
--       ... | inj₂ qc         = inj₂ (inj₂ qc)

--       ∙∙∙ (P ⨂ Q) (inj₁ (pj , qj)) = goL P Q (∙∙∙ P (inj₁ pj)) qj
--       ∙∙∙ (P ⨂ Q) (inj₂ (inj₁ (pd , qj) , c)) = goL P Q (∙∙∙ P (inj₂ (pd , c))) qj
--       ∙∙∙ (P ⨂ Q) (inj₂ (inj₂ (pc , qd) , c)) = goR P Q pc (∙∙∙ Q (inj₂ (qd , c)))

--       private
--         goL : ∀ {c j : Set} (P Q : Reg) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧ c) → ⟦ Q ⟧ j
--                                           → ((j × ⟦ ∇ (P ⨂ Q) ⟧₂ c j) ⊎ ⟦ P ⨂ Q ⟧ c)
--         goL P Q (inj₁ (j , pd)) qj = inj₁ (j , inj₁ (pd , qj))
--         goL P Q (inj₂ pc)       qj = goR P Q pc (∙∙∙ Q (inj₁ qj))

--         goR : ∀ {c j : Set} (P Q : Reg) → ⟦ P ⟧ c → ((j × ⟦ ∇ Q ⟧₂ c j) ⊎ ⟦ Q ⟧ c)
--                                           → ((j × ⟦ ∇ (P ⨂ Q) ⟧₂ c j) ⊎ ⟦ P ⨂ Q ⟧ c)
--         goR P Q pc (inj₁ (j , qd)) = inj₁ (j , (inj₂ (pc , qd)))
--         goR P Q pc (inj₂ y)        = inj₂ (pc , y)
-- \end{code}

-- \begin{code}
--     {-# TERMINATING #-}
-- \end{code}
-- %<*tcata>
-- \begin{code}
--     tcata : ∀ {A : Set} (F : Reg) → (⟦ F ⟧ A → A) → μ F → A
--     tcata R φ m = load R φ m []
--       where
--         mutual
--           load : ∀ {A : Set} (R : Reg)
--                → (⟦ R ⟧ A → A) → μ R → List (⟦ ∇ R ⟧₂ A (μ R)) → A
--           load R φ (In x) stk = next R φ (right R (inj₁ x)) stk

--           unload : ∀ {A : Set} (R : Reg)
--                  → (⟦ R ⟧ A -> A) → A → List (⟦ ∇ R ⟧₂ A (μ R)) → A
--           unload R φ v []          = v
--           unload R φ v (pd ∷ stk)  = next R φ (right R (inj₂ (pd , v))) stk

--           next : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A → A)
--                → (μ R × ⟦ ∇ R ⟧₂ A (μ R)) ⊎ ⟦ R ⟧ A → List (⟦ ∇ R ⟧₂ A (μ R)) → A
--           next R φ (inj₁ (t , pd)) stk  = load R φ t (pd ∷ stk)
--           next R φ (inj₂ pv) stk        = unload R φ (φ pv) stk

-- \end{code}
-- %</tcata>

-- %<*theorem>
-- \begin{code}
--     theorem : ∀ {A : Set} (F : Reg) → (ϕ : ⟦ F ⟧ A → A) → (x : μ F)
--             → cata F ϕ x ≡ tcata F ϕ x
--     theorem = {!!}
-- \end{code}
-- %</theorem>
