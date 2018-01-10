\begin{code}
module Proposal.Regular where

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
  -- open import Data.Bool
  open import Induction.WellFounded
\end{code}

%<*R>
\begin{code}
  data Reg : Set where
    0′    : Reg
    1′    : Reg
    V     : Reg
    _⨁_  : (r₁ r₂ : Reg) → Reg
    _⨂_  : (r₁ r₂ : Reg) → Reg
\end{code}
%</R>

\begin{code}
  infixl 30 _⨁_
  infixl 40 _⨂_
\end{code}

%<*Interpretation>
\begin{code}
  ⟦_⟧ : Reg → (Set → Set)
  ⟦ 0′ ⟧ X  = ⊥
  ⟦ 1′ ⟧ X  = ⊤
  ⟦ V ⟧  X  = X
  ⟦ F ⨁ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
  ⟦ F ⨂ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X
\end{code}
%</Interpretation>

\begin{code}
  module Example-Bool where
\end{code}

%<*Bool-Ind>
\begin{code}
    data Boolᵢ : Set where
      true false : Boolᵢ
\end{code}
%</Bool-Ind>

\begin{code}
\end{code}

%<*Bool-Reg>
\begin{code}
    Bool′ : Reg
    Bool′ = 1′ ⨁ 1′

    Boolᵣ : Set
    Boolᵣ = ⟦ Bool′ ⟧ ⊤

    trueᵣ : Boolᵣ
    trueᵣ = inj₁ tt

    falseᵣ : Boolᵣ
    falseᵣ = inj₂ tt
\end{code}
%</Bool-Reg>

%<*Bool-from-to>
\begin{code}
    from : Boolᵢ → Boolᵣ
    from true  = trueᵣ
    from false = falseᵣ

    to : Boolᵣ → Boolᵢ
    to (inj₁ tt) = true
    to (inj₂ tt) = false
\end{code}
%</Bool-from-to>

%<*R-Fmap>
\begin{code}
  fmap : ∀ {A B : Set} (R : Reg) → (A → B) → ⟦ R ⟧ A → ⟦ R ⟧ B
  fmap 0′ f ()
  fmap 1′ f tt  = tt
  fmap V f x    = f x
  fmap (R ⨁ Q) f (inj₁ x)  = inj₁ (fmap R f x)
  fmap (R ⨁ Q) f (inj₂ y)  = inj₂ (fmap Q f y)
  fmap (R ⨂ Q) f (x , y)   = (fmap R f x) , (fmap Q f y)

\end{code}
%</R-Fmap>

\begin{code}
  module Maybe-Example where
\end{code}
%<*Maybe-Type>
\begin{code}
    data Maybe (A : Set) : Set where
      just     : A → Maybe A
      nothing  : Maybe A

    Maybe′  : Reg
    Maybe′  = V ⨁ 1′

    just′ : ∀ {A : Set} → A → ⟦ Maybe′ ⟧ A
    just′ x = inj₁ x

    nothing′ : ∀ {A : Set} → ⟦ Maybe′ ⟧ A
    nothing′ = inj₂ tt
\end{code}
%</Maybe-Type>

%<*Maybe-from-to>
\begin{code}
    from : ∀ {A : Set} -> Maybe A → ⟦ Maybe′ ⟧ A
    from (just x)  = just′ x
    from nothing   = nothing′

    to : ∀ {A : Set} -> ⟦ Maybe′ ⟧ A → Maybe A
    to (inj₁ x)   = just x
    to (inj₂ tt)  = nothing
\end{code}
%</Maybe-from-to>

%<*Mu>
\begin{code}
  data μ (R : Reg) : Set where
    In : ⟦ R ⟧ (μ R) → μ R
\end{code}
%</Mu>

\begin{code}
  module Nat-Example where
\end{code}

%<*Nat-Ind>
\begin{code}
    data Nat : Set where
      zero : Nat
      suc  : Nat → Nat
\end{code}
%</Nat-Ind>

%<*Nat-Reg>
\begin{code}
    Nat′  : Set
    Nat′  = μ (V ⨁ 1′)

    zero′  : Nat′
    zero′ = In (inj₂ tt)

    suc′  : Nat′ → Nat′
    suc′ n = In (inj₁ n)
\end{code}
%</Nat-Reg>

%<*Nat-from-to>
\begin{code}
    from : Nat → Nat′
    from zero     = zero′
    from (suc x)  = suc′ (from x)

    to : Nat′ → Nat
    to (In (inj₁ x))   = suc (to x)
    to (In (inj₂ tt))  = zero
\end{code}
%</Nat-from-to>

\begin{code}
  module Differentiation where
    open import Data.Maybe
\end{code}
  %<*Differentiation>
  \begin{code}
    ϑ : Reg → Reg
    ϑ 0′  = 0′
    ϑ 1′  = 0′
    ϑ V   = 1′
    ϑ (f ⨁ g) = ϑ f ⨁ ϑ g
    ϑ (f ⨂ g) = ϑ f ⨂ g ⨁ f ⨂ ϑ g
  \end{code}
  %</Differentiation>

%<*Plug>
\begin{code}
    plug : ∀ {X : Set} → (R : Reg) → ⟦ ϑ R ⟧ X → X → ⟦ R ⟧ X
    plug 0′ () x
    plug 1′ () x
    plug V tt x = x
    plug (u ⨁ v) (inj₁ u′) x  = inj₁ (plug u u′ x)
    plug (u ⨁ v) (inj₂ v′) x  = inj₂ (plug v v′ x)
    plug (u ⨂ v) (inj₁ (du , v′)) x = plug u du x  , v′
    plug (u ⨂ v) (inj₂ (u′ , dv)) x = u′           , plug v dv x
\end{code}
%</Plug>


%<*Plug-Mu>
\begin{code}
    plug-μ : ∀ (R : Reg) → μ R → List (⟦ ϑ R ⟧ (μ R)) → μ R
    plug-μ u t []         = t
    plug-μ 0′ t (() ∷ xs)
    plug-μ 1′ t (() ∷ xs)
    plug-μ V t (tt ∷ xs)  = t
    plug-μ (u ⨁ v) t (inj₁ du ∷ xs)         = In (inj₁ (plug u du (plug-μ (u ⨁ v) t xs)))
    plug-μ (u ⨁ v) t (inj₂ dv ∷ xs)         = In (inj₂ (plug v dv (plug-μ (u ⨁ v) t xs)))
    plug-μ (u ⨂ v) t (inj₁ (du , v′) ∷ xs)  = In ((plug u du (plug-μ (u ⨂ v) t xs)) , v′)
    plug-μ (u ⨂ v) t (inj₂ (u′ , dv) ∷ xs)  = In (u′ , (plug v dv (plug-μ (u ⨂ v) t xs )))
\end{code}
%</Plug-Mu>

%<*First>
\begin{code}
    first : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → Maybe (⟦ ϑ R ⟧ X × X)
    first 0′ ()
    first 1′ x = nothing
    first V x  = just (tt , x)
    first (u ⨁ v) (inj₁ x) with first u x
    first (u ⨁ v) (inj₁ x) | just (du , x′) = just (inj₁ du , x′)
    first (u ⨁ v) (inj₁ x) | nothing        = nothing
    first (u ⨁ v) (inj₂ y) with first v y
    first (u ⨁ v) (inj₂ y) | just (x′ , dv) = just (inj₂ x′ , dv)
    first (u ⨁ v) (inj₂ y) | nothing        = nothing
    first (u ⨂ v) (u′ , v′) with first u u′
    first (u ⨂ v) (u′ , v′) | just (du , x) = just (inj₁ (du , v′) , x)
    first (u ⨂ v) (u′ , v′) | nothing with first v v′
    first (u ⨂ v) (u′ , v′) | nothing | just (dv , x) = just ((inj₂ (u′ , dv)) , x)
    first (u ⨂ v) (u′ , v′) | nothing | nothing       = nothing
\end{code}
%</First>

%<*First-Mu>
\begin{code}
    first-μ : (R : Reg) → μ R → Maybe (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
    first-μ = ∙∙∙
\end{code}
%</First-Mu>

\begin{code}
      where ∙∙∙ : (R : Reg) → μ R → Maybe (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
            ∙∙∙ = {!!}
\end{code}

%<*Right>
\begin{code}
    right : ∀ {X : Set} → (R : Reg) → ⟦ ϑ R ⟧ X × X → (⟦ ϑ R ⟧ X × X) ⊎ (⟦ R ⟧ X)
    right 0′ (() , _)
    right 1′ (() , _)
    right V (tt , x) = inj₂ x
    right (u ⨁ v) (inj₁ du , x) with right u (du , x)
    right (u ⨁ v) (inj₁ du , x) | inj₁ (du′ , x′) = inj₁ ((inj₁ du′) , x′)
    right (u ⨁ v) (inj₁ du , x) | inj₂ u′         = inj₂ (inj₁ u′)
    right (u ⨁ v) (inj₂ dv , x) with right v (dv , x)
    right (u ⨁ v) (inj₂ dv , x) | inj₁ (dv′ , x′) = inj₁ ((inj₂ dv′) , x′)
    right (u ⨁ v) (inj₂ dv , x) | inj₂ v′         = inj₂ (inj₂ v′)
    right (u ⨂ v) (inj₁ (du , v′) , x) with right u (du , x)
    right (u ⨂ v) (inj₁ (du , v′) , x) | inj₁ (du′ , x′) = inj₁ ((inj₁ (du′ , v′)) , x′)
    right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ with first v v′
    right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ | just (dv , x′′) = inj₁ (inj₂ (u′ , dv) , x′′)
    right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ | nothing         = inj₂ (u′ , v′)
    right (u ⨂ v) (inj₂ (u′ , dv) , x) with right v (dv , x)
    right (u ⨂ v) (inj₂ (u′ , dv) , x) | inj₁ (dv′ , x′) = inj₁ (inj₂ (u′ , dv′) , x′)
    right (u ⨂ v) (inj₂ (u′ , dv) , x) | inj₂ v′         = inj₂ (u′ , v′)
\end{code}
%</Right>

%<*Right-Mu>
\begin{code}
    right-μ : (R : Reg) → μ R → (List (⟦ ϑ R ⟧ (μ R)) × (μ R)) → (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
    right-μ = ∙∙∙
\end{code}
%</Right-Mu>
\begin{code}
      where ∙∙∙ : (R : Reg) → μ R → (List (⟦ ϑ R ⟧ (μ R)) × (μ R)) → (List (⟦ ϑ R ⟧ (μ R)) × (μ R))
            ∙∙∙ = {!!}
\end{code}

\begin{code}
  module Cata where
    {-# TERMINATING #-}
\end{code}
%<*Cata-nt>
\begin{code}
    cata : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A → A) → μ R → A
    cata R ϕ (In x) = ϕ (fmap R (cata R ϕ) x)
\end{code}
%</Cata-nt>

%<*Cata>
\begin{code}
  cata : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A → A) → μ R → A
  cata  R ϕ (In x) = ϕ (mapFold R R ϕ x)
    where
      mapFold : ∀ {a} (Q R : Reg) → (⟦ R ⟧ a → a) → ⟦ Q ⟧ (μ R) → ⟦ Q ⟧ a
      mapFold 0′ R ϕ ()
      mapFold 1′ R ϕ tt    = tt
      mapFold V R ϕ (In x) = ϕ (mapFold R R ϕ x)
      mapFold (P ⨁ Q)  R ϕ (inj₁ x)  = inj₁ (mapFold P R ϕ x)
      mapFold (P ⨁ Q)  R ϕ (inj₂ y)  = inj₂ (mapFold Q R ϕ y)
      mapFold (P ⨂ Q)  R ϕ (x , y)   = mapFold P R ϕ x , mapFold Q R ϕ y
\end{code}
%</Cata>

%<*R2>
\begin{code}
  data Reg₂ : Set where
    0′   :  Reg₂
    1′   :  Reg₂
    F    :  Reg₂
    S    :  Reg₂
    C    :  Reg → Reg₂
    J    :  Reg → Reg₂
    _⨁_  : (P Q : Reg₂)  → Reg₂
    _⨂_  : (P Q : Reg₂)  → Reg₂
\end{code}
%</R2>

%<*R2-Interpretation>
\begin{code}
  ⟦_⟧₂ : Reg₂ → (Set → Set → Set)
  ⟦ 0′  ⟧₂ X Y = ⊥
  ⟦ 1′  ⟧₂ X Y = ⊤
  ⟦ F   ⟧₂ X Y = X
  ⟦ S   ⟧₂ X Y = Y
  ⟦ C R ⟧₂ X Y  = ⟦ R ⟧ X
  ⟦ J R ⟧₂ X Y  = ⟦ R ⟧ Y
  ⟦ R ⨁ Q ⟧₂ X Y = ⟦ R ⟧₂ X Y ⊎ ⟦ Q ⟧₂ X Y
  ⟦ R ⨂ Q ⟧₂ X Y = ⟦ R ⟧₂ X Y × ⟦ Q ⟧₂ X Y
\end{code}
%</R2-Interpretation>

\begin{code}
  -- infixr 50 C J
\end{code}

\begin{code}
  module Dissection where
    open import Data.Maybe
\end{code}

%<*Dissection>
\begin{code}
    ∇ : Reg → Reg₂
    ∇ 0′ = 0′
    ∇ 1′ = 0′
    ∇ V  = 1′
    ∇ (R ⨁ Q) = ∇ R ⨁ ∇ Q
    ∇ (R ⨂ Q) = (∇ R ⨂ J Q) ⨁ (C R ⨂ ∇ Q)
\end{code}
%</Dissection>
%<*R2-first>
\begin{code}
    first : ∀ {X Y : Set} → (R : Reg) → ⟦ R ⟧ X → ⟦ R ⟧ Y ⊎ (⟦ ∇ R ⟧₂ Y X × X)
    first 0′ ()
    first 1′ tt = inj₁ tt
    first V x   = inj₂ (tt , x)
    first (R ⨁ Q) (inj₁ x) with first R x
    first (R ⨁ Q) (inj₁ x) | inj₂ (dr , x′)  = inj₂ (inj₁ dr , x′)
    first (R ⨁ Q) (inj₁ x) | inj₁ em         = inj₁ (inj₁ em)
    first (R ⨁ Q) (inj₂ y) with first Q y
    first (R ⨁ Q) (inj₂ y) | inj₂ (dq , y′)  = inj₂ (inj₂ dq , y′)
    first (R ⨁ Q) (inj₂ y) | inj₁ em         = inj₁ (inj₂ em)
    first (R ⨂ Q) (r , q) with first R r
    first (R ⨂ Q) (r , q) | inj₂ (dr , x) = inj₂ ((inj₁ (dr , q)) , x)
    first (R ⨂ Q) (r , q) | inj₁ em₁ with first Q q
    first (R ⨂ Q) (r , q) | inj₁ em₁ | inj₂ (dr , x)  = inj₂ (inj₂ (em₁ , dr) , x)
    first (R ⨂ Q) (r , q) | inj₁ em₁ | inj₁ em₂       = inj₁ (em₁ , em₂)
\end{code}
%</R2-first>

\begin{code}
    mutual
\end{code}
%<*R2-right>
\begin{code}
      right : ∀ {c j : Set} (P : Reg)
            → (⟦ P ⟧ j ⊎ (⟦ ∇ P ⟧₂ c j × c)) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧ c)
      right = ∙∙∙
\end{code}
%</R2-right>
\begin{code}
      ∙∙∙ : ∀ {c j : Set} (P : Reg)
          → (⟦ P ⟧ j ⊎ (⟦ ∇ P ⟧₂ c j × c)) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧ c)

      ∙∙∙ 0′ (inj₁ ())
      ∙∙∙ 0′ (inj₂ (() , _))
      ∙∙∙ 1′ (inj₁ tt) = inj₂ tt
      ∙∙∙ 1′ (inj₂ (() , _))
      ∙∙∙ V (inj₁ j)         = inj₁ (j , tt)
      ∙∙∙ V (inj₂ (tt , c))  = inj₂ c
      ∙∙∙ (P ⨁ Q) (inj₁ (inj₁ pj)) with ∙∙∙ P (inj₁ pj)
      ... | inj₁ (j , pd)  = inj₁ (j , inj₁ pd)
      ... | inj₂ pc        = inj₂ (inj₁ pc)
      ∙∙∙ (P ⨁ Q) (inj₁ (inj₂ qj)) with ∙∙∙ Q (inj₁ qj)
      ... | inj₁ (j , qd′)  = inj₁ (j , (inj₂ qd′))
      ... | inj₂ qc         = inj₂ (inj₂ qc)
      ∙∙∙ (P ⨁ Q) (inj₂ (inj₁ pd , c))    with ∙∙∙ P (inj₂ (pd , c))
      ... | inj₁ (j , pd′)  = inj₁ (j , inj₁ pd′)
      ... | inj₂ pc         = inj₂ (inj₁ pc)
      ∙∙∙ (P ⨁ Q) (inj₂ (inj₂ qd , c)) with ∙∙∙ Q (inj₂ (qd , c))
      ... | inj₁ (j , qd′)  = inj₁ (j , (inj₂ qd′))
      ... | inj₂ qc         = inj₂ (inj₂ qc)

      ∙∙∙ (P ⨂ Q) (inj₁ (pj , qj)) = goL P Q (∙∙∙ P (inj₁ pj)) qj
      ∙∙∙ (P ⨂ Q) (inj₂ (inj₁ (pd , qj) , c)) = goL P Q (∙∙∙ P (inj₂ (pd , c))) qj
      ∙∙∙ (P ⨂ Q) (inj₂ (inj₂ (pc , qd) , c)) = goR P Q pc (∙∙∙ Q (inj₂ (qd , c)))

      private
        goL : ∀ {c j : Set} (P Q : Reg) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧ c) → ⟦ Q ⟧ j
                                          → ((j × ⟦ ∇ (P ⨂ Q) ⟧₂ c j) ⊎ ⟦ P ⨂ Q ⟧ c)
        goL P Q (inj₁ (j , pd)) qj = inj₁ (j , inj₁ (pd , qj))
        goL P Q (inj₂ pc)       qj = goR P Q pc (∙∙∙ Q (inj₁ qj))

        goR : ∀ {c j : Set} (P Q : Reg) → ⟦ P ⟧ c → ((j × ⟦ ∇ Q ⟧₂ c j) ⊎ ⟦ Q ⟧ c)
                                          → ((j × ⟦ ∇ (P ⨂ Q) ⟧₂ c j) ⊎ ⟦ P ⨂ Q ⟧ c)
        goR P Q pc (inj₁ (j , qd)) = inj₁ (j , (inj₂ (pc , qd)))
        goR P Q pc (inj₂ y)        = inj₂ (pc , y)
\end{code}

\begin{code}
    {-# TERMINATING #-}
\end{code}
%<*tcata>
\begin{code}
    tcata : ∀ {A : Set} (F : Reg) → (⟦ F ⟧ A → A) → μ F → A
    tcata R φ m = load R φ m []
      where
        mutual
          load : ∀ {A : Set} (R : Reg)
               → (⟦ R ⟧ A → A) → μ R → List (⟦ ∇ R ⟧₂ A (μ R)) → A
          load R φ (In x) stk = next R φ (right R (inj₁ x)) stk

          unload : ∀ {A : Set} (R : Reg)
                 → (⟦ R ⟧ A -> A) → A → List (⟦ ∇ R ⟧₂ A (μ R)) → A
          unload R φ v []          = v
          unload R φ v (pd ∷ stk)  = next R φ (right R (inj₂ (pd , v))) stk

          next : ∀ {A : Set} (R : Reg) → (⟦ R ⟧ A → A)
               → (μ R × ⟦ ∇ R ⟧₂ A (μ R)) ⊎ ⟦ R ⟧ A → List (⟦ ∇ R ⟧₂ A (μ R)) → A
          next R φ (inj₁ (t , pd)) stk  = load R φ t (pd ∷ stk)
          next R φ (inj₂ pv) stk        = unload R φ (φ pv) stk

\end{code}
%</tcata>

%<*theorem>
\begin{code}
    theorem : ∀ {A : Set} (F : Reg) → (ϕ : ⟦ F ⟧ A → A) → (x : μ F)
            → cata F ϕ x ≡ tcata F ϕ x
    theorem = {!!}
\end{code}
%</theorem>
