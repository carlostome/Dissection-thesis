\begin{code}
module Thesis.Regular where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
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

  -- for this we need decidable equality on the underlying type
  ⟦Reg⟧-dec : ∀ {X : Set} (R : Reg) (x y : ⟦ R ⟧ X) → Dec (x ≡ y)
  ⟦Reg⟧-dec 0′ x y = {!!}
  ⟦Reg⟧-dec 1′ x y = {!!}
  ⟦Reg⟧-dec V x y = {!!}
  ⟦Reg⟧-dec (R ⨁ R₁) x y = {!!}
  ⟦Reg⟧-dec (R ⨂ R₁) x y = {!!}
  
  fmap : ∀ {A B : Set} (R : Reg) → (A → B) → ⟦ R ⟧ A → ⟦ R ⟧ B
  fmap 0′ f ()
  fmap 1′ f tt  = tt
  fmap V f x    = f x
  fmap (R ⨁ Q) f (inj₁ x)  = inj₁ (fmap R f x)
  fmap (R ⨁ Q) f (inj₂ y)  = inj₂ (fmap Q f y)
  fmap (R ⨂ Q) f (x , y)   = (fmap R f x) , (fmap Q f y)

  data μ (R : Reg) : Set where
    In : ⟦ R ⟧ (μ R) → μ R

  In-injective : ∀ {R : Reg} {x y} → (μ R ∋ In x) ≡ In y → x ≡ y
  In-injective refl = refl

  ϑ : Reg → Reg
  ϑ 0′  = 0′
  ϑ 1′  = 0′
  ϑ V   = 1′
  ϑ (f ⨁ g) = ϑ f ⨁ ϑ g
  ϑ (f ⨂ g) = ϑ f ⨂ g ⨁ f ⨂ ϑ g


  data Reg₂ : Set where
    0′   :  Reg₂
    1′   :  Reg₂
    F    :  Reg₂
    S    :  Reg₂
    C    :  Reg → Reg₂
    J    :  Reg → Reg₂
    _⨁_  : (P Q : Reg₂)  → Reg₂
    _⨂_  : (P Q : Reg₂)  → Reg₂

  Reg₂-dec : ∀ (x y : Reg₂) → Dec (x ≡ y)
  Reg₂-dec 0′ 0′ = yes refl
  Reg₂-dec 0′ 1′ = no (λ ())
  Reg₂-dec 0′ F = no (λ ())
  Reg₂-dec 0′ S = no (λ ())
  Reg₂-dec 0′ (C x) = no (λ ())
  Reg₂-dec 0′ (J x) = no (λ ())
  Reg₂-dec 0′ (y ⨁ y₁) = no (λ ())
  Reg₂-dec 0′ (y ⨂ y₁) = no (λ ())
  Reg₂-dec 1′ y = {!!}
  Reg₂-dec F y = {!!}
  Reg₂-dec S y = {!!}
  Reg₂-dec (C x) y = {!!}
  Reg₂-dec (J x) y = {!!}
  Reg₂-dec (x ⨁ x₁) y = {!!}
  Reg₂-dec (x ⨂ x₁) y = {!!}
  
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
  Rel₂ (R ⨁ Q) (inj₂ x) (inj₂ y)  = Rel₂ Q x y
  Rel₂ (R ⨂ Q) (dr , q) (r , dq) = {!!}

  data Tree₂-₃ : Set where
    tris  : Tree₂-₃ → Tree₂-₃ → Tree₂-₃ → Tree₂-₃
    bi   : Tree₂-₃ → Tree₂-₃ → Tree₂-₃
    leaf : Tree₂-₃

  Zipper : Reg → Set
  Zipper R = μ R × List (⟦ ∇ R ⟧₂ (μ R) (μ R))

  plug : ∀ {X : Set} → (R : Reg) → ⟦ ∇ R ⟧₂ X X → X → ⟦ R ⟧ X
  plug 0′ () x
  plug 1′ () x
  plug V tt x = x
  plug (u ⨁ v) (inj₁ u′) x  = inj₁ (plug u u′ x)
  plug (u ⨁ v) (inj₂ v′) x  = inj₂ (plug v v′ x)
  plug (u ⨂ v) (inj₁ (du , v′)) x = plug u du x  , v′
  plug (u ⨂ v) (inj₂ (u′ , dv)) x = u′           , plug v dv x

  ⊎-injective₁ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  ⊎-injective₁ refl = refl

  ⊎-injective₂ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  ⊎-injective₂ refl = refl

  ⊎-injective₁-inv : ∀ {A B : Set} {x y} → x ≡ y → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y
  ⊎-injective₁-inv refl = refl

  ⊎-injective₂-inv : ∀ {A B : Set} {x y} → x ≡ y → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y
  ⊎-injective₂-inv refl = refl
 
  ×-injective : ∀ {A B : Set} {x y a b} → (A × B ∋ (x , y)) ≡ (a , b) → x ≡ a × y ≡ b
  ×-injective refl = refl , refl

  plug-injective : ∀ {X : Set} → (R : Reg)
                 → (r : ⟦ ∇ R ⟧₂ X X) → (x y : X) → plug R r x ≡ plug R r y → x ≡ y
  plug-injective 0′ () x y p
  plug-injective 1′ () x y p
  plug-injective V r x .x refl = refl
  plug-injective (R ⨁ Q) (inj₁ x₁) x y p = plug-injective R x₁ x y (⊎-injective₁ p)
  plug-injective (R ⨁ Q) (inj₂ y₁) x y p = plug-injective Q y₁ x y (⊎-injective₂ p)
  plug-injective (R ⨂ Q) (inj₁ (a , b)) x y p  = plug-injective R a x y (proj₁ (×-injective p))
  plug-injective (R ⨂ Q) (inj₂ (a , b)) x y p  = plug-injective Q b x y (proj₂ (×-injective p))

  -- plug is not injective in both arguments
  plug-injective₂ : ∀ {X : Set} → (R : Reg)
                 → (r q : ⟦ ∇ R ⟧₂ X X) → (x y : X) → plug R r x ≡ plug R q y → x ≡ y × r ≡ q
  plug-injective₂ 0′ () q x y p
  plug-injective₂ 1′ () q x y p
  plug-injective₂ V tt tt x .x refl = refl , refl
  plug-injective₂ (R ⨁ Q) (inj₁ x₁) (inj₁ x₂) x y p with plug-injective₂ R x₁ x₂ x y (⊎-injective₁ p)
  plug-injective₂ (R ⨁ Q) (inj₁ x₁) (inj₁ .x₁) x .x p | refl , refl = refl , refl
  plug-injective₂ (R ⨁ Q) (inj₁ x₁) (inj₂ y₁) x y ()
  plug-injective₂ (R ⨁ Q) (inj₂ y₁) (inj₁ x₁) x y ()
  plug-injective₂ (R ⨁ Q) (inj₂ y₁) (inj₂ y₂) x y p with plug-injective₂ Q y₁ y₂ x y (⊎-injective₂ p)
  plug-injective₂ (R ⨁ Q) (inj₂ y₁) (inj₂ .y₁) x .x p | refl , refl = refl , refl
  plug-injective₂ (R ⨂ Q) (inj₁ (proj₃ , proj₄)) (inj₁ (proj₅ , proj₆)) x y p = {!!}
  plug-injective₂ (R ⨂ Q) (inj₁ (proj₃ , .(plug Q proj₆ y))) (inj₂ (.(plug R proj₃ x) , proj₆)) x y refl = {!!}
  plug-injective₂ (R ⨂ Q) (inj₂ y₁) q x y p = {!!}

  plug-μ : ∀ (R : Reg) → μ R → List (⟦ ∇ R ⟧₂ (μ R) (μ R)) → μ R
  plug-μ u t []         = t
  plug-μ 0′ t (() ∷ xs)
  plug-μ 1′ t (() ∷ xs)
  plug-μ V t (tt ∷ xs)  = t
  plug-μ (u ⨁ v) t (inj₁ du ∷ xs)         = In (inj₁ (plug u du (plug-μ (u ⨁ v) t xs)))
  plug-μ (u ⨁ v) t (inj₂ dv ∷ xs)         = In (inj₂ (plug v dv (plug-μ (u ⨁ v) t xs)))
  plug-μ (u ⨂ v) t (inj₁ (du , v′) ∷ xs)  = In (plug u du (plug-μ (u ⨂ v) t xs) , v′)
  plug-μ (u ⨂ v) t (inj₂ (u′ , dv) ∷ xs)  = In (u′ , (plug v dv (plug-μ (u ⨂ v) t xs)))

  plug-⊳ : (R : Reg) → Zipper R → μ R
  plug-⊳ R (t , s) = plug-μ R t s

-- the good one

  data IsInj₂ {X Y : Set} : (R : Reg) → ⟦ ∇ R ⟧₂ X Y → Set where
    isInj₂-⨁-inj₁ : ∀ (R Q : Reg) x → IsInj₂ R x → IsInj₂ (R ⨁ Q) (inj₁ x) 
    isInj₂-⨁-inj₂ : ∀ (R Q : Reg) y → IsInj₂ Q y → IsInj₂ (R ⨁ Q) (inj₂ y)
    isInj₂-⨂      : ∀ (R Q : Reg) x → IsInj₂ (R ⨂ Q) (inj₂ x)

  -- By construction now the relation makes sure that they plug onto the same
  -- value. It gives an order between the possible templates from a Code.
  data nltReg {X : Set} : (R : Reg) → (⟦ ∇ R ⟧₂ X X × X) → (⟦ ∇ R ⟧₂ X X × X) → Set where
    step-⨂-inj₁ : ∀ {R Q} {dr dr′ q q′} {t₁ t₂}
                 → q ≡ q′
                 → nltReg R (dr , t₁) (dr′ , t₂)             
                 → nltReg  ( R ⨂ Q ) (inj₁ (dr , q) , t₁) (inj₁ (dr′ , q′) , t₂)

    step-⨂-inj₂ : ∀ {R Q} {dq dq′ r r′} {t₁ t₂}
                 → r ≡ r′
                 → nltReg Q (dq , t₁) (dq′ , t₂)
                 → nltReg ( R ⨂ Q ) (inj₂ (r , dq) , t₁) (inj₂ (r′ , dq′) , t₂)

    base-⨂      : ∀ {R Q : Reg} {x y} {t₁ t₂}
                 → plug (R ⨂ Q) (inj₂ x) t₁ ≡ plug (R ⨂ Q) (inj₁ y) t₂
                 → nltReg (R ⨂ Q) (inj₂ x , t₁) (inj₁ y , t₂)

    step-⨁-inj₂ : ∀ {R Q} {x y} {t₁ t₂}
                 → nltReg Q (x , t₁) (y , t₂)
                 → nltReg (R ⨁ Q) (inj₂ x , t₁) (inj₂ y , t₂)

    step-⨁-inj₁ : ∀ {R Q} {x y} {t₁ t₂}
                 → nltReg R (x , t₁) (y , t₂)
                 → nltReg (R ⨁ Q) (inj₁ x , t₁) (inj₁ y , t₂)

  -- this relation embodies equality and ordering with respect to the diff r code
  data IsInj₁ {X Y : Set} : (R : Reg) → ⟦ ∇ R ⟧₂ X Y → Set where
    isInj₁-⨁-inj₁ : ∀ (R Q : Reg) x → IsInj₁ R x → IsInj₁ (R ⨁ Q) (inj₁ x) 
    isInj₁-⨁-inj₂ : ∀ (R Q : Reg) y → IsInj₁ Q y → IsInj₁ (R ⨁ Q) (inj₂ y)
    isInj₁-⨂      : ∀ (R Q : Reg) x → IsInj₁ (R ⨂ Q) (inj₁ x)

  nltReg-related : ∀ {X : Set} (R : Reg) → (x y : ⟦ ∇ R ⟧₂ X X) → (t₁ t₂ : X)
                 → nltReg R (x , t₁) (y , t₂) → plug R x t₁ ≡ plug R y t₂
  nltReg-related .(_ ⨂ _) .(inj₁ (_ , _)) .(inj₁ (_ , _)) t₁ t₂ (step-⨂-inj₁ refl p) = cong (_, _)  (nltReg-related _ _ _ t₁ t₂ p)
  nltReg-related .(_ ⨂ _) .(inj₂ (_ , _)) .(inj₂ (_ , _)) t₁ t₂ (step-⨂-inj₂ refl p) = cong (_,_ _) (nltReg-related _ _ _ t₁ t₂ p)
  nltReg-related .(_ ⨂ _) .(inj₂ _) .(inj₁ _) t₁ t₂ (base-⨂ p) = p
  nltReg-related .(_ ⨁ _) .(inj₂ _) .(inj₂ _) t₁ t₂ (step-⨁-inj₂ p) = ⊎-injective₂-inv (nltReg-related _ _ _ t₁ t₂ p)
  nltReg-related .(_ ⨁ _) .(inj₁ _) .(inj₁ _) t₁ t₂ (step-⨁-inj₁ p) = ⊎-injective₁-inv (nltReg-related _ _ _ t₁ t₂ p)

  nltReg-WF : ∀ {X : Set} (R : Reg) → Well-founded (nltReg {X} R)
  nltReg-WF R x = acc (aux R x)
    where aux : ∀ {X} (R : Reg) (x : Σ (⟦ ∇ R ⟧₂ X X) (λ x₁ → X))
                  (y : Σ (⟦ ∇ R ⟧₂ X X) (λ x₁ → X)) → nltReg R y x → Acc (nltReg R) y
          aux .(R ⨂ Q) (.(inj₁ (dr′ , q)) , x) (.(inj₁ (dr , q)) , y) (step-⨂-inj₁ {R} {Q} {dr} {dr′} {q} refl p) = {!!}
          aux .(_ ⨂ _) (.(inj₂ (_ , _)) , x) (.(inj₂ (_ , _)) , y) (step-⨂-inj₂ x₂ p) = {!!}
          aux .(_ ⨂ _) (.(inj₁ _) , x) (.(inj₂ _) , y) (base-⨂ x₃) = {!!}
          aux .(_ ⨁ _) (.(inj₂ _) , x) (.(inj₂ _) , y) (step-⨁-inj₂ p) = {!!}
          aux .(_ ⨁ _) (.(inj₁ _) , x) (.(inj₁ _) , y) (step-⨁-inj₁ p) = {!!}
          
  -- A reification as an inductive type of the plug function
  data Plug {X : Set} : (R : Reg) → (⟦ ∇ R ⟧₂ X X × X) → ⟦ R ⟧ X → Set where
    step-⨁-inj₁ : ∀ {R Q} {x y} {t}
                 → Plug R (x , t) y            
                 → Plug (R ⨁ Q) (inj₁ x , t) (inj₁ y)

    step-⨁-inj₂ : ∀ {R Q} {x y} {t}
                 → Plug Q (x , t) y            
                 → Plug (R ⨁ Q) (inj₂ x , t) (inj₂ y)

    step-⨂-inj₁ : ∀ {R Q} {r dr q q′} {t}
                 → q ≡ q′
                 → Plug R (dr , t) r
                 → Plug (R ⨂ Q) (inj₁ (dr , q′) , t) (r , q)

    step-⨂-inj₂ : ∀ {R Q} {r r′ q dq} {t}
                 → r ≡ r′
                 → Plug Q (dq , t) q
                 → Plug (R ⨂ Q) (inj₂ (r′ , dq) , t) (r , q)

    base         : ∀ {y} {t} → t ≡ y → Plug V (tt , t) y

  plugView : ∀ {X : Set} (R : Reg) → (x : ⟦ ∇ R ⟧₂ X X) → (t : X) → (y : ⟦ R ⟧ X) →
            plug R x t ≡ y → Plug R (x , t) y
  plugView 0′ () t y p
  plugView 1′ () t y p
  plugView V tt t .t refl = base refl
  plugView (R ⨁ Q) (inj₁ x) t (inj₁ x₁) p = step-⨁-inj₁ (plugView R x t x₁ (⊎-injective₁ p))
  plugView (R ⨁ Q) (inj₁ x) t (inj₂ y) ()
  plugView (R ⨁ Q) (inj₂ y₁) t (inj₁ x) ()
  plugView (R ⨁ Q) (inj₂ y₁) t (inj₂ y) p = step-⨁-inj₂ (plugView Q y₁ t y (⊎-injective₂ p))
  plugView (R ⨂ Q) (inj₁ (r , dq)) t (pr , dq′) p = step-⨂-inj₁ (sym (proj₂ (×-injective p))) (plugView R r t pr (proj₁ (×-injective p)))
  plugView (R ⨂ Q) (inj₂ (dr , q)) t (dr′ , pq) p = step-⨂-inj₂ (sym (proj₁ (×-injective p))) (plugView Q q t pq (proj₂ (×-injective p)))

  Plug-related : ∀ {X : Set} (R : Reg) → (x : ⟦ ∇ R ⟧₂ X X) → (t : X) → (y : ⟦ R ⟧ X)
               → Plug R (x , t) y → plug R x t ≡ y
  Plug-related .(_ ⨁ _) .(inj₁ _) t .(inj₁ _) (step-⨁-inj₁ p) = ⊎-injective₁-inv (Plug-related _ _ t _ p)
  Plug-related .(_ ⨁ _) .(inj₂ _) t .(inj₂ _) (step-⨁-inj₂ p) = ⊎-injective₂-inv (Plug-related _ _ t _ p)
  Plug-related .(_ ⨂ _) .(inj₁ (_ , q′)) t .(_ , q′) (step-⨂-inj₁ {q′ = q′} refl p) = cong (_, q′) (Plug-related _ _ t _ p)
  Plug-related .(_ ⨂ _) .(inj₂ (r′ , _)) t .(r′ , _) (step-⨂-inj₂ {r′ = r′} refl p) = cong (_,_ r′) (Plug-related _ _  t _ p) 
  Plug-related .V .tt t y (base x) = x


  first : ∀ {X Y : Set} → (R : Reg) → ⟦ R ⟧ X → (⟦ R ⟧ Y ⊎ (⟦ ∇ R ⟧₂ Y X × X))
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

  mutual
    first-μ : ∀ {X : Set} → (R : Reg) → μ R → List (⟦ ∇ R ⟧₂ X (μ R)) → (List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X)
    first-μ {X} R (In x) xs = first-cp R x {!cont-first xs!} 

    cont-first : ∀ {X : Set} (R : Reg) → List (⟦ ∇ R ⟧₂ X (μ R)) → ⟦ R ⟧ X ⊎ (⟦ ∇ R ⟧₂ X (μ R) × μ R) → List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X
    cont-first R xs (inj₁ x)       = xs , x
    cont-first R xs (inj₂ (y , x)) = first-μ R x (y ∷ xs)
    
    first-cp : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ (μ R) → (⟦ R ⟧ X ⊎ (⟦ ∇ R ⟧₂ X (μ R) × μ R) → List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X) → List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X 
    first-cp R x₁ x₂ = {!!}
    -- aux 0′ ()
      -- aux 1′ tt = inj₁ tt
      -- aux V x   = ?
      
      -- aux (R ⨁ Q) (inj₁ x) with aux R x
      -- aux (R ⨁ Q) (inj₁ x) | inj₂ (dr , x′)  = inj₂ (inj₁ dr , x′)
      -- aux (R ⨁ Q) (inj₁ x) | inj₁ em         = inj₁ (inj₁ em)
      -- aux (R ⨁ Q) (inj₂ y) with aux Q y
      -- aux (R ⨁ Q) (inj₂ y) | inj₂ (dq , y′)  = inj₂ (inj₂ dq , y′)
      -- aux (R ⨁ Q) (inj₂ y) | inj₁ em         = inj₁ (inj₂ em)
      -- aux (R ⨂ Q) (r , q) with aux R r
      -- aux (R ⨂ Q) (r , q) | inj₂ (dr , x) = inj₂ ((inj₁ (dr , q)) , x)
      -- aux (R ⨂ Q) (r , q) | inj₁ em₁ with aux Q q
      -- aux (R ⨂ Q) (r , q) | inj₁ em₁ | inj₂ (dr , x)  = inj₂ (inj₂ (em₁ , dr) , x)
      -- aux (R ⨂ Q) (r , q) | inj₁ em₁ | inj₁ em₂       = inj₁ (em₁ , em₂)

  {- I don't like to use maybe for the case where the value is a leaf of
     the tree. We should be able to express the fact on the type level -}
  first-cps : {Result : Set} {X Y : Set} (R : Reg)
            → (X → ⟦ ∇ R ⟧₂ Y X → Maybe Result)
            → ⟦ R ⟧ X → Maybe Result
  first-cps 0′ k ()
  first-cps 1′ k tt = nothing
  first-cps V k x   = k x tt
  first-cps (R ⨁ Q) k (inj₁ x) = first-cps R (λ x ctx → k x (inj₁ ctx)) x
  first-cps (R ⨁ Q) k (inj₂ y) = first-cps Q (λ y ctx → k y (inj₂ ctx)) y
  first-cps (R ⨂ Q) k (r , q)  = first-cps R (λ x ctx → k x (inj₁ (ctx , q))) r

  mutual
    first-μ-cps : ∀ {Result : Set} {X : Set} (R : Reg) → μ R → List (⟦ ∇ R ⟧₂ X (μ R)) → Maybe Result
    first-μ-cps {Result} {X} R (In x) ctxs
      = first-cps R (cont-μ R ctxs) x

    cont-μ : ∀ {Result : Set} {X : Set} (R : Reg) → List (⟦ ∇ R ⟧₂ X (μ R)) → μ R → ⟦ ∇ R ⟧₂ X (μ R) → Maybe Result
    cont-μ R ctxs (In x) ctx = {! !}
    {-
    ∀ {x} {y} → A x y × (A x y → ⊥) ⊎ B x y
  -}
  data lt : (R : Reg) → Zipper R → Zipper R → Set where
    -- this are wrong
--    lt-left  : ∀ {R} {t₁ t₂ s s₂} → Plug R (s , plug-μ R t₂ s₂) t₁ → IsInj₁ R s → lt R (In t₁ , []) (t₂ , s ∷ s₂)
--    lt-right : ∀ {R} {t₁ t₂ s s₁} → Plug R (s , plug-μ R t₁ s₁) t₂ → IsInj₂ R s → lt R (t₁ , s ∷ s₁) (In t₂ , [])

    lt-step  : ∀ {R} {t₁ t₂ x y s₁ s₂}  → x ≡ y → lt R (t₁ , s₁) (t₂ , s₂)                    → lt R (t₁ , x ∷ s₁) (t₂ , y ∷ s₂)
    lt-base  : ∀ {R} {t₁ t₂ x y s₁ s₂}  → nltReg R (y , plug-μ R t₂ s₂) (x , plug-μ R t₁ s₁)  → lt R (t₂ , y ∷ s₂) (t₁ , x ∷ s₁)

  {- We need to do induction on R because we need to pattern match on the top of the list
     so plug can reduce by computation -}
  -- related : (R : Reg) → (x y : Zipper R) → lt R x y → plug-⊳ R x ≡ plug-⊳ R y
  -- related 0′ (a , s) (b , s′) p = {!!}
  -- related 1′ (a , s) (b , s′) p = {!!}
  -- related V (.(In _) , .[]) (b , .(_ ∷ _)) (lt-left x ())
  -- related V (a , .(_ ∷ _)) (.(In _) , .[]) (lt-right x ())
  -- related V (a , .(tt ∷ s₁)) (b , .(tt ∷ s₂)) (lt-step {x = tt} {s₁ = s₁} {s₂} refl p) = {!!}
  -- related V (a , .(y ∷ s₂)) (b , .(x ∷ s₁)) (lt-base {x = x} {y} {s₁} {s₂} p) = {!!}
  -- related (R ⨁ Q) (.(In _) , .[]) (b , .(inj₁ x ∷ s₂)) (lt-left {s = inj₁ x} {s₂} p isI)
  --   with Plug-related (R ⨁ Q) (inj₁ x) _ _ p
  -- ...  | refl = refl
  -- related (R ⨁ Q) (.(In _) , .[]) (b , .(inj₂ y ∷ s₂)) (lt-left {s = inj₂ y} {s₂} p isI)
  --   with Plug-related (R ⨁ Q) (inj₂ y) _ _ p
  -- ...  | refl = refl
  -- related (R ⨁ Q) (a , .(inj₁ x ∷ s₁)) (.(In _) , .[]) (lt-right {s = inj₁ x} {s₁} p isI)
  --   with Plug-related (R ⨁ Q) (inj₁ x) _ _ p
  -- ... | refl = refl
  -- related (R ⨁ Q) (a , .(inj₂ y ∷ s₁)) (.(In _) , .[]) (lt-right {s = inj₂ y} {s₁} p isI)
  --   with Plug-related (R ⨁ Q) (inj₂ y) _ _ p
  -- ... | refl = refl
  -- related (R ⨁ Q) (a , .(inj₁ x ∷ s₁)) (b , .(inj₁ x ∷ s₂)) (lt-step {x = inj₁ x} {s₁ = s₁} {s₂} refl p)
  --  = cong (In ∘ inj₁ ∘ plug R x) (related (R ⨁ Q) (a  , s₁) (b , s₂) p)
  -- related (R ⨁ Q) (a , .(inj₂ y ∷ s₁)) (b , .(inj₂ y ∷ s₂)) (lt-step {x = inj₂ y} {s₁ = s₁} {s₂} refl p)
  --  = cong (In ∘ inj₂ ∘ plug Q y) (related (R ⨁ Q) (a , s₁) (b , s₂) p)
  -- related (R ⨁ Q) (a , .(inj₂ x ∷ s₂)) (b , .(inj₂ y ∷ s₁)) (lt-base {x = .(inj₂ y)} {.(inj₂ x)} {s₁} {s₂} (step-⨁-inj₂ {x = x} {y} p)) = {!!}
  -- related (R ⨁ Q) (a , .(inj₁ x ∷ s₂)) (b , .(inj₁ y ∷ s₁)) (lt-base {x = .(inj₁ y)} {.(inj₁ x)} {s₁} {s₂} (step-⨁-inj₁ {x = x} {y} p)) = {!!}
  -- --  with nltReg-related R x y (plug-μ (R ⨁ Q) b s₁) (plug-μ (R ⨁ Q) a s₂) p 
  -- -- ... | z =  {!!}
  -- related (R ⨂ R₁) (.(In _) , .[]) (b , .(_ ∷ _)) (lt-left x x₁) = {!!}
  -- related (R ⨂ R₁) (a , .(_ ∷ _)) (.(In _) , .[]) (lt-right x x₁) = {!!}
  -- related (R ⨂ R₁) (a , .(_ ∷ _)) (b , .(_ ∷ _)) (lt-step x₁ p) = {!!}
  -- related (R ⨂ R₁) (a , .(_ ∷ _)) (b , .(_ ∷ _)) (lt-base x₁) = {!!}

  binF : Reg
  binF = (V ⨂ V) ⨁ 1′

  z₁ : Zipper binF
  z₁ = (In (inj₂ tt)) , inj₁ (inj₁ (tt , In (inj₂ tt))) ∷ []

  z₂ : Zipper binF
  z₂ = (In (inj₂ tt) , (inj₁ (inj₂ ((In (inj₂ tt)) , tt))) ∷ [])

  z₃ : Zipper binF
  z₃ = (In (inj₁ (In (inj₂ tt) , In (inj₂ tt)))) , []
  
  Proof : lt binF z₂ z₁
  Proof = lt-base (step-⨁-inj₁ (base-⨂ refl))
  
  data IRel (R : Reg) (t : μ R) : Zipper R → Zipper R → Set where
    iRel : ∀ z₁ z₂ → plug-⊳ R z₁ ≡ t
                   → plug-⊳ R z₂ ≡ t
                   → lt R z₁ z₂ → IRel R t z₁ z₂
  mutual

    acc-⨁-inj₁ : ∀ R Q x a s₁ → Acc (IRel (R ⨁ Q) (plug-μ (R ⨁ Q) a s₁)) (a , s₁)
                               → WfRec (IRel (R ⨁ Q) (In (inj₁ (plug R x (plug-μ (R ⨁ Q) a s₁)))))
                                        (Acc (IRel (R ⨁ Q) (In (inj₁ (plug R x (plug-μ (R ⨁ Q) a s₁)))))) (a , inj₁ x ∷ s₁)
    acc-⨁-inj₁ R Q x a s (acc rs) (y , .(inj₁ x ∷ s₁)) (iRel .(y , inj₁ x ∷ s₁) .(a , inj₁ x ∷ s) eq₁ eq₂ (lt-step {s₁ = s₁} refl p))
      with plug-μ (R ⨁ Q) a s | plug-injective R x (plug-μ (R ⨁ Q) a s) (plug-μ (R ⨁ Q) y s₁) ((⊎-injective₁ (In-injective (sym eq₁))))
    acc-⨁-inj₁ R Q x a s (acc rs) (y , .(inj₁ x ∷ s₁)) (iRel .(y , inj₁ x ∷ s₁) .(a , inj₁ x ∷ s) eq₁ eq₂ (lt-step {s₁ = s₁} refl p))
      | .(plug-μ (R ⨁ Q) y s₁) | refl
      = acc (acc-⨁-inj₁ R Q x y s₁ (rs (y , s₁) (iRel (y , s₁) (a , s) refl {!!} p)))             -- We need to remember the equality but is done
    acc-⨁-inj₁ R Q c a s (acc rs) (b , .(inj₁ x ∷ s₂)) (iRel .(b , inj₁ x ∷ s₂) .(a , inj₁ c ∷ s) eq₁ refl (lt-base {y = .(inj₁ x)} {s₂ = s₂} (step-⨁-inj₁ {x = x} p)))
      with plug R c (plug-μ (R ⨁ Q) a s) | sym eq₁
    acc-⨁-inj₁ R Q c a s (acc rs) (b , .(inj₁ x ∷ s₂)) (iRel .(b , inj₁ x ∷ s₂) .(a , inj₁ c ∷ s) eq₁ refl (lt-base {_} {_} {_} {_} {.(inj₁ x)} {s₂ = s₂} (step-⨁-inj₁ {x = x} p))) | .(plug R x (plug-μ (R ⨁ Q) b s₂)) | refl = acc (acc-⨁-inj₁ R Q x b s₂ {!IRel-WF ? ? ? !}) -- acc (acc-⨁-inj₁ R Q x b s₂ {!IRel-WF ? ? ?!})

    -- acc-impl : ∀ (R : Reg) t b a → Acc (IRel R (In (plug R b t))) a → WfRec (IRel R t) (Acc (IRel R t)) a
    -- acc-impl R t b (_ , _) (acc rs) (b , .(x₄ ∷ _)) (iRel .(b , x₄ ∷ _) .(_ , x₄ ∷ _) x₁ x₂ (lt-step {x = x₄} refl x₃)) = {!.s₁!}
    -- acc-impl R t b (_ , _) (acc rs) (b , .(_ ∷ _)) (iRel .(b , _ ∷ _) .(_ , _ ∷ _) x₁ x₂ (lt-base x₄)) = {!!}

    IRel-WF : (R : Reg) → (t : μ R) → Well-founded (IRel R t)
    IRel-WF R t x = acc (aux R t x)
      where aux : (R : Reg) → (t : μ R) → (x : Zipper R) → WfRec (IRel R t) (Acc (IRel R t)) x
            aux R t (x , .(_ ∷ s₂)) (y , .(_ ∷ s₁)) (iRel .(y , _ ∷ s₁) .(x , _ ∷ s₂) eq₁ eq₂ (lt-step {s₁ = s₁} {s₂} x₃ p)) = {!!}
            aux 0′ t (a , .(x ∷ s₁)) (b , .(y ∷ s₂)) (iRel .(b , y ∷ s₂) .(a , x ∷ s₁) eq₁ eq₂ (lt-base {x = x} {y} {s₁} {s₂} p)) = {!!}
            aux 1′ t (a , .(x ∷ s₁)) (b , .(y ∷ s₂)) (iRel .(b , y ∷ s₂) .(a , x ∷ s₁) eq₁ eq₂ (lt-base {x = x} {y} {s₁} {s₂} p)) = {!!}
            aux V t (a , .(x ∷ s₁)) (b , .(y ∷ s₂)) (iRel .(b , y ∷ s₂) .(a , x ∷ s₁) eq₁ eq₂ (lt-base {x = x} {y} {s₁} {s₂} p)) = {!!}
            aux (R ⨁ Q) .(In (inj₁ (plug R x₁ (plug-μ (R ⨁ Q) b s₂)))) (a , .(inj₁ x ∷ s₁)) (b , .(inj₁ x₁ ∷ s₂)) (iRel .(b , inj₁ x₁ ∷ s₂) .(a , inj₁ x ∷ s₁) refl eq₂ (lt-base {x = inj₁ x} {inj₁ x₁} {s₁} {s₂} (step-⨁-inj₁ p))) = acc (acc-⨁-inj₁ R Q x₁ b s₂ {!IRel-WF  ? ? ?!})
         
            aux (R ⨁ R₁) t (a , .(inj₁ x ∷ s₁)) (b , .(inj₂ y ∷ s₂)) (iRel .(b , inj₂ y ∷ s₂) .(a , inj₁ x ∷ s₁) eq₁ eq₂ (lt-base {x = inj₁ x} {inj₂ y} {s₁} {s₂} ()))
            aux (R ⨁ R₁) t (a , .(inj₂ y₁ ∷ s₁)) (b , .(inj₁ x ∷ s₂)) (iRel .(b , inj₁ x ∷ s₂) .(a , inj₂ y₁ ∷ s₁) eq₁ eq₂ (lt-base {x = inj₂ y₁} {inj₁ x} {s₁} {s₂} p)) = {!!}
            aux (R ⨁ Q) .(In (inj₂ (plug Q y (plug-μ (R ⨁ Q) b s₂)))) (a , .(inj₂ y₁ ∷ s₁)) (b , .(inj₂ y ∷ s₂)) (iRel .(b , inj₂ y ∷ s₂) .(a , inj₂ y₁ ∷ s₁) refl eq₂ (lt-base {x = inj₂ y₁} {inj₂ y} {s₁} {s₂} p)) = acc {!acc-⨁-inj!}  
            
            aux (R ⨂ R₁) .(In (plug R dr (plug-μ (R ⨂ R₁) b s₂) , q)) (a , .(inj₁ (dr′ , q) ∷ s₁)) (b , .(inj₁ (dr , q) ∷ s₂)) (iRel .(b , inj₁ (dr , q) ∷ s₂) .(a , inj₁ (dr′ , q) ∷ s₁) refl eq₂ (lt-base {x = .(inj₁ (dr′ , q))} {.(inj₁ (dr , q))} {s₁} {s₂} (step-⨂-inj₁ {dr = dr} {dr′} {q} refl p))) = acc {!!}
            aux (R ⨂ R₁) t (a , .(inj₂ (_ , _) ∷ s₁)) (b , .(inj₂ (_ , _) ∷ s₂)) (iRel .(b , inj₂ (_ , _) ∷ s₂) .(a , inj₂ (_ , _) ∷ s₁) eq₁ eq₂ (lt-base {x = .(inj₂ (_ , _))} {.(inj₂ (_ , _))} {s₁} {s₂} (step-⨂-inj₂ x₁ p))) = {!!}
            aux (R ⨂ R₁) t (a , .(inj₁ _ ∷ s₁)) (b , .(inj₂ _ ∷ s₂)) (iRel .(b , inj₂ _ ∷ s₂) .(a , inj₁ _ ∷ s₁) eq₁ eq₂ (lt-base {x = .(inj₁ _)} {.(inj₂ _)} {s₁} {s₂} (base-⨂ x₂))) = {!!}

  data IRel1 (R : Reg) (t : ⟦ R ⟧ (μ R)) : Zipper R → Zipper R → Set where
    iRel : ∀ t₁ x s₁ t₂ y s₂ → Plug R (x , plug-μ R t₁ s₁) t
                             → Plug R (y , plug-μ R t₂ s₂) t
                             → lt R (t₁ , x ∷ s₁) (t₂ , y ∷ s₂)
                             → IRel1 R t (t₁ , s₁) (t₂ , s₂)

  
  mutual
    acc1-⨁-inj₁ : ∀ R Q x a s → Acc (IRel1 (R ⨁ Q) (inj₁ x)) (a , s) → WfRec (IRel1 (R ⨁ Q) (inj₁ x)) (Acc (IRel1 (R ⨁ Q) (inj₁ x))) (a , s)
    acc1-⨁-inj₁ R Q x a s (acc rs) .(t₁ , s₁) (iRel t₁ .(inj₁ x₁) s₁ .a .(inj₁ x₁) .s (step-⨁-inj₁ {x = x₁} eq₁) (step-⨁-inj₁ eq₂) (lt-step refl p)) = {!!}
    acc1-⨁-inj₁ R Q x a s (acc rs) .(t₁ , s₁) (iRel t₁ x₁ s₁ .a y .s eq₁ eq₂ (lt-base x₂)) = {!!}
      
    IRel1-WF : (R : Reg) → (t : ⟦ R ⟧ (μ R)) → Well-founded (IRel1 R t)
    IRel1-WF R t x = acc (aux R t x)
      where aux : (R : Reg) → (t : ⟦ R ⟧ (μ R)) → (x : Zipper R) → WfRec (IRel1 R t) (Acc (IRel1 R t)) x
            aux 0′ t (a , s) (b , s′) (iRel .b () .s′ .a _ .s eq₁ eq₂ (lt-step refl p))
            aux 1′ t (a , s) (b , s′) (iRel .b () .s′ .a _ .s eq₁ eq₂ (lt-step refl p))
            aux V t (a , s) (b , s′) (iRel .b x .s′ .a .x .s eq₁ eq₂ (lt-step refl p)) = {!!}
            aux (R ⨁ Q) .(inj₁ y) (a , s) (b , s′) (iRel .b .(inj₁ x) .s′ .a .(inj₁ x) .s (step-⨁-inj₁ {x = x} {y} eq₁) (step-⨁-inj₁ eq₂) (lt-step refl p))
              = acc {!eq₁!}
            aux (R ⨁ Q) .(inj₂ y) (a , s) (b , s′) (iRel .b .(inj₂ x) .s′ .a .(inj₂ x) .s (step-⨁-inj₂ {x = x} {y} eq₁) (step-⨁-inj₂ eq₂) (lt-step refl p)) = {!!}
            aux (R ⨂ R₁) t (a , s) (b , s′) (iRel .b x .s′ .a .x .s eq₁ eq₂ (lt-step refl p)) = {!!}
            aux R t (a , s) (b , s′) (iRel .b x .s′ .a y .s eq₁ eq₂ (lt-base x₂)) = {!!}
