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

  ×-injective : ∀ {A B : Set} {x y a b} → (A × B ∋ (x , y)) ≡ (a , b) → x ≡ a × y ≡ b
  ×-injective refl = refl , refl

  ×-injective-inv : ∀ {A B : Set} {x y a b}  → x ≡ a × y ≡ b → (A × B ∋ (x , y)) ≡ (a , b)
  ×-injective-inv (refl , refl) = refl
  ⊎-injective₁ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
  ⊎-injective₁ refl = refl

  ⊎-injective₂ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
  ⊎-injective₂ refl = refl

  data Reg : Set₁ where
    0′    : Reg
    1′    : Reg
    V     : Reg
    K     : (A : Set) → Reg
    _⨁_  : (r₁ r₂ : Reg) → Reg
    _⨂_  : (r₁ r₂ : Reg) → Reg

  infixl 30 _⨁_
  infixl 40 _⨂_

  ⟦_⟧ : Reg → (Set → Set)
  ⟦ 0′ ⟧ X  = ⊥
  ⟦ 1′ ⟧ X  = ⊤
  ⟦ K A ⟧ X = A 
  ⟦ V ⟧  X  = X
  ⟦ F ⨁ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
  ⟦ F ⨂ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

  fmap : ∀ {A B : Set} (R : Reg) → (A → B) → ⟦ R ⟧ A → ⟦ R ⟧ B
  fmap 0′ f ()
  fmap 1′ f tt   = tt
  fmap V f x     = f x
  fmap (K A) f x = x 
  fmap (R ⨁ Q) f (inj₁ x)  = inj₁ (fmap R f x)
  fmap (R ⨁ Q) f (inj₂ y)  = inj₂ (fmap Q f y)
  fmap (R ⨂ Q) f (x , y)   = (fmap R f x) , (fmap Q f y)

  data μ (R : Reg) : Set where
    In : ⟦ R ⟧ (μ R) → μ R

  In-injective : ∀ {R : Reg} {x y} → (μ R ∋ In x) ≡ In y → x ≡ y
  In-injective refl = refl

  ∇ : (R : Reg) → (Set → Set → Set)
  ∇ 0′ X Y = ⊥
  ∇ 1′ X Y = ⊥
  ∇ V X Y  = ⊤
  ∇ (K A) X Y = ⊥
  ∇ (R ⨁ Q) X Y = ∇ R X Y ⊎ ∇ Q X Y
  ∇ (R ⨂ Q) X Y = ∇ R X Y × ⟦ Q ⟧ Y ⊎ ⟦ R ⟧ X × ∇ Q X Y

  plug : ∀ {X : Set} → (R : Reg) → ∇ R X X → X → ⟦ R ⟧ X
  plug 0′ () x
  plug 1′ () x
  plug V tt x = x
  plug (K A) () x
  plug (u ⨁ v) (inj₁ u′) x  = inj₁ (plug u u′ x)
  plug (u ⨁ v) (inj₂ v′) x  = inj₂ (plug v v′ x)
  plug (u ⨂ v) (inj₁ (du , v′)) x = plug u du x  , v′
  plug (u ⨂ v) (inj₂ (u′ , dv)) x = u′           , plug v dv x

  data nltReg {X : Set} : (R : Reg) → (∇ R X X × X) → (∇ R X X × X) → Set where
    step-⨂-inj₁ : ∀ {R Q} {dr dr′ q q′} {t₁ t₂}
                 → q ≡ q′
                 → nltReg R (dr , t₁) (dr′ , t₂)             
                 → nltReg  ( R ⨂ Q ) (inj₁ (dr , q) , t₁) (inj₁ (dr′ , q′) , t₂)

    step-⨂-inj₂ : ∀ {R Q} {dq dq′ r r′} {t₁ t₂}
                 → r ≡ r′
                 → nltReg Q (dq , t₁) (dq′ , t₂)
                 → nltReg ( R ⨂ Q ) (inj₂ (r , dq) , t₁) (inj₂ (r′ , dq′) , t₂)

    base-⨂      : ∀ {R Q : Reg} {dr dq r q} {t₁ t₂}
                 → plug (R ⨂ Q) (inj₂ (r , dq)) t₁ ≡ plug (R ⨂ Q) (inj₁ (dr , q)) t₂
                 → nltReg (R ⨂ Q) (inj₂ (r , dq) , t₁) (inj₁ (dr , q) , t₂)

    step-⨁-inj₂ : ∀ {R Q} {q q′} {t₁ t₂}
                 → nltReg Q (q , t₁) (q′ , t₂)
                 → nltReg (R ⨁ Q) (inj₂ q , t₁) (inj₂ q′ , t₂)
                 
    step-⨁-inj₁ : ∀ {R Q} {r r′} {t₁ t₂}
                 → nltReg R (r , t₁) (r′ , t₂)
                 → nltReg (R ⨁ Q) (inj₁ r , t₁) (inj₁ r′ , t₂)

  nltReg-related : ∀ {X : Set} → (R : Reg)
                 → (h₁ h₂ : ∇ R X X) → (x y : X) → nltReg R (h₁ , x) (h₂ , y) → plug R h₁ x ≡ plug R h₂ y
  nltReg-related 0′ h₁ h₂ x y ()
  nltReg-related 1′ h₁ h₂ x y ()
  nltReg-related V h₁ h₂ x y ()
  nltReg-related (K _) h₁ h₂ x y ()
  nltReg-related (R ⨁ Q) .(inj₂ x₁) .(inj₂ y₁) x y (step-⨁-inj₂ {q = x₁} {y₁} p)
    = cong inj₂ (nltReg-related Q x₁ y₁ x y p)
  nltReg-related (R ⨁ Q) .(inj₁ x₁) .(inj₁ y₁) x y (step-⨁-inj₁ {r = x₁} {y₁} p)
    = cong inj₁ (nltReg-related R x₁ y₁ x y p)
  nltReg-related (R ⨂ Q) .(inj₁ (dr , q)) .(inj₁ (dr′ , q)) x y (step-⨂-inj₁ {dr = dr} {dr′} {q} refl p)
    = cong (_, q) (nltReg-related R dr dr′ x y p)
  nltReg-related (R ⨂ Q) .(inj₂ (r , dq)) .(inj₂ (r , dq′)) x y (step-⨂-inj₂ {dq = dq} {dq′} {r} refl p)
    = cong (_,_ r) (nltReg-related Q dq dq′ x y p)
  nltReg-related (R ⨂ Q) .(inj₂ (plug R _ y , _)) .(inj₁ (_ , plug Q _ x)) x y (base-⨂ refl) = refl

  data nltRegIx {X : Set} (R : Reg) (r : ⟦ R ⟧ X) : ∇ R X X × X → ∇ R X X × X → Set where
    nlt : ∀ h₁ x h₂ y → plug R h₁ x ≡ r → plug R h₂ y ≡ r → nltReg R (h₁ , x) (h₂ , y) → nltRegIx R r (h₁ , x) (h₂ , y)

  mutual
    acc-⨂-inj₁ : ∀ {X} (R Q : Reg) (q : ⟦ Q ⟧ X) (dr : ∇ R X X) (x : X)
                → Acc (nltRegIx R (plug R dr x)) (dr , x) →
                (y : (∇ R X X × ⟦ Q ⟧ X ⊎  ⟦ R ⟧ X × ∇ Q X X) × X) → nltRegIx (R ⨂ Q) (plug R dr x , q) y (inj₁ (dr , q) , x)
                                                                   → Acc (nltRegIx (R ⨂ Q) (plug R dr x , q)) y
    acc-⨂-inj₁ R Q q dr x (acc rs) .(inj₁ (dr₁ , q) , x₁) (nlt .(inj₁ (dr₁ , q)) x₁ .(inj₁ (dr , q)) .x eq₁ eq₂ (step-⨂-inj₁ {dr = dr₁} refl p))
      with plug R dr x | proj₁ (×-injective (sym eq₁))
    acc-⨂-inj₁ R Q q dr x (acc rs) .(inj₁ (dr₁ , q) , x₁) (nlt .(inj₁ (dr₁ , q)) x₁ .(inj₁ (dr , q)) .x eq₁ eq₂ (step-⨂-inj₁ {dr = dr₁} refl p))
      | .(plug R dr₁ x₁) | refl = acc (acc-⨂-inj₁ R Q q dr₁ x₁ (rs (dr₁ , x₁) (nlt dr₁ x₁ dr x refl (proj₁ (×-injective (sym eq₁))) p)))
    acc-⨂-inj₁ R Q .(plug Q dq x₁) dr x (acc rs) .(inj₂ (plug R dr x , dq) , x₁)
                   (nlt .(inj₂ (plug R dr x , dq)) x₁ .(inj₁ (dr , plug Q dq x₁)) .x refl refl (base-⨂ {dq = dq} refl))
      = acc (acc-⨂-inj₂ R Q (plug R dr x) dq x₁ (nltRegIx-WF Q (plug Q dq x₁) (dq , x₁)))

    acc-⨂-inj₂ : ∀ {X} (R Q : Reg) (r : ⟦ R ⟧ X) (dq : ∇ Q X X) (x : X)
                → Acc (nltRegIx Q (plug Q dq x)) (dq , x) →
               (y : (∇ R X X × ⟦ Q ⟧ X ⊎ ⟦ R ⟧ X × ∇ Q X X) × X) → nltRegIx (R ⨂ Q) (r , plug Q dq x) y (inj₂ (r , dq) , x) →
                                                                   Acc (nltRegIx (R ⨂ Q) (r , plug Q dq x)) y
    acc-⨂-inj₂ R Q r dq x (acc rs) .(inj₂ (r , dq₁) , x₁) (nlt .(inj₂ (r , dq₁)) x₁ .(inj₂ (r , dq)) .x eq₁ eq₂ (step-⨂-inj₂ {dq = dq₁} refl p))
      with plug Q dq x | proj₂ (×-injective (sym eq₁))
    acc-⨂-inj₂ R Q r dq x (acc rs) .(inj₂ (r , dq₁) , x₁) (nlt .(inj₂ (r , dq₁)) x₁ .(inj₂ (r , dq)) .x eq₁ eq₂ (step-⨂-inj₂ {dq = dq₁} refl p))
      | .(plug Q dq₁ x₁) | refl = acc (acc-⨂-inj₂ R Q r dq₁ x₁ (rs (dq₁ , x₁) (nlt dq₁ x₁ dq x refl (sym (proj₂ (×-injective eq₁))) p)))

    acc-⨁-inj₂ : ∀ {X : Set} (R Q : Reg) (q : ∇ Q X X) (x : X) →
               Acc (nltRegIx Q (plug Q q x)) (q , x) → 
               (y : (∇ R X X ⊎ ∇ Q X X) × X) →
               nltRegIx (R ⨁ Q) (inj₂ (plug Q q x)) y (inj₂ q , x) →
               Acc (nltRegIx (R ⨁ Q) (inj₂ (plug Q q x))) y
    acc-⨁-inj₂ R Q q x (acc rs) .(inj₂ q₁ , x₁) (nlt .(inj₂ q₁) x₁ .(inj₂ q) .x eq₁ refl (step-⨁-inj₂ {q = q₁} p))
      with plug Q q x | ⊎-injective₂ (sym eq₁)
    acc-⨁-inj₂ R Q q x (acc rs) .(inj₂ q₁ , x₁) (nlt .(inj₂ q₁) x₁ .(inj₂ q) .x eq₁ refl (step-⨁-inj₂ {q = q₁} p))
      | .(plug Q q₁ x₁) | refl = acc (acc-⨁-inj₂ R Q q₁ x₁ (rs (q₁ , x₁) (nlt q₁ x₁ q x refl (⊎-injective₂ (sym eq₁)) p)))

    acc-⨁-inj₁ : ∀ {X : Set} (R Q : Reg) (r : ∇ R X X) (x : X) →
                 Acc (nltRegIx R (plug R r x)) (r , x) → 
                 (y : (∇ R X X ⊎ ∇ Q X X) × X) →
                 nltRegIx (R ⨁ Q) (inj₁ (plug R r x)) y (inj₁ r , x) →
                 Acc (nltRegIx (R ⨁ Q) (inj₁ (plug R r x))) y
    acc-⨁-inj₁ R Q r x (acc rs) .(inj₁ r₁ , x₁) (nlt .(inj₁ r₁) x₁ .(inj₁ r) .x eq₁ refl (step-⨁-inj₁ {r = r₁} p))
      with plug R r x | ⊎-injective₁ (sym eq₁)
    acc-⨁-inj₁ R Q r x (acc rs) .(inj₁ r₁ , x₁) (nlt .(inj₁ r₁) x₁ .(inj₁ r) .x eq₁ refl (step-⨁-inj₁ {r = r₁} p))
      | .(plug R r₁ x₁) | refl = acc (acc-⨁-inj₁ R Q r₁ x₁ (rs (r₁ , x₁) (nlt r₁ x₁ r x refl (⊎-injective₁ (sym eq₁)) p)))

    nltRegIx-WF : {X : Set} (R : Reg) (t : ⟦ R ⟧ X) → Well-founded (nltRegIx {X} R t)
    nltRegIx-WF R t x = acc (aux R t x)
      where
        aux : ∀ {X : Set} (R : Reg) (t : ⟦ R ⟧ X) (x y : ∇ R X X × X) → nltRegIx R t y x → Acc (nltRegIx R t) y
        aux .(R ⨂ Q) .(plug R dr x , q) .(inj₁ (dr′ , q) , y) .(inj₁ (dr , q) , x)
                          (nlt .(inj₁ (dr , q)) x .(inj₁ (dr′ , q)) y refl eq₂ (step-⨂-inj₁ {R} {Q} {dr} {dr′} {q} {.q} refl p))
              = acc (acc-⨂-inj₁ R Q q dr x (nltRegIx-WF R (plug R dr x) (dr , x)))
        aux .(R ⨂ Q) .(r , plug Q dq x) .(inj₂ (r , dq′) , y) .(inj₂ (r , dq) , x)
                          (nlt .(inj₂ (r , dq)) x .(inj₂ (r , dq′)) y refl eq₂ (step-⨂-inj₂ {R} {Q} {dq} {dq′} {r} refl p))
              = acc (acc-⨂-inj₂ R Q r dq x (nltRegIx-WF Q (plug Q dq x) (dq , x)))
        aux .(R ⨂ Q) .(plug R dr y , plug Q dq x) .(inj₁ (dr , plug Q dq x) , y) .(inj₂ (plug R dr y , dq) , x)
                          (nlt .(inj₂ (plug R dr y , dq)) x .(inj₁ (dr , plug Q dq x)) y refl refl (base-⨂ {R} {Q} {dr} {dq} refl))
              = acc (acc-⨂-inj₂ R Q (plug R dr y) dq x (nltRegIx-WF Q (plug Q dq x) (dq , x)))
        aux .(R ⨁ Q) .(inj₂ (plug Q q x)) .(inj₂ q′ , y) .(inj₂ q , x) (nlt .(inj₂ q) x .(inj₂ q′) y refl eq₂ (step-⨁-inj₂ {R} {Q} {q} {q′} p))
          = acc (acc-⨁-inj₂ R Q q x (nltRegIx-WF Q (plug Q q x) (q , x)))
        aux .(R ⨁ Q) .(inj₁ (plug R r x)) .(inj₁ r′ , y) .(inj₁ r , x) (nlt .(inj₁ r) x .(inj₁ r′) y refl eq₂ (step-⨁-inj₁ {R} {Q} {r} {r′} p))
          = acc (acc-⨁-inj₁ R Q r x (nltRegIx-WF R (plug R r x) (r , x)))

  first : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → Maybe (∇ R X X × X)
  first 0′ ()
  first 1′ x = nothing
  first V x  = just (tt , x)
  first (K A) x = nothing
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

  first-preserves-plug : ∀ {X : Set} → (R : Reg) → (r : ⟦ R ⟧ X) → (h : ∇ R X X) (x : X) → first R r ≡ just (h , x) → plug R h x ≡ r
  first-preserves-plug 0′ r () x x₁
  first-preserves-plug 1′ r h x ()
  first-preserves-plug V r .tt .r refl = refl
  first-preserves-plug (K _) r () x p
  first-preserves-plug (R ⨁ Q) (inj₁ r) h x p with first R r | inspect (first R) r
  first-preserves-plug (R ⨁ Q) (inj₁ r) .(inj₁ dr) .x′ refl | just (dr , x′) | Reveal_·_is_.[ eq ]
    = cong inj₁ (first-preserves-plug R r dr x′ eq)
  first-preserves-plug (R ⨁ Q) (inj₁ r) h x () | nothing | eq
  first-preserves-plug (R ⨁ Q) (inj₂ q) h x p with first Q q | inspect (first Q) q
  first-preserves-plug (R ⨁ Q) (inj₂ q) .(inj₂ dq) .x′ refl | just (dq , x′) | Reveal_·_is_.[ eq ]
    = cong inj₂ (first-preserves-plug Q q dq x′ eq)
  first-preserves-plug (R ⨁ Q) (inj₂ q) h x () | nothing | eq
  first-preserves-plug (R ⨂ Q) (r , q) h x p with first R r | inspect (first R) r
  first-preserves-plug (R ⨂ Q) (r , q) .(inj₁ (dr , q)) .x′ refl | just (dr , x′) | Reveal_·_is_.[ eq ]
    = cong (_, q) (first-preserves-plug R r dr x′ eq)
  first-preserves-plug (R ⨂ Q) (r , q) h x p | nothing | Reveal_·_is_.[ eq ]
    with first Q q | inspect (first Q) q
  first-preserves-plug (R ⨂ Q) (r , q) .(inj₂ (r , dq)) .x′ refl | nothing | Reveal_·_is_.[ eq ] | just (dq , x′) | Reveal_·_is_.[ eq₁ ]
    = cong (_,_ r) (first-preserves-plug Q q dq x′ eq₁)
  first-preserves-plug (R ⨂ Q) (r , q) h x () | nothing | Reveal_·_is_.[ eq ] | nothing | eq₁

  right : ∀ {X : Set} → (R : Reg) → ∇ R X X × X → (∇ R X X × X) ⊎ (⟦ R ⟧ X)
  right 0′ (() , _)
  right 1′ (() , _)
  right V (tt , x) = inj₂ x
  right (K _) (() , _)
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

  righty : ∀ {j c : Set} → (R : Reg) → ⟦ R ⟧ j ⊎ (∇ R j c × c) → ⟦ R ⟧ c ⊎ (∇ R j c × j)
  righty = {!!}


  plug-μ : ∀ (R : Reg) → μ R → List (∇ R (μ R) (μ R)) → μ R
  plug-μ u t []         = t
  plug-μ 0′ t (() ∷ xs)
  plug-μ 1′ t (() ∷ xs)
  plug-μ (K _) _ (() ∷ xs)
  plug-μ V t (tt ∷ xs)  = t
  plug-μ (u ⨁ v) t (inj₁ du ∷ xs)         = In (inj₁ (plug u du (plug-μ (u ⨁ v) t xs)))
  plug-μ (u ⨁ v) t (inj₂ dv ∷ xs)         = In (inj₂ (plug v dv (plug-μ (u ⨁ v) t xs)))
  plug-μ (u ⨂ v) t (inj₁ (du , v′) ∷ xs)  = In (plug u du (plug-μ (u ⨂ v) t xs) , v′)
  plug-μ (u ⨂ v) t (inj₂ (u′ , dv) ∷ xs)  = In (u′ , (plug v dv (plug-μ (u ⨂ v) t xs)))


  {- What is a leaf of μ R? 

  ∀ {X : Set} → ⟦ R ⟧ X

  -}
  Leaf : (R : Reg) → Set₁
  Leaf R = ∀ {X} → ⟦ R ⟧ X

  Zipper : (R : Reg) → Set₁
  Zipper R = Leaf R × List (∇ R (μ R) (μ R))

  plugZ : (R : Reg) → Zipper R → μ R
  plugZ R (leaf , stk) = plug-μ R (In leaf) stk

  data lt (R : Reg) : Zipper R → Zipper R → Set₁ where
  --  lt-step : ∀ {t₁ t₂} {h} {s₁ s₂}            →  lt R (t₁ , s₁) (t₂ , s₂)                           → lt R (t₁ , h  ∷ s₁) (t₂ , h  ∷ s₂)





--  data lt {X : Set} (R : Reg) (em : X → μ R) : List (∇ R (μ R) (μ R)) × X → List (∇ R (μ R) (μ R)) × X → Set where
--    lt-step : ∀ {t₁ t₂} {h} {s₁ s₂}            →  lt R em (s₁ , t₁) (s₂ , t₂)                           → lt R em (h  ∷ s₁ , t₁) (h  ∷ s₂ , t₂)
--    lt-base  : ∀ {h₁ h₂} {s₁ s₂} {t₁ t₂}       → h₁ ≡ nltReg R (h₁ , plug-μ R (em t₂)  s₂) (h₂ , plug-μ R (em t₁) s₁)  → lt R em (h₁ ∷ s₁ , t₁) (h₂ ∷ s₂ , t₂)

--   right-preserves-plug₂ : ∀ {X : Set} (R : Reg) (h : ∇ R X X ) (x : X) (r : ⟦ R ⟧ X) → right R (h , x) ≡ inj₂ r → r ≡ plug R h x
--   right-preserves-plug₂ 0′ () x r p
--   right-preserves-plug₂ 1′ () x r p
--   right-preserves-plug₂ (K _) () x r p
--   right-preserves-plug₂ V h x .x refl = refl
--   right-preserves-plug₂ (R ⨁ Q) (inj₁ h) x r p with right R (h , x) | inspect (right R) (h , x)
--   right-preserves-plug₂ (R ⨁ Q) (inj₁ h) x r () | inj₁ _ | Reveal_·_is_.[ eq ]
--   right-preserves-plug₂ (R ⨁ Q) (inj₁ h) x .(inj₁ r′) refl | inj₂ r′ | Reveal_·_is_.[ eq ]
--     = cong inj₁ (right-preserves-plug₂ R h x r′ eq)
--   right-preserves-plug₂ (R ⨁ Q) (inj₂ h) x r p with right Q (h , x) | inspect (right Q) (h , x)
--   right-preserves-plug₂ (R ⨁ Q) (inj₂ h) x r () | inj₁ _ | eq
--   right-preserves-plug₂ (R ⨁ Q) (inj₂ h) x .(inj₂ q) refl | inj₂ q | [ eq ]
--     = cong inj₂ (right-preserves-plug₂ Q h x q eq)
--   right-preserves-plug₂ (R ⨂ Q) (inj₁ (dr , q)) x r p with right R (dr , x) | inspect (right R) (dr , x)
--   right-preserves-plug₂ (R ⨂ Q) (inj₁ (dr , q)) x r () | inj₁ _ | eq
--   right-preserves-plug₂ (R ⨂ Q) (inj₁ (dr , q)) x r p | inj₂ r′ | eq with first Q q | inspect (first Q) q
--   right-preserves-plug₂ (R ⨂ Q) (inj₁ (dr , q)) x r () | inj₂ r′ | eq | just (q′ , x′′) | Reveal_·_is_.[ eq₁ ]
--   right-preserves-plug₂ (R ⨂ Q) (inj₁ (dr , q)) x .(r′ , q) refl | inj₂ r′ | Reveal_·_is_.[ eq ] | nothing | Reveal_·_is_.[ eq₁ ]
--     = cong (_, q) (right-preserves-plug₂ R dr x r′ eq)
--   right-preserves-plug₂ (R ⨂ Q) (inj₂ (r′ , dq)) x r p with right Q (dq , x) | inspect (right Q) (dq , x)
--   right-preserves-plug₂ (R ⨂ Q) (inj₂ (r′ , dq)) x r () | inj₁ (dq′ , x′) | Reveal_·_is_.[ eq ]
--   right-preserves-plug₂ (R ⨂ Q) (inj₂ (r′ , dq)) x .(r′ , q) refl | inj₂ q | Reveal_·_is_.[ eq ]
--     = cong (_,_ r′) (right-preserves-plug₂ Q dq x q eq)
  
--   right-preserves-plug₁ : ∀ {X : Set} (R : Reg) (h h′ : ∇ R X X ) (x x′ : X) → right R (h , x) ≡ inj₁ (h′ , x′) → plug R h x ≡ plug R h′ x′
--   right-preserves-plug₁ 0′ () h′ x x′ x₁
--   right-preserves-plug₁ 1′ () h′ x x′ x₁
--   right-preserves-plug₁ V h h′ x x′ ()
--   right-preserves-plug₁ (K _) () h′ x x′ x₁
--   right-preserves-plug₁ (R ⨁ Q) (inj₁ r) h′ x x′ p with right R (r , x) | inspect (right R) (r , x)
--   right-preserves-plug₁ (R ⨁ Q) (inj₁ r) .(inj₁ dr) x .q refl | inj₁ (dr , q) | Reveal_·_is_.[ eq ]
--     = cong inj₁ (right-preserves-plug₁ R r dr x q eq)
--   right-preserves-plug₁ (R ⨁ Q) (inj₁ r) h′ x x′ () | inj₂ r′ | Reveal_·_is_.[ eq ]
--   right-preserves-plug₁ (R ⨁ Q) (inj₂ q) h′ x x′ p with right Q (q , x) | inspect (right Q) (q , x)
--   right-preserves-plug₁ (R ⨁ Q) (inj₂ q) .(inj₂ dq) x .x′ refl | inj₁ (dq , x′) | Reveal_·_is_.[ eq ]
--     = cong inj₂ (right-preserves-plug₁ Q q dq x x′ eq)
--   right-preserves-plug₁ (R ⨁ Q) (inj₂ q) h′ x x′ () | inj₂ q′ | Reveal_·_is_.[ eq ]
--   right-preserves-plug₁ (R ⨂ Q) (inj₁ (dr , q)) h′ x x′ p with right R (dr , x) | inspect (right R) (dr , x)
--   right-preserves-plug₁ (R ⨂ Q) (inj₁ (dr , q)) .(inj₁ (dr′ , q)) x .x′ refl | inj₁ (dr′ , x′) | Reveal_·_is_.[ eq ]
--     = cong (_, q) (right-preserves-plug₁ R dr dr′ x x′ eq)
--   right-preserves-plug₁ (R ⨂ Q) (inj₁ (dr , q)) h′ x x′ p | inj₂ r′ | eq with first Q q | inspect (first Q) q
--   right-preserves-plug₁ (R ⨂ Q) (inj₁ (dr , q)) .(inj₂ (r′ , dr′)) x .x′′ refl | inj₂ r′ | [ eq ] | just (dr′ , x′′) | Reveal_·_is_.[ eq₁ ]
--     = ×-injective-inv (sym (right-preserves-plug₂ R dr x r′ eq) , sym (first-preserves-plug Q q dr′ x′′ eq₁))
--   right-preserves-plug₁ (R ⨂ Q) (inj₁ (dr , q)) h′ x x′ () | inj₂ r′ | eq | nothing | eq₁
--   right-preserves-plug₁ (R ⨂ Q) (inj₂ (r , dq)) h′ x x′ p with right Q (dq , x) | inspect (right Q) (dq , x)
--   right-preserves-plug₁ (R ⨂ Q) (inj₂ (r , dq)) .(inj₂ (r , dq′)) x .x′′ refl | inj₁ (dq′ , x′′) | Reveal_·_is_.[ eq ]
--     = cong (_,_ r) (right-preserves-plug₁ Q dq dq′ x x′′ eq)
--   right-preserves-plug₁ (R ⨂ Q) (inj₂ (r , dq)) h′ x x′ () | inj₂ y | eq

--   right-< : ∀ {X : Set} (R : Reg) (h : ∇ R X X) (x : X) h′ (x′ : X)
--           → right R (h , x) ≡ inj₁ (h′ , x′) → nltReg R (h′ , x′) (h , x)
--   right-< 0′ () x h′ x′ p
--   right-< 1′ () x h′ x′ p
--   right-< (K _) () x h′ x′ p
--   right-< V h x h′ x′ ()
--   right-< (R ⨁ Q) (inj₁ h) x h′ x′ p with right R (h , x) | inspect (right R) (h , x)
--   right-< (R ⨁ Q) (inj₁ h) x .(inj₁ h′) .x′ refl | inj₁ (h′ , x′) | Reveal_·_is_.[ eq ]
--     = step-⨁-inj₁ (right-< R h x h′ x′ eq)
--   right-< (R ⨁ Q) (inj₁ h) x h′ x′ () | inj₂ y | Reveal_·_is_.[ eq ]
--   right-< (R ⨁ Q) (inj₂ h) x h′ x′ p with right Q (h , x) | inspect (right Q) (h , x)
--   right-< (R ⨁ Q) (inj₂ h) x .(inj₂ h′) .x′ refl | inj₁ (h′ , x′) | Reveal_·_is_.[ eq ]
--     = step-⨁-inj₂ (right-< Q h x h′ x′ eq)
--   right-< (R ⨁ Q) (inj₂ h) x h′ x′ () | inj₂ y | eq
--   right-< (R ⨂ Q) (inj₁ (dr , q)) x h′ x′ p with right R (dr , x) | inspect (right R) (dr , x)
--   right-< (R ⨂ Q) (inj₁ (dr , q)) x .(inj₁ (dr′ , q)) .q′ refl | inj₁ (dr′ , q′) | Reveal_·_is_.[ eq ]
--     = step-⨂-inj₁ refl (right-< R dr x dr′ q′ eq)
--   right-< (R ⨂ Q) (inj₁ (dr , q)) x h′ x′ p | inj₂ r | Reveal_·_is_.[ eq ] with first Q q | inspect (first Q) q
--   right-< (R ⨂ Q) (inj₁ (dr , q)) x .(inj₂ (r , h′)) .x′ refl | inj₂ r | Reveal_·_is_.[ eq ] | just (h′ , x′) | Reveal_·_is_.[ eq₁ ]
--     = base-⨂ (×-injective-inv (right-preserves-plug₂ R dr x r eq , first-preserves-plug Q q h′ x′ eq₁))
--   right-< (R ⨂ Q) (inj₁ (dr , q)) x h′ x′ () | inj₂ r | Reveal_·_is_.[ eq ] | nothing | eq₁
--   right-< (R ⨂ Q) (inj₂ (r , dq)) x h′ x′ p with right Q (dq , x) | inspect (right Q) (dq , x)
--   right-< (R ⨂ Q) (inj₂ (r , dq)) x .(inj₂ (r , h′)) .x′ refl | inj₁ (h′ , x′) | Reveal_·_is_.[ eq ]
--     = step-⨂-inj₂ refl (right-< Q dq x h′ x′ eq)
--   right-< (R ⨂ Q) (inj₂ (r , dq)) x h′ x′ () | inj₂ y | Reveal_·_is_.[ eq ]
-- --   ⊎-injective₁ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
--  --   ⊎-injective₁ refl = refl

-- --   ⊎-injective₂ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
-- --   ⊎-injective₂ refl = refl

-- --   ⊎-injective₁-inv : ∀ {A B : Set} {x y} → x ≡ y → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y
-- --   ⊎-injective₁-inv refl = refl

-- --   ⊎-injective₂-inv : ∀ {A B : Set} {x y} → x ≡ y → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y
-- --   ⊎-injective₂-inv refl = refl
 
-- --   ×-injective : ∀ {A B : Set} {x y a b} → (A × B ∋ (x , y)) ≡ (a , b) → x ≡ a × y ≡ b
-- --   ×-injective refl = refl , refl

-- --   plug-injective : ∀ {X : Set} → (R : Reg)
-- --                  → (r : ⟦ ∇ R ⟧₂ X X) → (x y : X) → plug R r x ≡ plug R r y → x ≡ y
-- --   plug-injective 0′ () x y p
-- --   plug-injective 1′ () x y p
-- --   plug-injective V r x .x refl = refl
-- --   plug-injective (R ⨁ Q) (inj₁ x₁) x y p = plug-injective R x₁ x y (⊎-injective₁ p)
-- --   plug-injective (R ⨁ Q) (inj₂ y₁) x y p = plug-injective Q y₁ x y (⊎-injective₂ p)
-- --   plug-injective (R ⨂ Q) (inj₁ (a , b)) x y p  = plug-injective R a x y (proj₁ (×-injective p))
-- --   plug-injective (R ⨂ Q) (inj₂ (a , b)) x y p  = plug-injective Q b x y (proj₂ (×-injective p))

-- --   -- plug is not injective in both arguments
-- --   plug-injective₂ : ∀ {X : Set} → (R : Reg)
-- --                  → (r q : ⟦ ∇ R ⟧₂ X X) → (x y : X) → plug R r x ≡ plug R q y → x ≡ y × r ≡ q
-- --   plug-injective₂ 0′ () q x y p
-- --   plug-injective₂ 1′ () q x y p
-- --   plug-injective₂ V tt tt x .x refl = refl , refl
-- --   plug-injective₂ (R ⨁ Q) (inj₁ x₁) (inj₁ x₂) x y p with plug-injective₂ R x₁ x₂ x y (⊎-injective₁ p)
-- --   plug-injective₂ (R ⨁ Q) (inj₁ x₁) (inj₁ .x₁) x .x p | refl , refl = refl , refl
-- --   plug-injective₂ (R ⨁ Q) (inj₁ x₁) (inj₂ y₁) x y ()
-- --   plug-injective₂ (R ⨁ Q) (inj₂ y₁) (inj₁ x₁) x y ()
-- --   plug-injective₂ (R ⨁ Q) (inj₂ y₁) (inj₂ y₂) x y p with plug-injective₂ Q y₁ y₂ x y (⊎-injective₂ p)
-- --   plug-injective₂ (R ⨁ Q) (inj₂ y₁) (inj₂ .y₁) x .x p | refl , refl = refl , refl
-- --   plug-injective₂ (R ⨂ Q) (inj₁ (proj₃ , proj₄)) (inj₁ (proj₅ , proj₆)) x y p = {!!}
-- --   plug-injective₂ (R ⨂ Q) (inj₁ (proj₃ , .(plug Q proj₆ y))) (inj₂ (.(plug R proj₃ x) , proj₆)) x y refl = {!!}
-- --   plug-injective₂ (R ⨂ Q) (inj₂ y₁) q x y p = {!!}

-- --   plug-⊳ : (R : Reg) → Zipper R → μ R
-- --   plug-⊳ R (t , s) = plug-μ R t s

-- -- -- the good one

-- --   data IsInj₂ {X Y : Set} : (R : Reg) → ⟦ ∇ R ⟧₂ X Y → Set where
-- --     isInj₂-⨁-inj₁ : ∀ (R Q : Reg) x → IsInj₂ R x → IsInj₂ (R ⨁ Q) (inj₁ x) 
-- --     isInj₂-⨁-inj₂ : ∀ (R Q : Reg) y → IsInj₂ Q y → IsInj₂ (R ⨁ Q) (inj₂ y)
-- --     isInj₂-⨂      : ∀ (R Q : Reg) x → IsInj₂ (R ⨂ Q) (inj₂ x)

-- --   -- By construction now the relation makes sure that they plug onto the same
-- --   -- value. It gives an order between the possible templates from a Code.
-- --   data nltReg {X : Set} : (R : Reg) → (⟦ ∇ R ⟧₂ X X × X) → (⟦ ∇ R ⟧₂ X X × X) → Set where
-- --     step-⨂-inj₁ : ∀ {R Q} {dr dr′ q q′} {t₁ t₂}
-- --                  → q ≡ q′
-- --                  → nltReg R (dr , t₁) (dr′ , t₂)             
-- --                  → nltReg  ( R ⨂ Q ) (inj₁ (dr , q) , t₁) (inj₁ (dr′ , q′) , t₂)

-- --     step-⨂-inj₂ : ∀ {R Q} {dq dq′ r r′} {t₁ t₂}
-- --                  → r ≡ r′
-- --                  → nltReg Q (dq , t₁) (dq′ , t₂)
-- --                  → nltReg ( R ⨂ Q ) (inj₂ (r , dq) , t₁) (inj₂ (r′ , dq′) , t₂)

-- --     base-⨂      : ∀ {R Q : Reg} {x y} {t₁ t₂}
-- --                  → plug (R ⨂ Q) (inj₂ x) t₁ ≡ plug (R ⨂ Q) (inj₁ y) t₂
-- --                  → nltReg (R ⨂ Q) (inj₂ x , t₁) (inj₁ y , t₂)

-- --     step-⨁-inj₂ : ∀ {R Q} {x y} {t₁ t₂}
-- --                  → nltReg Q (x , t₁) (y , t₂)
-- --                  → nltReg (R ⨁ Q) (inj₂ x , t₁) (inj₂ y , t₂)

-- --     step-⨁-inj₁ : ∀ {R Q} {x y} {t₁ t₂}
-- --                  → nltReg R (x , t₁) (y , t₂)
-- --                  → nltReg (R ⨁ Q) (inj₁ x , t₁) (inj₁ y , t₂)

-- --   -- this relation embodies equality and ordering with respect to the diff r code
-- --   data IsInj₁ {X Y : Set} : (R : Reg) → ⟦ ∇ R ⟧₂ X Y → Set where
-- --     isInj₁-⨁-inj₁ : ∀ (R Q : Reg) x → IsInj₁ R x → IsInj₁ (R ⨁ Q) (inj₁ x) 
-- --     isInj₁-⨁-inj₂ : ∀ (R Q : Reg) y → IsInj₁ Q y → IsInj₁ (R ⨁ Q) (inj₂ y)
-- --     isInj₁-⨂      : ∀ (R Q : Reg) x → IsInj₁ (R ⨂ Q) (inj₁ x)

-- --   nltReg-related : ∀ {X : Set} (R : Reg) → (x y : ⟦ ∇ R ⟧₂ X X) → (t₁ t₂ : X)
-- --                  → nltReg R (x , t₁) (y , t₂) → plug R x t₁ ≡ plug R y t₂
-- --   nltReg-related .(_ ⨂ _) .(inj₁ (_ , _)) .(inj₁ (_ , _)) t₁ t₂ (step-⨂-inj₁ refl p) = cong (_, _)  (nltReg-related _ _ _ t₁ t₂ p)
-- --   nltReg-related .(_ ⨂ _) .(inj₂ (_ , _)) .(inj₂ (_ , _)) t₁ t₂ (step-⨂-inj₂ refl p) = cong (_,_ _) (nltReg-related _ _ _ t₁ t₂ p)
-- --   nltReg-related .(_ ⨂ _) .(inj₂ _) .(inj₁ _) t₁ t₂ (base-⨂ p) = p
-- --   nltReg-related .(_ ⨁ _) .(inj₂ _) .(inj₂ _) t₁ t₂ (step-⨁-inj₂ p) = ⊎-injective₂-inv (nltReg-related _ _ _ t₁ t₂ p)
-- --   nltReg-related .(_ ⨁ _) .(inj₁ _) .(inj₁ _) t₁ t₂ (step-⨁-inj₁ p) = ⊎-injective₁-inv (nltReg-related _ _ _ t₁ t₂ p)

-- --   nltReg-WF : ∀ {X : Set} (R : Reg) → Well-founded (nltReg {X} R)
-- --   nltReg-WF R x = acc (aux R x)
-- --     where aux : ∀ {X} (R : Reg) (x : Σ (⟦ ∇ R ⟧₂ X X) (λ x₁ → X))
-- --                   (y : Σ (⟦ ∇ R ⟧₂ X X) (λ x₁ → X)) → nltReg R y x → Acc (nltReg R) y
-- --           aux .(R ⨂ Q) (.(inj₁ (dr′ , q)) , x) (.(inj₁ (dr , q)) , y) (step-⨂-inj₁ {R} {Q} {dr} {dr′} {q} refl p) = {!!}
-- --           aux .(_ ⨂ _) (.(inj₂ (_ , _)) , x) (.(inj₂ (_ , _)) , y) (step-⨂-inj₂ x₂ p) = {!!}
-- --           aux .(_ ⨂ _) (.(inj₁ _) , x) (.(inj₂ _) , y) (base-⨂ x₃) = {!!}
-- --           aux .(_ ⨁ _) (.(inj₂ _) , x) (.(inj₂ _) , y) (step-⨁-inj₂ p) = {!!}
-- --           aux .(_ ⨁ _) (.(inj₁ _) , x) (.(inj₁ _) , y) (step-⨁-inj₁ p) = {!!}
          
-- --   -- A reification as an inductive type of the plug function
-- --   data Plug {X : Set} : (R : Reg) → (⟦ ∇ R ⟧₂ X X × X) → ⟦ R ⟧ X → Set where
-- --     step-⨁-inj₁ : ∀ {R Q} {x y} {t}
-- --                  → Plug R (x , t) y            
-- --                  → Plug (R ⨁ Q) (inj₁ x , t) (inj₁ y)

-- --     step-⨁-inj₂ : ∀ {R Q} {x y} {t}
-- --                  → Plug Q (x , t) y            
-- --                  → Plug (R ⨁ Q) (inj₂ x , t) (inj₂ y)

-- --     step-⨂-inj₁ : ∀ {R Q} {r dr q q′} {t}
-- --                  → q ≡ q′
-- --                  → Plug R (dr , t) r
-- --                  → Plug (R ⨂ Q) (inj₁ (dr , q′) , t) (r , q)

-- --     step-⨂-inj₂ : ∀ {R Q} {r r′ q dq} {t}
-- --                  → r ≡ r′
-- --                  → Plug Q (dq , t) q
-- --                  → Plug (R ⨂ Q) (inj₂ (r′ , dq) , t) (r , q)

-- --     base         : ∀ {y} {t} → t ≡ y → Plug V (tt , t) y

-- --   plugView : ∀ {X : Set} (R : Reg) → (x : ⟦ ∇ R ⟧₂ X X) → (t : X) → (y : ⟦ R ⟧ X) →
-- --             plug R x t ≡ y → Plug R (x , t) y
-- --   plugView 0′ () t y p
-- --   plugView 1′ () t y p
-- --   plugView V tt t .t refl = base refl
-- --   plugView (R ⨁ Q) (inj₁ x) t (inj₁ x₁) p = step-⨁-inj₁ (plugView R x t x₁ (⊎-injective₁ p))
-- --   plugView (R ⨁ Q) (inj₁ x) t (inj₂ y) ()
-- --   plugView (R ⨁ Q) (inj₂ y₁) t (inj₁ x) ()
-- --   plugView (R ⨁ Q) (inj₂ y₁) t (inj₂ y) p = step-⨁-inj₂ (plugView Q y₁ t y (⊎-injective₂ p))
-- --   plugView (R ⨂ Q) (inj₁ (r , dq)) t (pr , dq′) p = step-⨂-inj₁ (sym (proj₂ (×-injective p))) (plugView R r t pr (proj₁ (×-injective p)))
-- --   plugView (R ⨂ Q) (inj₂ (dr , q)) t (dr′ , pq) p = step-⨂-inj₂ (sym (proj₁ (×-injective p))) (plugView Q q t pq (proj₂ (×-injective p)))

-- --   Plug-related : ∀ {X : Set} (R : Reg) → (x : ⟦ ∇ R ⟧₂ X X) → (t : X) → (y : ⟦ R ⟧ X)
-- --                → Plug R (x , t) y → plug R x t ≡ y
-- --   Plug-related .(_ ⨁ _) .(inj₁ _) t .(inj₁ _) (step-⨁-inj₁ p) = ⊎-injective₁-inv (Plug-related _ _ t _ p)
-- --   Plug-related .(_ ⨁ _) .(inj₂ _) t .(inj₂ _) (step-⨁-inj₂ p) = ⊎-injective₂-inv (Plug-related _ _ t _ p)
-- --   Plug-related .(_ ⨂ _) .(inj₁ (_ , q′)) t .(_ , q′) (step-⨂-inj₁ {q′ = q′} refl p) = cong (_, q′) (Plug-related _ _ t _ p)
-- --   Plug-related .(_ ⨂ _) .(inj₂ (r′ , _)) t .(r′ , _) (step-⨂-inj₂ {r′ = r′} refl p) = cong (_,_ r′) (Plug-related _ _  t _ p) 
-- --   Plug-related .V .tt t y (base x) = x


-- --   first : ∀ {X Y : Set} → (R : Reg) → ⟦ R ⟧ X → (⟦ R ⟧ Y ⊎ (⟦ ∇ R ⟧₂ Y X × X))
-- --   first 0′ ()
-- --   first 1′ tt = inj₁ tt
-- --   first V x   = inj₂ (tt , x)
-- --   first (R ⨁ Q) (inj₁ x) with first R x
-- --   first (R ⨁ Q) (inj₁ x) | inj₂ (dr , x′)  = inj₂ (inj₁ dr , x′)
-- --   first (R ⨁ Q) (inj₁ x) | inj₁ em         = inj₁ (inj₁ em)
-- --   first (R ⨁ Q) (inj₂ y) with first Q y
-- --   first (R ⨁ Q) (inj₂ y) | inj₂ (dq , y′)  = inj₂ (inj₂ dq , y′)
-- --   first (R ⨁ Q) (inj₂ y) | inj₁ em         = inj₁ (inj₂ em)
-- --   first (R ⨂ Q) (r , q) with first R r
-- --   first (R ⨂ Q) (r , q) | inj₂ (dr , x) = inj₂ ((inj₁ (dr , q)) , x)
-- --   first (R ⨂ Q) (r , q) | inj₁ em₁ with first Q q
-- --   first (R ⨂ Q) (r , q) | inj₁ em₁ | inj₂ (dr , x)  = inj₂ (inj₂ (em₁ , dr) , x)
-- --   first (R ⨂ Q) (r , q) | inj₁ em₁ | inj₁ em₂       = inj₁ (em₁ , em₂)



-- --   {- We would like to be more precise on the types and say that if there is no hole then we can return a ⟦ R ⟧ Y for any Y
-- --      in the spirit of parametric polymorphism. -}
-- --   mutual
-- --     first-cps : ∀ {X : Set} {Result : Set} → (R : Reg) → ⟦ R ⟧ X → (X → ⟦ ∇ R ⟧₂ X X → Maybe Result) → Maybe Result
-- --     first-cps 0′ () k
-- --     first-cps 1′ tt k = nothing
-- --     first-cps V x k   = k x tt
-- --     first-cps (R ⨁ Q) (inj₁ x) k = first-cps R x (λ x i → k x (inj₁ i))
-- --     first-cps (R ⨁ Q) (inj₂ y) k = first-cps Q y (λ x i → k x (inj₂ i))
-- --     first-cps (R ⨂ Q) (x , y) k  = first-cps R x (λ x i → k x (inj₁ (i , y))) <|> first-cps Q y (λ y i → k y (inj₂ (x , i)))
-- --       where _<|>_ : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
-- --             just x  <|> y = just x
-- --             nothing <|> y = y

-- --     first-μ : ∀ {X : Set} {Result : Set} → (R : Reg) → μ R → List (⟦ ∇ R ⟧₂ (μ R) (μ R)) → Maybe Result
-- --     first-μ {X} R (In x) cs = first-cps R x (λ x c → first-μ R {!x!} (c ∷ cs))
-- --     --                ^                        ^
-- --     -- the x bound by the lambda is not structurally smaller than the original x


-- --   data lt : (R : Reg) → Zipper R → Zipper R → Set where
-- --     step-⨂-inj₁ : ∀ {R Q} {dr dr′ q q′} {t₁ t₂}
-- --                  → q ≡ q′
-- --                  → nltReg R (dr , t₁) (dr′ , t₂)             
-- --                  → nltReg  ( R ⨂ Q ) (inj₁ (dr , q) , t₁) (inj₁ (dr′ , q′) , t₂)

-- --     step-⨂-inj₂ : ∀ {R Q} {dq dq′ r r′} {t₁ t₂}
-- --                  → r ≡ r′
-- --                  → nltReg Q (dq , t₁) (dq′ , t₂)
-- --                  → nltReg ( R ⨂ Q ) (inj₂ (r , dq) , t₁) (inj₂ (r′ , dq′) , t₂)

-- --     base-⨂      : ∀ {R Q : Reg} {x y} {t₁ t₂}
-- --                  → plug (R ⨂ Q) (inj₂ x) t₁ ≡ plug (R ⨂ Q) (inj₁ y) t₂
-- --                  → nltReg (R ⨂ Q) (inj₂ x , t₁) (inj₁ y , t₂)

-- --     step-⨁-inj₂ : ∀ {R Q} {x y} {t₁ t₂}
-- --                  → nltReg Q (x , t₁) (y , t₂)
-- --                  → nltReg (R ⨁ Q) (inj₂ x , t₁) (inj₂ y , t₂)

-- --     step-⨁-inj₁ : ∀ {R Q} {x y} {t₁ t₂}
-- --                  → nltReg R (x , t₁) (y , t₂)
-- --                  → nltReg (R ⨁ Q) (inj₁ x , t₁) (inj₁ y , t₂)


-- --     lt-step  : ∀ {R} {t₁ t₂ x s₁ s₂} →  lt R (t₁ , s₁) (t₂ , s₂)                    → lt R (t₁ , x ∷ s₁) (t₂ , x ∷ s₂)
-- --   --  lt-base  : ∀ {R} {t₁ t₂ x y s₁ s₂}  → nltReg R (y , plug-μ R t₂ s₂) (x , plug-μ R t₁ s₁)  → lt R (t₂ , y ∷ s₂) (t₁ , x ∷ s₁)

-- --   {- We need to do induction on R because we need to pattern match on the top of the list
-- --      so plug can reduce by computation -}
-- --   -- related : (R : Reg) → (x y : Zipper R) → lt R x y → plug-⊳ R x ≡ plug-⊳ R y
-- --   -- related 0′ (a , s) (b , s′) p = {!!}
-- --   -- related 1′ (a , s) (b , s′) p = {!!}
-- --   -- related V (.(In _) , .[]) (b , .(_ ∷ _)) (lt-left x ())
-- --   -- related V (a , .(_ ∷ _)) (.(In _) , .[]) (lt-right x ())
-- --   -- related V (a , .(tt ∷ s₁)) (b , .(tt ∷ s₂)) (lt-step {x = tt} {s₁ = s₁} {s₂} refl p) = {!!}
-- --   -- related V (a , .(y ∷ s₂)) (b , .(x ∷ s₁)) (lt-base {x = x} {y} {s₁} {s₂} p) = {!!}
-- --   -- related (R ⨁ Q) (.(In _) , .[]) (b , .(inj₁ x ∷ s₂)) (lt-left {s = inj₁ x} {s₂} p isI)
-- --   --   with Plug-related (R ⨁ Q) (inj₁ x) _ _ p
-- --   -- ...  | refl = refl
-- --   -- related (R ⨁ Q) (.(In _) , .[]) (b , .(inj₂ y ∷ s₂)) (lt-left {s = inj₂ y} {s₂} p isI)
-- --   --   with Plug-related (R ⨁ Q) (inj₂ y) _ _ p
-- --   -- ...  | refl = refl
-- --   -- related (R ⨁ Q) (a , .(inj₁ x ∷ s₁)) (.(In _) , .[]) (lt-right {s = inj₁ x} {s₁} p isI)
-- --   --   with Plug-related (R ⨁ Q) (inj₁ x) _ _ p
-- --   -- ... | refl = refl
-- --   -- related (R ⨁ Q) (a , .(inj₂ y ∷ s₁)) (.(In _) , .[]) (lt-right {s = inj₂ y} {s₁} p isI)
-- --   --   with Plug-related (R ⨁ Q) (inj₂ y) _ _ p
-- --   -- ... | refl = refl
-- --   -- related (R ⨁ Q) (a , .(inj₁ x ∷ s₁)) (b , .(inj₁ x ∷ s₂)) (lt-step {x = inj₁ x} {s₁ = s₁} {s₂} refl p)
-- --   --  = cong (In ∘ inj₁ ∘ plug R x) (related (R ⨁ Q) (a  , s₁) (b , s₂) p)
-- --   -- related (R ⨁ Q) (a , .(inj₂ y ∷ s₁)) (b , .(inj₂ y ∷ s₂)) (lt-step {x = inj₂ y} {s₁ = s₁} {s₂} refl p)
-- --   --  = cong (In ∘ inj₂ ∘ plug Q y) (related (R ⨁ Q) (a , s₁) (b , s₂) p)
-- --   -- related (R ⨁ Q) (a , .(inj₂ x ∷ s₂)) (b , .(inj₂ y ∷ s₁)) (lt-base {x = .(inj₂ y)} {.(inj₂ x)} {s₁} {s₂} (step-⨁-inj₂ {x = x} {y} p)) = {!!}
-- --   -- related (R ⨁ Q) (a , .(inj₁ x ∷ s₂)) (b , .(inj₁ y ∷ s₁)) (lt-base {x = .(inj₁ y)} {.(inj₁ x)} {s₁} {s₂} (step-⨁-inj₁ {x = x} {y} p)) = {!!}
-- --   -- --  with nltReg-related R x y (plug-μ (R ⨁ Q) b s₁) (plug-μ (R ⨁ Q) a s₂) p 
-- --   -- -- ... | z =  {!!}
-- --   -- related (R ⨂ R₁) (.(In _) , .[]) (b , .(_ ∷ _)) (lt-left x x₁) = {!!}
-- --   -- related (R ⨂ R₁) (a , .(_ ∷ _)) (.(In _) , .[]) (lt-right x x₁) = {!!}
-- --   -- related (R ⨂ R₁) (a , .(_ ∷ _)) (b , .(_ ∷ _)) (lt-step x₁ p) = {!!}
-- --   -- related (R ⨂ R₁) (a , .(_ ∷ _)) (b , .(_ ∷ _)) (lt-base x₁) = {!!}

-- --   binF : Reg
-- --   binF = (V ⨂ V) ⨁ 1′

-- --   z₁ : Zipper binF
-- --   z₁ = (In (inj₂ tt)) , inj₁ (inj₁ (tt , In (inj₂ tt))) ∷ []

-- --   z₂ : Zipper binF
-- --   z₂ = (In (inj₂ tt) , (inj₁ (inj₂ ((In (inj₂ tt)) , tt))) ∷ [])

-- --   z₃ : Zipper binF
-- --   z₃ = (In (inj₁ (In (inj₂ tt) , In (inj₂ tt)))) , []
  
-- --   Proof : lt binF z₂ z₁
-- --   Proof = lt-base (step-⨁-inj₁ (base-⨂ refl))
  
-- --   data IRel (R : Reg) (t : μ R) : Zipper R → Zipper R → Set where
-- --     iRel : ∀ z₁ z₂ → plug-⊳ R z₁ ≡ t
-- --                    → plug-⊳ R z₂ ≡ t
-- --                    → lt R z₁ z₂ → IRel R t z₁ z₂
-- --   mutual

-- --     acc-⨁-inj₁ : ∀ R Q x a s₁ → Acc (IRel (R ⨁ Q) (plug-μ (R ⨁ Q) a s₁)) (a , s₁)
-- --                                → WfRec (IRel (R ⨁ Q) (In (inj₁ (plug R x (plug-μ (R ⨁ Q) a s₁)))))
-- --                                         (Acc (IRel (R ⨁ Q) (In (inj₁ (plug R x (plug-μ (R ⨁ Q) a s₁)))))) (a , inj₁ x ∷ s₁)
-- --     acc-⨁-inj₁ R Q x a s (acc rs) (y , .(inj₁ x ∷ s₁)) (iRel .(y , inj₁ x ∷ s₁) .(a , inj₁ x ∷ s) eq₁ eq₂ (lt-step {s₁ = s₁} refl p))
-- --       with plug-μ (R ⨁ Q) a s | plug-injective R x (plug-μ (R ⨁ Q) a s) (plug-μ (R ⨁ Q) y s₁) ((⊎-injective₁ (In-injective (sym eq₁))))
-- --     acc-⨁-inj₁ R Q x a s (acc rs) (y , .(inj₁ x ∷ s₁)) (iRel .(y , inj₁ x ∷ s₁) .(a , inj₁ x ∷ s) eq₁ eq₂ (lt-step {s₁ = s₁} refl p))
-- --       | .(plug-μ (R ⨁ Q) y s₁) | refl
-- --       = acc (acc-⨁-inj₁ R Q x y s₁ (rs (y , s₁) (iRel (y , s₁) (a , s) refl {!!} p)))             -- We need to remember the equality but is done
-- --     acc-⨁-inj₁ R Q c a s (acc rs) (b , .(inj₁ x ∷ s₂)) (iRel .(b , inj₁ x ∷ s₂) .(a , inj₁ c ∷ s) eq₁ refl (lt-base {y = .(inj₁ x)} {s₂ = s₂} (step-⨁-inj₁ {x = x} p)))
-- --       with plug R c (plug-μ (R ⨁ Q) a s) | sym eq₁
-- --     acc-⨁-inj₁ R Q c a s (acc rs) (b , .(inj₁ x ∷ s₂)) (iRel .(b , inj₁ x ∷ s₂) .(a , inj₁ c ∷ s) eq₁ refl (lt-base {_} {_} {_} {_} {.(inj₁ x)} {s₂ = s₂} (step-⨁-inj₁ {x = x} p))) | .(plug R x (plug-μ (R ⨁ Q) b s₂)) | refl = acc (acc-⨁-inj₁ R Q x b s₂ {!IRel-WF ? ? ? !}) -- acc (acc-⨁-inj₁ R Q x b s₂ {!IRel-WF ? ? ?!})

-- --     -- acc-impl : ∀ (R : Reg) t b a → Acc (IRel R (In (plug R b t))) a → WfRec (IRel R t) (Acc (IRel R t)) a
-- --     -- acc-impl R t b (_ , _) (acc rs) (b , .(x₄ ∷ _)) (iRel .(b , x₄ ∷ _) .(_ , x₄ ∷ _) x₁ x₂ (lt-step {x = x₄} refl x₃)) = {!.s₁!}
-- --     -- acc-impl R t b (_ , _) (acc rs) (b , .(_ ∷ _)) (iRel .(b , _ ∷ _) .(_ , _ ∷ _) x₁ x₂ (lt-base x₄)) = {!!}

-- --     IRel-WF : (R : Reg) → (t : μ R) → Well-founded (IRel R t)
-- --     IRel-WF R t x = acc (aux R t x)
-- --       where aux : (R : Reg) → (t : μ R) → (x : Zipper R) → WfRec (IRel R t) (Acc (IRel R t)) x
-- --             aux R t (x , .(_ ∷ s₂)) (y , .(_ ∷ s₁)) (iRel .(y , _ ∷ s₁) .(x , _ ∷ s₂) eq₁ eq₂ (lt-step {s₁ = s₁} {s₂} x₃ p)) = {!!}
-- --             aux 0′ t (a , .(x ∷ s₁)) (b , .(y ∷ s₂)) (iRel .(b , y ∷ s₂) .(a , x ∷ s₁) eq₁ eq₂ (lt-base {x = x} {y} {s₁} {s₂} p)) = {!!}
-- --             aux 1′ t (a , .(x ∷ s₁)) (b , .(y ∷ s₂)) (iRel .(b , y ∷ s₂) .(a , x ∷ s₁) eq₁ eq₂ (lt-base {x = x} {y} {s₁} {s₂} p)) = {!!}
-- --             aux V t (a , .(x ∷ s₁)) (b , .(y ∷ s₂)) (iRel .(b , y ∷ s₂) .(a , x ∷ s₁) eq₁ eq₂ (lt-base {x = x} {y} {s₁} {s₂} p)) = {!!}
-- --             aux (R ⨁ Q) .(In (inj₁ (plug R x₁ (plug-μ (R ⨁ Q) b s₂)))) (a , .(inj₁ x ∷ s₁)) (b , .(inj₁ x₁ ∷ s₂)) (iRel .(b , inj₁ x₁ ∷ s₂) .(a , inj₁ x ∷ s₁) refl eq₂ (lt-base {x = inj₁ x} {inj₁ x₁} {s₁} {s₂} (step-⨁-inj₁ p))) = acc (acc-⨁-inj₁ R Q x₁ b s₂ {!IRel-WF  ? ? ?!})
         
-- --             aux (R ⨁ R₁) t (a , .(inj₁ x ∷ s₁)) (b , .(inj₂ y ∷ s₂)) (iRel .(b , inj₂ y ∷ s₂) .(a , inj₁ x ∷ s₁) eq₁ eq₂ (lt-base {x = inj₁ x} {inj₂ y} {s₁} {s₂} ()))
-- --             aux (R ⨁ R₁) t (a , .(inj₂ y₁ ∷ s₁)) (b , .(inj₁ x ∷ s₂)) (iRel .(b , inj₁ x ∷ s₂) .(a , inj₂ y₁ ∷ s₁) eq₁ eq₂ (lt-base {x = inj₂ y₁} {inj₁ x} {s₁} {s₂} p)) = {!!}
-- --             aux (R ⨁ Q) .(In (inj₂ (plug Q y (plug-μ (R ⨁ Q) b s₂)))) (a , .(inj₂ y₁ ∷ s₁)) (b , .(inj₂ y ∷ s₂)) (iRel .(b , inj₂ y ∷ s₂) .(a , inj₂ y₁ ∷ s₁) refl eq₂ (lt-base {x = inj₂ y₁} {inj₂ y} {s₁} {s₂} p)) = acc {!acc-⨁-inj!}  
            
-- --             aux (R ⨂ R₁) .(In (plug R dr (plug-μ (R ⨂ R₁) b s₂) , q)) (a , .(inj₁ (dr′ , q) ∷ s₁)) (b , .(inj₁ (dr , q) ∷ s₂)) (iRel .(b , inj₁ (dr , q) ∷ s₂) .(a , inj₁ (dr′ , q) ∷ s₁) refl eq₂ (lt-base {x = .(inj₁ (dr′ , q))} {.(inj₁ (dr , q))} {s₁} {s₂} (step-⨂-inj₁ {dr = dr} {dr′} {q} refl p))) = acc {!!}
-- --             aux (R ⨂ R₁) t (a , .(inj₂ (_ , _) ∷ s₁)) (b , .(inj₂ (_ , _) ∷ s₂)) (iRel .(b , inj₂ (_ , _) ∷ s₂) .(a , inj₂ (_ , _) ∷ s₁) eq₁ eq₂ (lt-base {x = .(inj₂ (_ , _))} {.(inj₂ (_ , _))} {s₁} {s₂} (step-⨂-inj₂ x₁ p))) = {!!}
-- --             aux (R ⨂ R₁) t (a , .(inj₁ _ ∷ s₁)) (b , .(inj₂ _ ∷ s₂)) (iRel .(b , inj₂ _ ∷ s₂) .(a , inj₁ _ ∷ s₁) eq₁ eq₂ (lt-base {x = .(inj₁ _)} {.(inj₂ _)} {s₁} {s₂} (base-⨂ x₂))) = {!!}
