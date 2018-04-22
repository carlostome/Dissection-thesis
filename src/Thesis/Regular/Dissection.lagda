\begin{code}
module Thesis.Regular.Dissection where

  open import Data.Product
  open import Data.Sum
  open import Data.Empty
  open import Data.Unit
  open import Thesis.Regular.Core
  open import Relation.Binary.PropositionalEquality
  open import Data.Maybe

  open import Induction.WellFounded
  
  ∇ : (R : Reg) → (Set → Set → Set)
  ∇ 0′ X Y = ⊥
  ∇ 1′ X Y = ⊥
  ∇ I X Y  = ⊤
  ∇ (K A) X Y = ⊥
  ∇ (R ⨁ Q) X Y = ∇ R X Y ⊎ ∇ Q X Y
  ∇ (R ⨂ Q) X Y = ∇ R X Y × ⟦ Q ⟧ Y ⊎ ⟦ R ⟧ X × ∇ Q X Y

  plug : ∀ {X : Set} → (R : Reg) → ∇ R X X → X → ⟦ R ⟧ X
  plug 0′ () x
  plug 1′ () x
  plug I tt x = x
  plug (K A) () x
  plug (u ⨁ v) (inj₁ u′) x  = inj₁ (plug u u′ x)
  plug (u ⨁ v) (inj₂ v′) x  = inj₂ (plug v v′ x)
  plug (u ⨂ v) (inj₁ (du , v′)) x = plug u du x  , v′
  plug (u ⨂ v) (inj₂ (u′ , dv)) x = u′           , plug v dv x

  data Plug {X : Set} : (R : Reg) → ∇ R X X → X → ⟦ R ⟧ X → Set where
    Plug-I : ∀ {x} → Plug I tt x x
    Plug-⨁-inj₁ : ∀ {R Q} {x} {r} {e}      → Plug R r x e  → Plug (R ⨁ Q) (inj₁ r) x (inj₁ e)
    Plug-⨁-inj₂ : ∀ {R Q} {x} {q} {e}      → Plug Q q x e  → Plug (R ⨁ Q) (inj₂ q) x (inj₂ e)
    Plug-⨂-inj₁ : ∀ {R Q} {x} {dr} {q} {e} → Plug R dr x e → Plug (R ⨂ Q) (inj₁ (dr , q)) x (e , q)
    Plug-⨂-inj₂ : ∀ {R Q} {x} {r} {dq} {e} → Plug Q dq x e → Plug (R ⨂ Q) (inj₂ (r , dq)) x (r , e)

  -- first : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → Maybe (∇ R X X × X)
  -- first 0′ ()
  -- first 1′ x    = nothing
  -- first I x     = just (tt , x)
  -- first (K A) x = nothing
  -- first (R ⨁ Q) (inj₁ r) with first R r
  -- first (R ⨁ Q) (inj₁ r) | just (rx , x) = just (inj₁ rx , x)
  -- first (R ⨁ Q) (inj₁ r) | nothing       = nothing
  -- first (R ⨁ Q) (inj₂ q) with first Q q
  -- first (R ⨁ Q) (inj₂ q) | just (qx , x) = just (inj₂ qx , x)
  -- first (R ⨁ Q) (inj₂ q) | nothing       = nothing
  -- first (R ⨂ Q) (r , q) with first R r
  -- first (R ⨂ Q) (r , q) | just (rx , x) = just (inj₁ (rx , q) , x)
  -- first (R ⨂ Q) (r , q) | nothing       with first Q q
  -- first (R ⨂ Q) (r , q) | nothing | just (qx , x) = just (inj₂ (r , qx) , x)
  -- first (R ⨂ Q) (r , q) | nothing | nothing       = nothing


    
  Plug-to-plug : {X : Set} → (R : Reg) → (h : ∇ R X X) → (x : X) → (r : ⟦ R ⟧ X) → Plug R h x r → plug R h x ≡ r
  Plug-to-plug .I .tt x .x Plug-I = refl
  Plug-to-plug .(R ⨁ _) .(inj₁ r) x .(inj₁ e) (Plug-⨁-inj₁ {R} {r = r} {e} p)             = cong inj₁ (Plug-to-plug R r x e p)
  Plug-to-plug .(_ ⨁ Q) .(inj₂ q) x .(inj₂ e) (Plug-⨁-inj₂ {Q = Q} {q = q} {e} p)         = cong inj₂ (Plug-to-plug Q q x e p)
  Plug-to-plug .(R ⨂ _) .(inj₁ (dr , q)) x .(e , q) (Plug-⨂-inj₁ {R} {dr = dr} {q} {e} p) = cong (λ x → (x , q)) (Plug-to-plug R dr x e p)
  Plug-to-plug .(_ ⨂ Q) .(inj₂ (r , dq)) x .(r , e) (Plug-⨂-inj₂ {Q = Q} {r = r} {dq} {e} p) = cong (λ x → (r , x)) (Plug-to-plug Q dq x e p)

  data ∇-Dec (R : Reg) (X : Set) (tₓ : ⟦ R ⟧ X) : Set where
    _,,_,,_ : (h : ∇ R X X) → (x : X) → Plug R h x tₓ → ∇-Dec R X tₓ

  data ∇-[[_,_,_]]_<_ (X : Set) : (R : Reg) → (tₓ : ⟦ R ⟧ X) → ∇-Dec R X tₓ → ∇-Dec R X tₓ → Set where
    step-⨂-inj₁ : ∀ {R Q} {r} {dr dr′ q} {t₁ t₂} {eq₁ eq₂}
                 → ∇-[[ X , R , r ]]          (dr ,, t₁ ,, eq₁) < (dr′ ,, t₂ ,, eq₂)             
                 → ∇-[[ X , R ⨂ Q , (r , q) ]] (inj₁ (dr , q) ,, t₁ ,, Plug-⨂-inj₁ eq₁) < (inj₁ (dr′ , q) ,, t₂ ,, Plug-⨂-inj₁ eq₂)

    step-⨂-inj₂ : ∀ {R Q} {q} {dq dq′ r} {t₁ t₂} {eq₁ eq₂}
                 → ∇-[[ X , Q , q ]]          (dq ,, t₁ ,, eq₁) < (dq′ ,, t₂ ,, eq₂)             
                 → ∇-[[ X , R ⨂ Q , (r , q) ]] (inj₂ (r , dq) ,, t₁ ,, Plug-⨂-inj₂ eq₁) < (inj₂ (r , dq′) ,, t₂ ,, Plug-⨂-inj₂ eq₂)

    base-⨂      : ∀ {R Q : Reg} {dr dq r q} {t₁ t₂} {eq₁ eq₂}
                 → ∇-[[ X , R ⨂ Q , (r , q) ]] (inj₂ (r , dq) ,, t₁ ,, eq₁) < (inj₁ (dr , q) ,, t₂ ,, eq₂)
    
    step-⨁-inj₂ : ∀ {R Q} {tq} {q q′} {t₁ t₂} eq₁ eq₂
                 → ∇-[[ X , Q , tq ]] (q ,, t₁ ,, eq₁) < (q′ ,, t₂ ,, eq₂)
                 → ∇-[[ X , R ⨁ Q , inj₂ tq ]] (inj₂ q ,, t₁ ,, Plug-⨁-inj₂ eq₁) < (inj₂ q′ ,, t₂ ,, Plug-⨁-inj₂ eq₂)

    step-⨁-inj₁ : ∀ {R Q} {tr} {r r′} {t₁ t₂} eq₁ eq₂
                 → ∇-[[ X , R , tr ]] (r ,, t₁ ,, eq₁) < (r′ ,, t₂ ,, eq₂)
                 → ∇-[[ X , R ⨁ Q , inj₁ tr ]] (inj₁ r ,, t₁ ,, Plug-⨁-inj₁ eq₁) < (inj₁ r′ ,, t₂ ,, Plug-⨁-inj₁ eq₂)

  acc-⨂-inj₂ : ∀ {X : Set} (R Q : Reg) (r : ⟦ R ⟧ X) (q : ⟦ Q ⟧ X) (dq : ∇ Q X X) (t : X) eq
              → Acc (∇-[[ X , Q , q ]]_<_) (dq ,, t ,, eq)
              → WfRec (∇-[[ X , R ⨂ Q , (r , q) ]]_<_) (Acc (∇-[[ X , R ⨂ Q , (r , q) ]]_<_))
                      (inj₂ (r , dq) ,, t ,, Plug-⨂-inj₂ eq)
  acc-⨂-inj₂ R Q r q dq t eq (acc rs) .(inj₂ (r , dq′) ,, t₁ ,, Plug-⨂-inj₂ eq₁) (step-⨂-inj₂ {dq = dq′} {t₁ = t₁} {eq₁ = eq₁} p)
    = acc (acc-⨂-inj₂ R Q r q dq′ t₁ eq₁ (rs (dq′ ,, t₁ ,, eq₁) p))
      
  acc-⨂-inj₁ : ∀ {X : Set} (R Q : Reg) (dr : ∇ R X X) (t :  X) (r : ⟦ R ⟧ X) (q : ⟦ Q ⟧ X) eq
              → Well-founded (∇-[[ X , Q , q ]]_<_)
              → Acc (∇-[[ X , R , r ]]_<_) (dr ,, t ,,  eq)
              → WfRec (∇-[[ X , R ⨂ Q , (r , q) ]]_<_) (Acc (∇-[[ X , R ⨂ Q , (r , q) ]]_<_))
                      (inj₁ (dr , q) ,, t ,, Plug-⨂-inj₁ eq)
  acc-⨂-inj₁ R Q dr t r q eq wfq (acc rs) .(inj₁ (dr′ , q) ,, t₁ ,, Plug-⨂-inj₁ eq₁) (step-⨂-inj₁ {dr = dr′} {t₁ = t₁} {eq₁ = eq₁} p)
    = acc (acc-⨂-inj₁ R Q dr′ t₁ r q eq₁ wfq (rs (dr′ ,, t₁ ,, eq₁) p))
  acc-⨂-inj₁ R Q dr t r q eq wfq (acc rs) .(inj₂ (r , dq) ,, t₁ ,, Plug-⨂-inj₂ eq₁) (base-⨂ {dq = dq} {t₁ = t₁} {eq₁ = Plug-⨂-inj₂ eq₁})
    = acc (acc-⨂-inj₂ R Q r q dq t₁ eq₁ (wfq (dq ,, t₁ ,, eq₁)))

  acc-⨁-inj₂ : ∀ {X : Set} (R Q : Reg) (tq : ⟦ Q ⟧ X) (dq : ∇ Q X X) (t : X) eq
              → Acc (∇-[[ X , Q , tq ]]_<_) (dq ,, t ,, eq)
              → WfRec (∇-[[ X , R ⨁ Q , inj₂ tq ]]_<_) (Acc (∇-[[ X , R ⨁ Q , inj₂ tq ]]_<_)) (inj₂ dq ,, t ,, Plug-⨁-inj₂ eq)
  acc-⨁-inj₂ R Q tq dq t eq (acc rs) .(inj₂ q ,, t₁ ,, Plug-⨁-inj₂ eq₁) (step-⨁-inj₂ {q = q} {t₁ = t₁} eq₁ .eq p)
    = acc (acc-⨁-inj₂ R Q tq q t₁ eq₁ (rs (q ,, t₁ ,, eq₁) p))

  acc-⨁-inj₁ : ∀ {X : Set} (R Q : Reg) (tr : ⟦ R ⟧ X) (dr : ∇ R X X) (t : X) eq
              → Acc (∇-[[ X , R , tr ]]_<_) (dr ,, t ,, eq)
              → WfRec (∇-[[ X , R ⨁ Q , inj₁ tr ]]_<_) (Acc (∇-[[ X , R ⨁ Q , inj₁ tr ]]_<_)) (inj₁ dr ,, t ,,  Plug-⨁-inj₁ eq)
  acc-⨁-inj₁ R Q tr dr t eq (acc rs) .(inj₁ r ,, t₁ ,, Plug-⨁-inj₁ eq₁) (step-⨁-inj₁ {r = r} {t₁ = t₁} eq₁ .eq p)
    = acc (acc-⨁-inj₁ R Q tr r t₁ eq₁ (rs (r ,, t₁ ,, eq₁) p))

  ∇-WF : (X : Set) → (R : Reg) → (tₓ : ⟦ R ⟧ X) → Well-founded (∇-[[ X , R , tₓ ]]_<_)
  ∇-WF X R tₓ x = acc (aux R tₓ x)
    where
      aux : ∀ (R : Reg) (t : ⟦ R ⟧ X) (x : ∇-Dec R X t) → WfRec (∇-[[ X , R , t ]]_<_) (Acc (∇-[[ X , R , t ]]_<_)) x
      aux .(R ⨂ Q) .(r , q) .(inj₁ (dr′ , q) ,, t₂ ,, Plug-⨂-inj₁ eq₂) .(inj₁ (dr , q) ,, t₁ ,, Plug-⨂-inj₁ eq₁)
        (step-⨂-inj₁ {R} {Q} {r} {dr} {dr′} {q} {t₁} {t₂} {eq₁} {eq₂} p)
          = acc (acc-⨂-inj₁ R Q dr t₁ r q eq₁ (∇-WF X Q q) (aux R r (dr′ ,, t₂ ,, eq₂) (dr ,, t₁ ,, eq₁) p))
      aux .(R ⨂ Q) .(r , q) .(inj₂ (r , dq′) ,, t₂ ,, Plug-⨂-inj₂ eq₂) .(inj₂ (r , dq) ,, t₁ ,, Plug-⨂-inj₂ eq₁)
        (step-⨂-inj₂ {R} {Q} {q} {dq} {dq′} {r} {t₁} {t₂} {eq₁} {eq₂} p)
          = acc (acc-⨂-inj₂ R Q r q dq t₁ eq₁ (aux Q q (dq′ ,, t₂ ,, eq₂) (dq ,, t₁ ,, eq₁) p))
      aux .(R ⨂ Q) .(r , q) .(inj₁ (dr , q) ,, t₂ ,, eq₂) .(inj₂ (r , dq) ,, t₁ ,, Plug-⨂-inj₂ eq₁)
        (base-⨂ {R} {Q} {dr} {dq} {r} {q} {t₁} {t₂} {Plug-⨂-inj₂ eq₁} {eq₂})
          = acc (acc-⨂-inj₂ R Q r q dq t₁ eq₁ (∇-WF X Q q (dq ,, t₁ ,, eq₁)))
      aux .(R ⨁ Q) .(inj₂ tq) .(inj₂ q′ ,, t₂ ,, Plug-⨁-inj₂ eq₂) .(inj₂ q ,, t₁ ,, Plug-⨁-inj₂ eq₁)
        (step-⨁-inj₂ {R} {Q} {tq} {q}  {q′} {t₁} {t₂} eq₁ eq₂ p)
        = acc (acc-⨁-inj₂ R Q tq q t₁ eq₁ (aux Q tq (q′ ,, t₂ ,, eq₂) (q ,, t₁ ,, eq₁) p))
      aux .(R ⨁ Q) .(inj₁ tr) .(inj₁ r′ ,, t₂ ,, Plug-⨁-inj₁ eq₂) .(inj₁ r ,, t₁ ,, Plug-⨁-inj₁ eq₁)
        (step-⨁-inj₁ {R} {Q} {tr} {r} {r′} {t₁} {t₂} eq₁ eq₂ p)
        = acc (acc-⨁-inj₁ R Q tr r t₁ eq₁ (aux R tr (r′ ,, t₂ ,, eq₂) (r ,, t₁ ,, eq₁) p))
