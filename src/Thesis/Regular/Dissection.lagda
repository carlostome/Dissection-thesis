\begin{code}
module Thesis.Regular.Dissection where

  open import Data.Product
  open import Data.Sum
  open import Data.Empty
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality

  open import Induction.WellFounded

  open import Thesis.Regular.Core renaming (proof-irrelevance to Fmap-proof-irrelevance)
  -- Dissection operation
  ∇ : (R : Reg) → (Set → Set → Set)
  ∇ 0′ X Y = ⊥
  ∇ 1′ X Y = ⊥
  ∇ I X Y  = ⊤
  ∇ (K A) X Y = ⊥
  ∇ (R ⨁ Q) X Y = ∇ R X Y ⊎ ∇ Q X Y
  ∇ (R ⨂ Q) X Y = ∇ R X Y × ⟦ Q ⟧ Y ⊎ ⟦ R ⟧ X × ∇ Q X Y

  -- plug operation given a function to extract X values from
  -- the recursive positions to the left of the hole
  plug : ∀ {X Y : Set} (R : Reg) → (Y → X) → ∇ R Y X → X → ⟦ R ⟧ X
  plug 0′ ex () x
  plug 1′ ex () x
  plug I ex tt x = x
  plug (K A) ex () x
  plug (R ⨁ Q) ex (inj₁ u′) x  = inj₁ (plug R ex u′ x)
  plug (R ⨁ Q) ex (inj₂ v′) x  = inj₂ (plug Q ex v′ x)
  plug (R ⨂ Q) ex (inj₁ (du , v′)) x = plug R ex du x  , v′
  plug (R ⨂ Q) ex (inj₂ (u′ , dv)) x = fmap R ex u′           , plug Q ex dv x
  
  -- plug reified as a relation
  data Plug {X Y : Set} (ex : Y → X) : (R : Reg) → ∇ R Y X → X → ⟦ R ⟧ X → Set where
    Plug-I       : ∀ {x} → Plug ex I tt x x
    Plug-⨁-inj₁ : ∀ {R Q} {x} {r} {e}         → Plug ex R r x e  → Plug ex (R ⨁ Q) (inj₁ r) x (inj₁ e)
    Plug-⨁-inj₂ : ∀ {R Q} {x} {q} {e}         → Plug ex Q q x e  → Plug ex (R ⨁ Q) (inj₂ q) x (inj₂ e)
    Plug-⨂-inj₁ : ∀ {R Q} {x} {dr} {q} {e}    → Plug ex R dr x e → Plug ex (R ⨂ Q) (inj₁ (dr , q)) x (e , q)
    Plug-⨂-inj₂ : ∀ {R Q} {x} {r r′} {dq} {e} → Fmap ex R r r′   → Plug ex Q dq x e →  Plug ex (R ⨂ Q) (inj₂ (r , dq)) x (r′ , e)

  Dissection : (R : Reg) → (X Y : Set) → Set
  Dissection R X Y = ∇ R Y X × X

  PlugD : (R : Reg) (X Y : Set) → Dissection R X Y → (Y → X) → ⟦ R ⟧ X → Set
  PlugD R X Y (h , x) ex tₓ = Plug ex R h x tₓ
  
  -- UnIndexed smaller-than relation over Dissection
  data Lt (X Y : Set) : (R : Reg) → Dissection R X Y → Dissection R X Y → Set where
    step-⨂₁ : ∀ {R Q} {dr dr′ q} {t₁ t₂}
             → Lt X Y  R       (dr , t₁)            (dr′ , t₂)             
             → Lt X Y (R ⨂ Q) (inj₁ (dr , q) , t₁) (inj₁ (dr′ , q) , t₂)

    step-⨂₂ : ∀ {R Q} {dq dq′ r} {t₁ t₂}
             → Lt X Y Q        (dq , t₁)            (dq′ , t₂)             
             → Lt X Y (R ⨂ Q) (inj₂ (r , dq) , t₁) (inj₂ (r , dq′) , t₂)

    base-⨂      : ∀ {R Q : Reg} {dr dq r q} {t₁ t₂}
                 → Lt X Y (R ⨂ Q) (inj₂ (r , dq) , t₁)  (inj₁ (dr , q) , t₂)
    
    step-⨁₂ : ∀ {R Q} {q q′} {t₁ t₂}
             → Lt X Y  Q (q , t₁)  (q′ , t₂)
             → Lt X Y (R ⨁ Q) (inj₂ q , t₁) (inj₂ q′ , t₂)

    step-⨁₁ : ∀ {R Q} {r r′} {t₁ t₂}
             → Lt X Y  R       (r , t₁)      (r′ , t₂)
             → Lt X Y (R ⨁ Q) (inj₁ r , t₁) (inj₁ r′ , t₂)

  -- Type-Indexed Dissection
  data IxDissection (R : Reg) (X Y : Set) (ex : Y → X) (tₓ : ⟦ R ⟧ X) : Set₁ where
    _,_ : (d : Dissection R X Y) → PlugD R X Y d ex tₓ → IxDissection R X Y ex tₓ  
 

  -- Indexed relation over indexed dissections.
  data IxLt (X Y : Set) (ex : Y → X) : (R : Reg) → (tₓ : ⟦ R ⟧ X) → IxDissection R X Y ex tₓ → IxDissection R X Y ex tₓ → Set where
    step-⨂₁ : ∀ {R Q} {r} {dr dr′ q} {t₁ t₂} {eq₁ eq₂}
             → IxLt X Y ex R r              ((dr , t₁) , eq₁) ((dr′ , t₂) , eq₂)             
             → IxLt X Y ex (R ⨂ Q) (r , q) ((inj₁ (dr , q) , t₁) , Plug-⨂-inj₁ eq₁) ((inj₁ (dr′ , q) , t₂) , Plug-⨂-inj₁ eq₂)

    step-⨂₂ : ∀ {R Q} {q} {dq dq′ r r′} {t₁ t₂} {fr} {eq₁ eq₂}
             → IxLt X Y ex Q q   ((dq , t₁) , eq₁) ((dq′ , t₂) , eq₂)             
             → IxLt X Y ex (R ⨂ Q) (r , q) ((inj₂ (r′ , dq) , t₁) , Plug-⨂-inj₂ fr eq₁) ((inj₂ (r′ , dq′) , t₂) , Plug-⨂-inj₂ fr eq₂)

    base-⨂      : ∀ {R Q : Reg} {dr dq r r′ q} {t₁ t₂} {eq₁ eq₂}
                → IxLt X Y ex (R ⨂ Q) (r , q) ((inj₂ (r′ , dq) , t₁) , eq₁) ((inj₁ (dr , q) , t₂) , eq₂)
    
    step-⨁-inj₂ : ∀ {R Q} {tq} {q q′} {t₁ t₂} eq₁ eq₂
                 → IxLt X Y ex Q tq ((q , t₁) , eq₁) ((q′ , t₂) , eq₂)
                 → IxLt X Y ex (R ⨁ Q) (inj₂ tq) ((inj₂ q , t₁) , Plug-⨁-inj₂ eq₁) ((inj₂ q′ , t₂) , Plug-⨁-inj₂ eq₂)

    step-⨁-inj₁ : ∀ {R Q} {tr} {r r′} {t₁ t₂} eq₁ eq₂
                 → IxLt X Y ex R tr ((r , t₁) , eq₁) ((r′ , t₂) , eq₂)
                 → IxLt X Y ex (R ⨁ Q) (inj₁ tr) ((inj₁ r , t₁) , Plug-⨁-inj₁ eq₁) ((inj₁ r′ , t₂) , Plug-⨁-inj₁ eq₂)

  -- Given two dissections and a proof that they plug to a common value
  -- we can recover the indexed relation from the unindexed one
  Lt-to-LtIx : ∀ {X Y : Set} {ex : Y → X} {R : Reg} {tₓ : ⟦ R ⟧ X}
             → {d₁ d₂ : Dissection R X Y} → (eq₁ : PlugD R X Y d₁ ex tₓ) → (eq₂ : PlugD R X Y d₂ ex tₓ)
             → Lt X Y R d₁ d₂ → IxLt X Y ex R tₓ (d₁ , eq₁) (d₂ , eq₂)  
  Lt-to-LtIx (Plug-⨂-inj₁ eq₁)    (Plug-⨂-inj₁ eq₂)    (step-⨂₁ x) = step-⨂₁ (Lt-to-LtIx eq₁ eq₂ x)
  Lt-to-LtIx (Plug-⨂-inj₂ x₁ eq₁) (Plug-⨂-inj₂ x₂ eq₂) (step-⨂₂ x)
    with Fmap-proof-irrelevance x₁ x₂
  ... | refl = step-⨂₂ (Lt-to-LtIx eq₁ eq₂ x)
  Lt-to-LtIx (Plug-⨂-inj₂ x eq₁) (Plug-⨂-inj₁ eq₂) base-⨂    = base-⨂
  Lt-to-LtIx (Plug-⨁-inj₂ eq₁) (Plug-⨁-inj₂ eq₂) (step-⨁₂ x) = step-⨁-inj₂ eq₁ eq₂ (Lt-to-LtIx eq₁ eq₂ x)
  Lt-to-LtIx (Plug-⨁-inj₁ eq₁) (Plug-⨁-inj₁ eq₂) (step-⨁₁ x) = step-⨁-inj₁ eq₁ eq₂ (Lt-to-LtIx eq₁ eq₂ x)


  ---------------------------------------------------------------------------------------------------
  --                         IxLt is a well founded relation


  acc-⨂₂ : ∀ {X Y : Set} {ex : Y → X} (R Q : Reg) (r : ⟦ R ⟧ X) (r′ : ⟦ R ⟧ Y) (q : ⟦ Q ⟧ X) (dq : ∇ Q Y X) (t : X) eq fm
              → Acc (IxLt X Y ex Q q) ((dq , t) , eq)
              → WfRec (IxLt X Y ex (R ⨂ Q) (r , q)) (Acc (IxLt X Y ex (R ⨂ Q) (r , q)))
                      ((inj₂ (r′ , dq) , t) , Plug-⨂-inj₂ fm eq)
  acc-⨂₂ R Q r r′ q dq′ t eq fm (acc rs) .((inj₂ (r′ , dq) , t₁) , Plug-⨂-inj₂ fm eq₁) (step-⨂₂ {dq = dq} {t₁ = t₁} {eq₁ = eq₁} p)
    = acc (acc-⨂₂ R Q r r′ q dq t₁ eq₁ fm (rs ((dq , t₁) , eq₁) p))
  
  acc-⨂₁ : ∀ {X Y : Set} {ex : Y → X} (R Q : Reg) (dr : ∇ R Y X) (t :  X) (r : ⟦ R ⟧ X) (q : ⟦ Q ⟧ X) eq
              → Well-founded (IxLt X Y ex Q q)
              → Acc (IxLt X Y ex R r) ((dr , t) ,  eq)
              → WfRec (IxLt X Y ex (R ⨂ Q) (r , q)) (Acc (IxLt X Y ex (R ⨂ Q) (r , q)))
                      ((inj₁ (dr , q) , t) , Plug-⨂-inj₁ eq)
  acc-⨂₁ R Q dr t r q eq wf (acc rs) .((inj₁ (dr₁ , q) , t₁) , Plug-⨂-inj₁ eq₁) (step-⨂₁ {dr = dr₁} {t₁ = t₁} {eq₁ = eq₁} p)
    = acc (acc-⨂₁ R Q dr₁ t₁ r q eq₁ wf (rs ((dr₁ , t₁) , eq₁) p))
  acc-⨂₁ R Q dr t r q eq wf (acc rs) .((inj₂ (r′ , dq) , t₁) , Plug-⨂-inj₂ x eq₁) (base-⨂ {dq = dq} {r′ = r′} {t₁ = t₁} {eq₁ = Plug-⨂-inj₂ x eq₁})
    = acc (acc-⨂₂ R Q r r′ q dq t₁ eq₁ x (wf ((dq , t₁) , eq₁)) )

  acc-⨁₂ : ∀ {X Y : Set} {ex : Y → X} (R Q : Reg) (tq : ⟦ Q ⟧ X) (dq : ∇ Q Y X) (t : X) eq
          → Acc (IxLt X Y ex Q tq) ((dq , t) , eq)
          → WfRec (IxLt X Y ex (R ⨁ Q) (inj₂ tq)) (Acc (IxLt X Y ex (R ⨁ Q) (inj₂ tq))) ((inj₂ dq , t) , Plug-⨁-inj₂ eq)
  acc-⨁₂ R Q tq dq t eq (acc rs) .((inj₂ q , t₁) , Plug-⨁-inj₂ eq₁) (step-⨁-inj₂ {q = q} {t₁ = t₁} eq₁ .eq p)
    = acc (acc-⨁₂ R Q tq q t₁ eq₁ (rs ((q , t₁) , eq₁) p))

  acc-⨁₁ : ∀ {X Y : Set} {ex : Y → X} (R Q : Reg) (tr : ⟦ R ⟧ X) (dr : ∇ R Y X) (t : X) eq
          → Acc (IxLt X Y ex R tr) ((dr , t) , eq)
          → WfRec (IxLt X Y ex (R ⨁ Q) (inj₁ tr)) (Acc (IxLt X Y ex (R ⨁ Q) (inj₁ tr))) ((inj₁ dr , t) , Plug-⨁-inj₁ eq)
  acc-⨁₁ R Q tr dr t eq (acc rs) .((inj₁ r , t₁) , Plug-⨁-inj₁ eq₁) (step-⨁-inj₁ {r = r} {t₁ = t₁} eq₁ .eq p)
    = acc (acc-⨁₁ R Q tr r t₁ eq₁ (rs ((r , t₁) , eq₁) p))

  IxLt-WF : (X Y : Set) → (ex : Y → X) → (R : Reg) → (tₓ : ⟦ R ⟧ X) → Well-founded (IxLt X Y ex R tₓ)
  IxLt-WF X Y ex R tₓ x = acc (aux R tₓ x)
    where
      aux : ∀ (R : Reg) (t : ⟦ R ⟧ X) (x : IxDissection R X Y ex t) → WfRec (IxLt X Y ex R t) (Acc (IxLt X Y ex R t)) x
      aux .(R ⨂ Q) .(r , q) .((inj₁ (dr′ , q) , t₂) , Plug-⨂-inj₁ eq₂) .((inj₁ (dr , q) , t₁) , Plug-⨂-inj₁ eq₁)
        (step-⨂₁ {R} {Q} {r} {dr} {dr′} {q} {t₁} {t₂} {eq₁} {eq₂} p)
        = acc (acc-⨂₁ R Q dr t₁ r q eq₁ (IxLt-WF X Y ex Q q) (aux R r ((dr′ , t₂) , eq₂) ((dr , t₁) , eq₁) p))
      aux .(R ⨂ Q) .(r , q) .((inj₂ (r′ , dq′) , t₂) , Plug-⨂-inj₂ fr eq₂) .((inj₂ (r′ , dq) , t₁) , Plug-⨂-inj₂ fr eq₁)
        (step-⨂₂ {R} {Q} {q} {dq} {dq′} {r} {r′} {t₁} {t₂} {fr} {eq₁} {eq₂} p)
        = acc (acc-⨂₂ R Q r r′ q dq t₁ eq₁ fr (aux Q q ((dq′ , t₂) , eq₂) ((dq , t₁) , eq₁) p))
      aux .(R ⨂ Q) .(r , q) .((inj₁ (dr , q) , t₂) , eq₂) .((inj₂ (r′ , dq) , t₁) , Plug-⨂-inj₂ x eq₁)
        (base-⨂ {R} {Q} {dr} {dq} {r} {r′} {q} {t₁} {t₂} {Plug-⨂-inj₂ x eq₁} {eq₂})
        = acc (acc-⨂₂ R Q r r′ q dq t₁ eq₁ x (IxLt-WF X Y ex Q q ((dq , t₁) , eq₁) ))
      aux .(R ⨁ Q) .(inj₂ tq) .((inj₂ q′ , t₂) , Plug-⨁-inj₂ eq₂) .((inj₂ q , t₁) , Plug-⨁-inj₂ eq₁)
        (step-⨁-inj₂ {R} {Q} {tq} {q} {q′} {t₁} {t₂} eq₁ eq₂ p)
        = acc (acc-⨁₂ R Q tq q t₁ eq₁ (aux Q tq ((q′ , t₂) , eq₂) ((q , t₁) , eq₁) p))
      aux .(R ⨁ Q) .(inj₁ tr) .((inj₁ r′ , t₂) , Plug-⨁-inj₁ eq₂) .((inj₁ r , t₁) , Plug-⨁-inj₁ eq₁)
        (step-⨁-inj₁ {R} {Q} {tr} {r} {r′} {t₁} {t₂} eq₁ eq₂ p)
        = acc (acc-⨁₁ R Q tr r t₁ eq₁ (aux R tr ((r′ , t₂) , eq₂) ((r , t₁) , eq₁) p))