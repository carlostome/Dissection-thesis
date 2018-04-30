\begin{code}
module Thesis.Regular where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  open import Function
  open import Data.List
  open import Data.Nat
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Induction.WellFounded


  open import Thesis.Regular.Core
  open import Thesis.Regular.Equality
    renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Thesis.Regular.Dissection
    renaming ( Lt to Dissection-Lt
             ; IxLt to Dissection-IxLt
             ; Lt-to-IxLt to Dissection-Lt-to-IxLt
             ; IxLt-WF to Dissection-IxLt-WF
             ; proof-irrelevance to Plug-proof-irrelevance)
  open import Thesis.Regular.NonRec
    renaming (proof-irrelevance to NonRec-proof-irrelevance)
  open import Thesis.Regular.Catamorphism


  open import Thesis.Dissection.Core
  open import Thesis.Dissection.Load
  open import Thesis.Dissection.Unload


  


  propInit : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (l : ⟦ R ⟧ X) (isl : NonRec R l) → Catamorphism R alg (In (coerce l isl)) (alg l)
  propInit 0′ alg () isl
  propInit 1′ alg tt NonRec-1′          = Cata MapFold-1′
  propInit I alg l ()
  propInit (K A) alg l (NonRec-K .A .l) = Cata MapFold-K
  propInit (R ⨁ Q) alg .(inj₁ r) (NonRec-⨁-inj₁ .R .Q r isl) = {!!}
  propInit (R ⨁ Q) alg .(inj₂ q) (NonRec-⨁-inj₂ .R .Q q isl) = {!!}
  propInit (R ⨂ Q) alg (r , q) (NonRec-⨂ .R .Q _ _ isl₁ isl₂) with propInit R {!!} r isl₁ | propInit Q (λ x → alg (r , x)) q isl₂
  ... | z | zz = Cata (MapFold-⨂ {!z!} {!!})
  
  step : {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X)
       → UZipper R X alg → UZipper R X alg ⊎ X
  step R alg ((l , isl) , s) = unload R alg (In (coerce l isl)) (alg l) (propInit R alg l isl) s

  -- unload-Lt : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → ∀ (l : ⟦ R ⟧ X) (isl : NonRec R l) (l′ : Leaf R X) (s s′ : Stack R X alg) eq
  --           → unload R alg (In (coerce l isl)) (alg l) eq s ≡ inj₁ (l′ , s′) → Lt R X alg (l′ , reverse s′ ) ((l , isl) , reverse s)
  -- unload-Lt R alg l isl l′ [] s′ eq ()
  -- unload-Lt R alg l isl l′ (h ∷ hs) s′ eq x with right R R h (In (coerce l isl)) (alg l) eq | inspect (right R R h (In (coerce l isl)) (alg l)) eq
  -- unload-Lt R alg l isl l′ (h ∷ hs) s′ eq x | inj₁ x₁ | Is is = {!!}
  -- unload-Lt R alg l isl l′ (h ∷ hs) [] eq x | inj₂ (dr , mq) | Is is = {!!} -- bogus
  -- unload-Lt R alg l isl l′ (h ∷ hs) (h′ ∷ hs′) eq x | inj₂ (dr , mq) | Is is
  --   with reverse (h′ ∷ hs′) | unfold-reverse h′ hs′ | reverse (h ∷ hs) | unfold-reverse h hs
  -- unload-Lt R alg l isl l′ (h ∷ hs) (h′ ∷ hs′) eq x
  --   | inj₂ (dr , mq) | Is is | .(reverse hs′ ++ h′ ∷ []) | refl | .(reverse hs ++ h ∷ []) | refl = {!!}

  -- step-Lt : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → (l l′ : Leaf R X) (s s′ : Stack R X alg)
  --         → step R alg (l , s) ≡ inj₁ (l′ , s′) → Lt R X alg (l′ , reverse s′ ) (l , reverse s)
  -- step-Lt R alg (l , isl) l′ s s′ x = unload-Lt R alg l isl l′ s s′ {!!} x

  -- stepIx : ∀ {X : Set} → (R : Reg) → {t : μ R} → (alg : ⟦ R ⟧ X → X)
  --        → Zipper⇑ R X alg t → Zipper⇑ R X alg t ⊎ X
  -- stepIx R alg x = {!!}


  -- stepIx-Lt : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {t : μ R}
  --         → (z₁ z₂ : Zipper⇑ R X alg t) → stepIx R alg z₁ ≡ inj₁ z₂ → IxLt⇑ R X alg t z₂ z₁
  -- stepIx-Lt z₁ z₂ x = {!!}

  -- rec : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R)
  --     → (z : Zipper⇑ R X alg t) → Acc (IxLt⇑ R X alg t) z → X
  -- rec t z (acc rs) with stepIx t z | inspect (stepIx t) z
  -- rec t z (acc rs) | inj₁ x | Is eq  = rec t x (rs x (stepIx-Lt t z x eq))
  -- rec t z (acc rs) | inj₂ y | _      = y

 
  -- right-Lt : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} 
  --          → (dr  : ∇ R (Computed Q X alg) (μ Q)) → (t : μ Q)
  --          → (y : X) → (eq : Catamorphism Q alg t y)
  --          → (dr′ : ∇ R (Computed Q X alg) (μ Q)) → (t′ : μ Q)
  --          → right R Q dr t y eq ≡ inj₂ (dr′ , t′)
  --          → Dissection-Lt (μ Q) (Computed Q X alg) R ((dr′ , t′)) ((dr , t)) 
  -- right-Lt 0′ Q () t y eq dr′ t′ x
  -- right-Lt 1′ Q () t y eq dr′ t′ x
  -- right-Lt I Q tt t y eq dr′ t′ ()
  -- right-Lt (K A) Q () t y eq dr′ t′ x
  -- right-Lt (R ⨁ Q) P (inj₁ r) t y eq dr′ t′ p
  --   with right R P r t y eq | inspect (right R P r t y) eq
  -- right-Lt (R ⨁ Q) P (inj₁ r) t y eq dr′ t′ () | inj₁ x | Is is
  -- right-Lt (R ⨁ Q) P (inj₁ r) t y eq .(inj₁ dr′) .q refl
  --   | inj₂ (dr′ , q) | Is is = step-⨁₁ (right-Lt R P r t y eq dr′ q is)
  -- right-Lt (R ⨁ Q) P (inj₂ q) t y eq dr′ t′ p
  --   with right Q P q t y eq | inspect (right Q P q t y) eq
  -- right-Lt (R ⨁ Q) P (inj₂ q) t y eq dr′ t′ () | inj₁ x | Is is
  -- right-Lt (R ⨁ Q) P (inj₂ q) t y eq .(inj₂ dq) .q′ refl
  --   | inj₂ (dq , q′) | Is is = step-⨁₂ (right-Lt Q P q t y eq dq q′ is)
  -- right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq dr′ t′ p
  --   with right R P dr t y eq | inspect (right R P dr t y) eq
  -- right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ p | inj₁ xx | Is is
  --   with first-aux {X = Computed P X alg } {Y = μ P} Q q | inspect (first-aux {X = Computed P X alg } {Y = μ P}Q) q
  -- right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ () | inj₁ xx | Is is | inj₁ x | Is is′
  -- right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ () | inj₁ xx | Is is | inj₂ (r , dq) | Is is′
  -- right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq (inj₂ (r , dq)) t′ p
  --   | inj₁ xx | Is is = base-⨂
  -- right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq .(inj₁ (dr′′ , q)) .q′ refl
  --   | inj₂ (dr′′ , q′) | Is is = step-⨂₁ (right-Lt R P dr t y eq dr′′ q′ is)
  -- right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ t′ p
  --   with right Q P dq t y eq | inspect (right Q P dq t y) eq
  -- right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ t′ () | inj₁ x | Is is
  -- right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(inj₂ (r , dq′)) .q refl
  --   | inj₂ (dq′ , q) | Is is = step-⨂₂ (right-Lt Q P dq t y eq dq′ q is) 

