\begin{code}
module Thesis.Regular where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  open import Relation.Nullary
  open import Function
  open import Data.List
  open import Data.Nat
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Data.List.All as L
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

  open import Thesis.Data.List
  open import Thesis.Dissection.Core
  open import Thesis.Dissection.Load
  open import Thesis.Dissection.Unload
  open import Thesis.Dissection.Relation


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

  --   with reverse (h′ ∷ hs′) | unfold-reverse h′ hs′ | reverse (h ∷ hs) | unfold-reverse h hs
  -- unload-Lt R alg l isl l′ (h ∷ hs) (h′ ∷ hs′) eq x
  --   | inj₂ (dr , mq) | Is is | .(reverse hs′ ++ h′ ∷ []) | refl | .(reverse hs ++ h ∷ []) | refl = {!!}
--                    → ∃ λ s′′
  --                    → s′ ≡ s′′ ++ s 
  -- load-stack-lemma = ?
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

 
  right-Lt : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} 
           → (dr  : ∇ R (Computed Q X alg) (μ Q)) → (t : μ Q)
           → (y : X) → (eq : Catamorphism Q alg t y)
           → (dr′ : ∇ R (Computed Q X alg) (μ Q)) → (t′ : μ Q)
           → right R Q dr t y eq ≡ inj₂ (dr′ , t′)
           → Dissection-Lt (μ Q) (Computed Q X alg) R ((dr′ , t′)) ((dr , t)) 
  right-Lt 0′ Q () t y eq dr′ t′ x
  right-Lt 1′ Q () t y eq dr′ t′ x
  right-Lt I Q tt t y eq dr′ t′ ()
  right-Lt (K A) Q () t y eq dr′ t′ x
  right-Lt (R ⨁ Q) P (inj₁ r) t y eq dr′ t′ p
    with right R P r t y eq | inspect (right R P r t y) eq
  right-Lt (R ⨁ Q) P (inj₁ r) t y eq dr′ t′ () | inj₁ x | Is is
  right-Lt (R ⨁ Q) P (inj₁ r) t y eq .(inj₁ dr′) .q refl
    | inj₂ (dr′ , q) | Is is = step-⨁₁ (right-Lt R P r t y eq dr′ q is)
  right-Lt (R ⨁ Q) P (inj₂ q) t y eq dr′ t′ p
    with right Q P q t y eq | inspect (right Q P q t y) eq
  right-Lt (R ⨁ Q) P (inj₂ q) t y eq dr′ t′ () | inj₁ x | Is is
  right-Lt (R ⨁ Q) P (inj₂ q) t y eq .(inj₂ dq) .q′ refl
    | inj₂ (dq , q′) | Is is = step-⨁₂ (right-Lt Q P q t y eq dq q′ is)
  right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq dr′ t′ p
    with right R P dr t y eq | inspect (right R P dr t y) eq
  right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ p | inj₁ xx | Is is
    with first {X = Computed P X alg } {Y = μ P} Q q | inspect (first {X = Computed P X alg } {Y = μ P}Q) q
  right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ () | inj₁ xx | Is is | inj₁ x | Is is′
  right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ () | inj₁ xx | Is is | inj₂ (r , dq) | Is is′
  right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq (inj₂ (r , dq)) t′ p
    | inj₁ xx | Is is = base-⨂
  right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq .(inj₁ (dr′′ , q)) .q′ refl
    | inj₂ (dr′′ , q′) | Is is = step-⨂₁ (right-Lt R P dr t y eq dr′′ q′ is)
  right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ t′ p
    with right Q P dq t y eq | inspect (right Q P dq t y) eq
  right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ t′ () | inj₁ x | Is is
  right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(inj₂ (r , dq′)) .q refl
    | inj₂ (dq′ , q) | Is is = step-⨂₂ (right-Lt Q P dq t y eq dq′ q is) 


  prepend : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {l₁ l₂ : Leaf R X} {s₁ s₂ : Stack R X alg}
          → Lt R X alg (l₁ , s₁) (l₂ , s₂) → ∀ s → Lt R X alg (l₁ , s ++ s₁) (l₂ , s ++ s₂)
  prepend x [] = x
  prepend (Step {h = h′} {s₁} {s₂} x) (h ∷ s) with prepend x (s ++ [ h′ ])
  ... | lt  with (s ++ [ h′ ]) ++ s₁ | (s ++ [ h′ ]) ++ s₂ | ++-assoc s [ h′ ] s₁ | ++-assoc s [ h′ ] s₂
  prepend (Step {h = h′} {s₁} {s₂} x) (h ∷ s)
      | lt | .(s ++ h′ ∷ s₁) | .(s ++ h′ ∷ s₂) | refl | refl = Step lt
  prepend (Base p₁ p₂ r) (h ∷ s)                             = Step (prepend (Base p₁ p₂ r) s) 

  -- Predicate to test if a dissection has only one hole left
  data Last {X Y : Set} : (R : Reg) → ∇ R Y X → Set where
    Last-⨁-inj₁ : ∀ {R Q} {rx} → Last R rx → Last (R ⨁ Q) (inj₁ rx)
    Last-⨁-inj₂ : ∀ {R Q} {qx} → Last Q qx → Last (R ⨁ Q) (inj₂ qx)
    Last-I       : Last I tt
    Last-⨂₁     : ∀ {R Q} {rx} {q} → (isl : NonRec Q q) → Last R rx → Last (R ⨂ Q) (inj₁ (rx , q))
    Last-⨂₂     : ∀ {R Q} {qx} {r} → Last Q qx          → Last (R ⨂ Q) (inj₂ (r , qx))

  
  Last-Dec : ∀ {X Y : Set} (R : Reg) → (x : ∇ R Y X) → Dec (Last R x)
  Last-Dec 0′ ()
  Last-Dec 1′ ()
  Last-Dec I tt   = yes Last-I
  Last-Dec (K A) ()
  Last-Dec (R ⨁ Q) (inj₁ x) with Last-Dec R x
  Last-Dec (R ⨁ Q) (inj₁ x) | yes p = yes (Last-⨁-inj₁ p)
  Last-Dec (R ⨁ Q) (inj₁ x) | no ¬p = no λ { (Last-⨁-inj₁ x) → ¬p x}
  Last-Dec (R ⨁ Q) (inj₂ y) with Last-Dec Q y
  Last-Dec (R ⨁ Q) (inj₂ y) | yes p = yes (Last-⨁-inj₂ p)
  Last-Dec (R ⨁ Q) (inj₂ y) | no ¬p = no λ { (Last-⨁-inj₂ x) → ¬p x}
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) with Last-Dec R dr
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | yes p with NonRec-Dec Q q
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | yes p | yes p₁ = yes (Last-⨂₁ p₁ p)
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | yes p | no ¬p  = no λ { (Last-⨂₁ isl x) → ¬p isl}
  Last-Dec (R ⨂ Q) (inj₁ (dr , q)) | no ¬p          = no λ { (Last-⨂₁ isl x) → ¬p x}
  Last-Dec (R ⨂ Q) (inj₂ (r , dq)) with Last-Dec Q dq
  Last-Dec (R ⨂ Q) (inj₂ (r , dq)) | yes p = yes (Last-⨂₂ p)
  Last-Dec (R ⨂ Q) (inj₂ (r , dq)) | no ¬p = no λ { (Last-⨂₂ x) → ¬p x}
  
  data PrefixView {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} : Stack R X alg → Set where
    AllOf  : ∀ xs         → L.All (Last R) xs  → PrefixView xs
    Prefix : ∀ pre x post → L.All (Last R) pre → ¬ (Last R x) → PrefixView (pre ++ x ∷ post)

  toView : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (s : Stack R X alg) → PrefixView {X} {R} {alg} s
  toView R [] = AllOf [] []
  toView R (h ∷ hs) with toView R hs
  toView R (h ∷ hs) | AllOf .hs x with Last-Dec R h
  toView R (h ∷ hs) | AllOf .hs x | yes p = AllOf (h ∷ hs) (p ∷ x)
  toView R (h ∷ hs) | AllOf .hs x | no ¬p = Prefix [] h hs [] ¬p
  toView R (h ∷ .(pre ++ x ∷ post)) | Prefix pre x post ¬p all
    with Last-Dec R h
  toView R (h ∷ .(pre ++ x ∷ post)) | Prefix pre x post ¬p all | yes p  = Prefix (h ∷ pre) x post (p ∷ ¬p) all
  toView R (h ∷ .(pre ++ x ∷ post)) | Prefix pre x post ¬p all | no ¬p′ = Prefix [] h (pre ++ x ∷ post) [] ¬p′

  -- unload-stack-lemma : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X}
  --                        {pre post : Stack R X alg} {dr : ∇ R (Computed R X alg) (μ R)}
  --                        {t : μ R} {x : X} {eq : Catamorphism R alg t x}
  --                        {l′ : Leaf R X} {s′ : Stack R X alg}
  --                        → L.All (Last R) pre → ¬ (Last R dr) → unload R alg t x eq (pre ++ dr ∷ post) ≡ inj₁ (l′ , s′)
  --                        → Σ (Stack R X alg × λ {(s , dr′ , y , eq , e , mq)
  --                        → Plug-μ⇑ R t pre e × right R R dr e y eq ≡ inj₂ (dr′ , mq) × s′ ≡ s ++ {!dr′!} ∷ post}
  -- unload-stack-lemma = {!!}
  
  unload-Lt : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → ∀ (l : ⟦ R ⟧ X) (isl : NonRec R l) (l′ : Leaf R X) (s s′ : Stack R X alg) eq
            → unload R alg (In (coerce l isl)) (alg l) eq s ≡ inj₁ (l′ , s′) → Lt R X alg (l′ , reverse s′ ) ((l , isl) , reverse s)
  unload-Lt R alg l isl l′ [] s′ eq ()
  unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul with right R R h (In (coerce l isl)) (alg l) eq | inspect (right R R h (In (coerce l isl)) (alg l)) eq
  unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul | inj₁ r′ | Is is with compute R R r′ | inspect (compute R R) r′
  unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ with toView R hs
  unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | AllOf .hs x = {!!} -- this is bogus
  unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) s′ eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂ = {!!}
  unload-Lt R alg l isl l′ (h ∷ hs) hs′ eq x | inj₂ (dr , mq) | Is is with right-Lt R R h (In (coerce l isl)) (alg l) eq dr mq is 
  ... | d with load-stack-lemma R mq dr hs l′ dr hs′ x
  unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is | d | s′′ , refl
    with reverse (s′′ ++ dr ∷ hs) | reverse-++-commute s′′ (dr ∷ hs)
  unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is |
    d | s′′ , refl | .(reverse (dr ∷ hs) ++ reverse s′′) | refl with reverse (dr ∷ hs) | unfold-reverse dr hs | reverse (h ∷ hs) | unfold-reverse h hs
  unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is | d
    | s′′ , refl | .(reverse (dr ∷ hs) ++ reverse s′′) | refl | .(reverse hs ++ dr ∷ []) | refl | .(reverse hs ++ h ∷ []) | refl
    with (reverse hs ++ [ dr ]) ++ reverse s′′ | ++-assoc (reverse hs) [ dr ] (reverse s′′)
  unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is | d
    | s′′ , refl | .(reverse (dr ∷ hs) ++ reverse s′′) | refl | .(reverse hs ++ dr ∷ []) | refl
    | .(reverse hs ++ h ∷ []) | refl | .(reverse hs ++ dr ∷ reverse s′′) | refl  with load-preserves′ R mq (dr ∷ hs) (l′ , s′′ ++ dr ∷ hs) x
  ... | pr = prepend (Base {!!} Plug-[] d) (reverse hs) -- this is easyᵀᴹ
 
