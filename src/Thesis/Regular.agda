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
  open import Thesis.Data.List.Prefix
  open import Thesis.Dissection.Core
  open import Thesis.Dissection.Load
  open import Thesis.Dissection.Relation
  open import Thesis.Regular.First
  open import Thesis.Regular.Last
  open import Thesis.Regular.Right

  ------------------------------------------------------------------------------
  --                     `unload` function and properties                     --
  
  unload : {X : Set} (R : Reg)
         → (alg : ⟦ R ⟧ X → X)
         → (t : μ R) → (x : X) → Catamorphism R alg t x
         → List (∇ R (Computed R X alg) (μ R))
         → UZipper R X alg ⊎ X
  unload R alg t x eq []       = inj₂ x
  unload R alg t x eq (h ∷ hs) with right R h (t ,, x  ,, eq)
  unload R alg t x eq (h ∷ hs) | inj₁ r with compute R R r
  ... | (rx , rp) , p                               = unload R alg (In rp) (alg rx) (Cata p) hs
  unload R alg t x eq (h ∷ hs) | inj₂ (dr , q)      = load R q (dr ∷ hs)

  -- `unload` preserves the structure of the tree
  unload-preserves : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X}
                   → (t : μ R) (x : X) (eq : Catamorphism R alg t x) (s : List (∇ R (Computed R X alg) (μ R)))
                   → (z : UZipper R X alg)
                   → ∀ (e : μ R) → Plug-μ⇑ R t s e → unload R alg t x eq s ≡ inj₁ z → PlugZ-μ⇑ R z e
  unload-preserves R t x eq [] z e pl ()
  unload-preserves R t x eq (h ∷ hs) z e pl unl with right R h (t ,, x ,, eq) | inspect (right R h) (t ,, x ,, eq)
  unload-preserves R t x eq (h ∷ hs) z e pl unl | inj₁ r | Is is
    with compute R R r | inspect (compute R R) r
  unload-preserves R {alg} t x eq (h ∷ hs) z e (Plug-∷ p pl) unl | inj₁ r | Is is | (rx , rp) , pr | Is is′
    with right-Fmap R h (t ,, x ,, eq) r is _ p | compute-Fmap R R r rx rp pr is′
  ... | fm | (fm′ , _) with Fmap-unicity fm fm′
  unload-preserves R {alg} t x eq (h ∷ hs) z e (Plug-∷ p pl) unl
    | inj₁ r | Is is | (rx , rp) , pr | Is is′ | fm | fm′ , _ | refl = unload-preserves R (In rp) (alg rx) (Cata pr) hs z e pl unl
  unload-preserves R t x eq (h ∷ hs) z e (Plug-∷ p pl) unl | inj₂ (dr , q) | Is is
    = load-preserves R q (dr ∷ hs) z unl e (Plug-∷ (right-Plug R h (t ,, x ,, eq) dr q is _ p) pl)

  
  propInit : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (l : ⟦ R ⟧ X)
             (isl : NonRec R l) → Catamorphism R alg (In (coerce l isl)) (alg l)
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
           → right R dr (t ,, y ,, eq) ≡ inj₂ (dr′ , t′)
           → Dissection-Lt (μ Q) (Computed Q X alg) R ((dr′ , t′)) ((dr , t)) 
  right-Lt 0′ Q () t y eq dr′ t′ x
  right-Lt 1′ Q () t y eq dr′ t′ x
  right-Lt I Q tt t y eq dr′ t′ ()
  right-Lt (K A) Q () t y eq dr′ t′ x
  right-Lt (R ⨁ Q) P (inj₁ r) t y eq dr′ t′ p
    with right R r (t ,, y ,, eq) | inspect (right R r) (t ,, y ,, eq)
  right-Lt (R ⨁ Q) P (inj₁ r) t y eq dr′ t′ () | inj₁ x | Is is
  right-Lt (R ⨁ Q) P (inj₁ r) t y eq .(inj₁ dr′) .q refl
    | inj₂ (dr′ , q) | Is is = step-⨁₁ (right-Lt R P r t y eq dr′ q is)
  right-Lt (R ⨁ Q) P (inj₂ q) t y eq dr′ t′ p
    with right Q q (t ,, y ,, eq) | inspect (right Q q) (t ,, y ,, eq)
  right-Lt (R ⨁ Q) P (inj₂ q) t y eq dr′ t′ () | inj₁ x | Is is
  right-Lt (R ⨁ Q) P (inj₂ q) t y eq .(inj₂ dq) .q′ refl
    | inj₂ (dq , q′) | Is is = step-⨁₂ (right-Lt Q P q t y eq dq q′ is)
  right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq dr′ t′ p
    with right R dr (t ,, y ,, eq) | inspect (right R dr) (t ,, y ,, eq)
  right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ p | inj₁ xx | Is is
    with first {X = μ P} {Y = Computed P X alg } Q q | inspect (first {X = μ P} {Y = Computed P X alg }  Q) q
  right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ () | inj₁ xx | Is is | inj₁ x | Is is′
  right-Lt {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq (inj₁ (dr′ , q′)) t′ () | inj₁ xx | Is is | inj₂ (r , dq) | Is is′
  right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq (inj₂ (r , dq)) t′ p
    | inj₁ xx | Is is = base-⨂
  right-Lt (R ⨂ Q) P (inj₁ (dr , q)) t y eq .(inj₁ (dr′′ , q)) .q′ refl
    | inj₂ (dr′′ , q′) | Is is = step-⨂₁ (right-Lt R P dr t y eq dr′′ q′ is)
  right-Lt (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ t′ p
    with right Q dq (t ,, y ,, eq) | inspect (right Q dq) (t ,, y ,, eq)
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

  
  first-NonRec : ∀ {X Y : Set} (R : Reg)
               → (ry : ⟦ R ⟧ Y)
               → (isl-ry : NonRec R ry)
               → ∀ (rx : ∇ R X Y) (y : Y) → first R ry ≡ inj₂ (rx , y)
               → ⊥
  first-NonRec 0′ () isl-ry rx y x
  first-NonRec 1′ ry isl-ry rx y ()
  first-NonRec I ry () .tt .ry refl
  first-NonRec (K A) ry isl-ry () y x 
  first-NonRec (R ⨁ Q) (inj₁ x₁) isl-ry rx y x = {!!}
  first-NonRec (R ⨁ Q) (inj₂ y₁) isl-ry rx y x = {!!}
  first-NonRec (R ⨂ Q) ry isl-ry rx y x = {!!}


  right-Last : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X}
          (dr : ∇ R (Computed Q X alg) (μ Q)) (t : μ Q) (x : X) (eq : Catamorphism Q alg t x)
        → Last R dr → (dr′ : ∇ R (Computed Q X alg) (μ Q)) (mq : μ Q)
        → right R dr (t ,, x ,, eq) ≡ inj₂ (dr′ , mq) → ⊥
  right-Last = {!!}
  -- right-Last 0′ Q () t x eq last dr′ mq pr
  -- right-Last 1′ Q () t x eq last dr′ mq pr
  -- right-Last I Q tt t x eq last dr′ mq ()
  -- right-Last (K A) Q () t x eq last dr′ mq pr
  -- right-Last (R ⨁ Q) P (inj₁ dr) t x eq last dr′ mq pr with right R P dr t x eq | inspect (right R P dr t x) eq
  -- right-Last (R ⨁ Q) P (inj₁ dr) t x eq last dr′ mq () | inj₁ _ | Is is
  -- right-Last (R ⨁ Q) P (inj₁ dr) t x eq (Last-⨁-inj₁ last) .(inj₁ dr′′) .mq′ refl | inj₂ (dr′′ , mq′) | Is is = right-Last R P dr t x eq last dr′′ mq′ is
  -- right-Last (R ⨁ Q) P (inj₂ dq) t x eq last dr′ mq pr with right Q P dq t x eq | inspect (right Q P dq t x) eq
  -- right-Last (R ⨁ Q) P (inj₂ dq) t x eq last dr′ mq () | inj₁ x₁ | Is is
  -- right-Last (R ⨁ Q) P (inj₂ dq) t x eq (Last-⨁-inj₂ last) .(inj₂ dq′) .mq′ refl | inj₂ (dq′ , mq′) | Is is = right-Last Q P dq t x eq last dq′ mq′ is
  -- right-Last (R ⨂ Q) P (inj₁ (dr , q)) t x eq last dr′ mq pr with right R P dr t x eq | inspect (right R P dr t x) eq
  -- right-Last {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t x eq (Last-⨂₁ isl last) dr′ mq pr | inj₁ x₁ | Is is
  --   with first {X = Computed P X alg } {Y = μ P} Q q | inspect (first {X = Computed P X alg } {Y = μ P} Q) q
  -- right-Last {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t x eq (Last-⨂₁ isl last) dr′ mq () | inj₁ x₁ | Is is | inj₁ x₂ | Is is′
  -- right-Last {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t x eq (Last-⨂₁ isl last) .(inj₂ (x₁ , dr′′)) .mq′ refl | inj₁ x₁ | Is is | inj₂ (dr′′ , mq′) | Is is′
  --   = first-NonRec Q q isl dr′′ mq′ is′
  -- right-Last (R ⨂ Q) P (inj₁ (dr , q)) t x eq (Last-⨂₁ isl last) .(inj₁ (dr′′ , q)) .mq′ refl | inj₂ (dr′′ , mq′) | Is is = right-Last R P dr t x eq last dr′′ mq′  is
  -- right-Last (R ⨂ Q) P (inj₂ (r , dq)) t x eq (Last-⨂₂ last) dr′ mq pr with right Q P  dq t x eq | inspect (right Q P dq t x) eq
  -- right-Last (R ⨂ Q) P (inj₂ (r , dq)) t x eq (Last-⨂₂ last) dr′ mq () | inj₁ x₁ | Is is
  -- right-Last (R ⨂ Q) P (inj₂ (r , dq)) t x eq (Last-⨂₂ last) .(inj₂ (r , dq′)) .mq′ refl | inj₂ (dq′ , mq′) | Is is = right-Last Q P dq t x eq last dq′ mq′ is 

  right-¬Last : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X}
          (dr : ∇ R (Computed Q X alg) (μ Q)) (t : μ Q) (x : X) (eq : Catamorphism Q alg t x)
        → ¬ Last R dr → (r : ⟦ R ⟧ (Computed Q X alg))
        → right R dr (t ,, x ,, eq) ≡ inj₁ r → ⊥
  right-¬Last = {!!}
  unload-stack-lemma : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X}
                         (pre post : Stack R X alg) (dr : ∇ R (Computed R X alg) (μ R))
                         (t : μ R) (x : X) (eq : Catamorphism R alg t x)
                         (l′ : Leaf R X) (s′ : Stack R X alg)
                         → L.All (Last R) pre → ¬ (Last R dr) → unload R alg t x eq (pre ++ dr ∷ post) ≡ inj₁ (l′ , s′)
                         → Σ (Stack R X alg) λ s
                         → Σ (∇ R (Computed R X alg) (μ R)) λ dr′ → Σ (μ R × X) λ {(e , x) 
                         → Σ (Catamorphism R alg e x) λ eq′ → Σ (μ R) λ e′
                           → s′ ≡ s ++ dr′ ∷ post × Plug-μ⇑ R t pre e × PlugZ-μ⇑ R (l′ , s) e′ × right R dr (e ,, x ,, eq′) ≡ inj₂ (dr′ , e′)}
  unload-stack-lemma R .[] post dr t x eq l′ s′ [] last pr with right R dr (t ,, x ,, eq) | inspect (right R dr) (t ,, x ,, eq)
  unload-stack-lemma R .[] post dr t x eq l′ s′ [] last pr | inj₁ r′ | Is is = ⊥-elim (right-¬Last R R dr t x eq last r′ is)
  unload-stack-lemma R .[] post dr t x eq l′ s′ [] last pr | inj₂ (dr′ , mq) | Is is with load-stack-lemma R mq dr′ post l′ dr′ s′ pr
  unload-stack-lemma R .[] post dr t x eq l′ .(s ++ dr′ ∷ post) [] last pr | inj₂ (dr′ , mq) | Is is | s , refl , plug
    = s , (dr′ , ((t , x) , (eq , (mq , (refl , (Plug-[] , (plug , is)))))))
  unload-stack-lemma R .(x ∷ _) post dr t y eq l′ s′ (_∷_ {x} px all) last pr with right R x (t ,, y ,, eq) | inspect (right R x) (t ,, y ,, eq)
  unload-stack-lemma R {alg} .(x ∷ _) post dr t y eq l′ s′ (_∷_ {x} px all) last pr | inj₁ r′ | Is is with compute R R r′ | inspect (compute R R) r′
  ... | (rx , rm) , mf | Is is′ with unload-stack-lemma R _ post dr  (In rm) (alg rx) (Cata mf) l′ s′ all last pr
  unload-stack-lemma R {alg} .(x ∷ xs) post dr t y eq l′ .(s ++ dr′ ∷ post) (_∷_ {x} {xs} px all) last pr | inj₁ r′ | Is is | (rx , rm) , mf | Is is′ | s , dr′ , (rm′ , x′) , ceq , e′ , refl , pl1 , pl₂ , req = s , (dr′ , ((rm′ , x′) , (ceq , (e′ , (refl , (Plug-∷ {!!} pl1 , (pl₂ , req)))))))
  unload-stack-lemma R .(x ∷ _) post dr t y eq l′ s′ (_∷_ {x} px all) last pr | inj₂ (dr′ , mq) | Is is = ⊥-elim (right-Last R R x t y eq px dr′ mq is)
  
  -- unload-Lt : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → ∀ (l : ⟦ R ⟧ X) (isl : NonRec R l) (l′ : Leaf R X) (s s′ : Stack R X alg) eq
  --           → unload R alg (In (coerce l isl)) (alg l) eq s ≡ inj₁ (l′ , s′) → Lt R X alg (l′ , reverse s′ ) ((l , isl) , reverse s)
  -- unload-Lt R alg l isl l′ [] s′ eq ()
  -- unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul with right R h ((In (coerce l isl)) ,, (alg l) ,, eq) | inspect (right R h) ((In (coerce l isl)) ,, (alg l) ,, eq)
  -- unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul | inj₁ r′ | Is is with compute R R r′ | inspect (compute R R) r′
  -- unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ with prefix R hs
  -- unload-Lt R alg l isl l′ (h ∷ hs) s′ eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | AllOf .hs x = {!!} -- this is bogus
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) s′ eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | OnlyPrefix pre x post x₁ x₂
  --   with unload-stack-lemma R pre post x (In rp) (alg rx) (Cata mFold) l′ s′ x₁ x₂ ul
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) .(s ++ dr ∷ post) eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂
  --   | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req
  --   with reverse (h ∷ pre ++ x ∷ post) | unfold-reverse h (pre ++ x ∷ post)
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) .(s ++ dr ∷ post) eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂
  --   | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req | .(reverse (pre ++ x ∷ post) ++ h ∷ []) | refl
  --   with reverse (s ++ dr ∷ post) | reverse-++-commute s (dr ∷ post) | reverse (pre ++ x ∷ post) | reverse-++-commute pre (x ∷ post)
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) .(s ++ dr ∷ post) eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂
  --   | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req | .(reverse (pre ++ x ∷ post) ++ h ∷ []) | refl
  --   | .(reverse (dr ∷ post) ++ reverse s) | refl | .(reverse (x ∷ post) ++ reverse pre) | refl
  --   with reverse (dr ∷ post) | unfold-reverse dr post | reverse (x ∷ post) | unfold-reverse x post
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) .(s ++ dr ∷ post) eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂
  --   | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req | .(reverse (pre ++ x ∷ post) ++ h ∷ []) | refl | .(reverse (dr ∷ post) ++ reverse s) | refl
  --   | .(reverse (x ∷ post) ++ reverse pre) | refl | .(reverse post ++ [ dr ]) | refl | .(reverse post ++ [ x ]) | refl
  --   with (reverse post ++ [ dr ]) ++ reverse s | ++-assoc (reverse post) ([ dr ]) (reverse s)
  --   | (reverse post ++ [ x ]) ++ reverse pre | ++-assoc (reverse post) ([ x ]) (reverse pre)
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) .(s ++ dr ∷ post) eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂
  --   | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req | .(reverse (pre ++ x ∷ post) ++ h ∷ []) | refl | .(reverse (dr ∷ post) ++ reverse s) | refl
  --   | .(reverse (x ∷ post) ++ reverse pre) | refl | .(reverse post ++ [ dr ]) | refl | .(reverse post ++ [ x ]) | refl
  --   | .(reverse post ++ dr ∷ reverse s) | refl | .(reverse post ++ x ∷ reverse pre) | refl
  --   with (reverse post ++ x ∷ reverse pre) ++ [ h ] | ++-assoc (reverse post) (x ∷ reverse pre) [ h ]
  -- unload-Lt R alg l isl l′ (h ∷ .(pre ++ x ∷ post)) .(s ++ dr ∷ post) eq ul | inj₁ r′ | Is is | (rx , rp) , mFold | Is is′ | Prefix pre x post x₁ x₂
  --   | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req | .(reverse (pre ++ x ∷ post) ++ [ h ]) | refl | .(reverse (dr ∷ post) ++ reverse s) | refl
  --   | .(reverse (x ∷ post) ++ reverse pre) | refl | .(reverse post ++ [ dr ]) | refl | .(reverse post ++ [ x ]) | refl
  --   | .(reverse post ++ dr ∷ reverse s) | refl | .(reverse post ++ x ∷ reverse pre) | refl | .(reverse post ++ x ∷ reverse pre ++ [ h ]) | refl
  --   with right-Lt R R x mr x′ ceq dr mq′ req
  -- ... | lt = prepend (Base (Plug-μ⇑-to-Plug-μ⇓ R l′ s mq′ plug₂) {!plug₂!} lt) (reverse post)
  -- unload-Lt R alg l isl l′ (h ∷ hs) hs′ eq x | inj₂ (dr , mq) | Is is with right-Lt R R h (In (coerce l isl)) (alg l) eq dr mq is 
  -- ... | d with load-stack-lemma R mq dr hs l′ dr hs′ x
  -- unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is | d | s′′ , refl , pl
  --   with reverse (s′′ ++ dr ∷ hs) | reverse-++-commute s′′ (dr ∷ hs)
  -- unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is |
  --   d | s′′ , refl , pl | .(reverse (dr ∷ hs) ++ reverse s′′) | refl with reverse (dr ∷ hs) | unfold-reverse dr hs | reverse (h ∷ hs) | unfold-reverse h hs
  -- unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is | d
  --   | s′′ , refl , pl | .(reverse (dr ∷ hs) ++ reverse s′′) | refl | .(reverse hs ++ dr ∷ []) | refl | .(reverse hs ++ h ∷ []) | refl
  --   with (reverse hs ++ [ dr ]) ++ reverse s′′ | ++-assoc (reverse hs) [ dr ] (reverse s′′)
  -- unload-Lt R alg l isl l′ (h ∷ hs) .(s′′ ++ dr ∷ hs) eq x | inj₂ (dr , mq) | Is is | d
  --   | s′′ , refl , pl | .(reverse (dr ∷ hs) ++ reverse s′′) | refl | .(reverse hs ++ dr ∷ []) | refl
  --   | .(reverse hs ++ h ∷ []) | refl | .(reverse hs ++ dr ∷ reverse s′′) | refl  with load-preserves R mq (dr ∷ hs) (l′ , s′′ ++ dr ∷ hs) x
  -- ... | pr with  pr (plug-μ⇑ R mq (dr ∷ hs)) (plug-μ⇑-to-Plug-μ⇑ R mq (dr ∷ hs) (plug-μ⇑ R mq (dr ∷ hs)) refl)
  -- ... |  z = prepend (Base (Plug-μ⇑-to-Plug-μ⇓ R l′ s′′ mq pl) Plug-[] d) (reverse hs) -- this is easyᵀᴹ
 
