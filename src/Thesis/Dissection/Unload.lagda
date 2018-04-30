\begin{code}
module Thesis.Dissection.Unload where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  open import Function
  open import Data.List
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
  
  ------------------------------------------------------------------------------
  --                          unload function

  private
    -- first-aux performs recursion on the functorial layer of the tree either
    -- finding whether there are no more left holes to the right.
    first : {X Y : Set} (R : Reg)
              → ⟦ R ⟧ Y
              → ⟦ R ⟧ X ⊎ (∇ R X Y × Y)
    first 0′ ()
    first 1′ tt   = inj₁ tt
    first I x     = inj₂ (tt , x)
    first (K A) x = inj₁ x
    first {X} {Y} (R ⨁ Q) (inj₁ r) with first {X} {Y} R r
    first (R ⨁ Q) (inj₁ r) | inj₁ x        = inj₁ (inj₁ x)
    first (R ⨁ Q) (inj₁ r) | inj₂ (dr , y) = inj₂ (inj₁ dr , y) 
    first {X} {Y} (R ⨁ Q) (inj₂ q) with first {X} {Y} Q q
    first {X} {Y} (R ⨁ Q) (inj₂ q) | inj₁ x        = inj₁ (inj₂ x)
    first {X} {Y} (R ⨁ Q) (inj₂ q) | inj₂ (dq , y) = inj₂ (inj₂ dq , y)
    first {X} {Y} (R ⨂ Q) (r , q) with first {X} {Y} R r
    first {X} {Y} (R ⨂ Q) (r , q) | inj₁ r′ with first {X} {Y} Q q
    first {X} {Y} (R ⨂ Q) (r , q) | inj₁ r′ | inj₁ q′       = inj₁ (r′ , q′)
    first {X} {Y} (R ⨂ Q) (r , q) | inj₁ r′ | inj₂ (dq , y) = inj₂ (inj₂ (r′ , dq) , y)
    first {X} {Y} (R ⨂ Q) (r , q) | inj₂ (dr , y)           = inj₂ (inj₁ (dr , q) , y)

    -- given a dissection and a tree to fill find either the next dissection
    -- or if none left return the input
    right : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} 
          → (∇ R (Computed Q X alg) (μ Q))
          → (t : μ Q) → (y : X) → Catamorphism Q alg t y
          → (⟦ R ⟧ (Computed Q X alg)) ⊎ (∇ R (Computed Q X alg) (μ Q) × μ Q )
    right 0′ Q () t y eq
    right 1′ Q () t y eq
    right I  Q tt t y eq = inj₁ (t ,, y ,, eq)
    right (K A) Q () t y eq
    right (R ⨁ Q) P (inj₁ r) t y eq with right R P r t y eq
    right (R ⨁ Q) P (inj₁ r) t y eq | inj₁ r′        = inj₁ (inj₁ r′)
    right (R ⨁ Q) P (inj₁ r) t y eq | inj₂ (r′ , mq) = inj₂ (inj₁ r′ , mq)
    right (R ⨁ Q) P (inj₂ q) t y eq with right Q P q t y eq
    right (R ⨁ Q) P (inj₂ q) t y eq | inj₁ q′        = inj₁ (inj₂ q′)
    right (R ⨁ Q) P (inj₂ q) t y eq | inj₂ (q′ , mq) = inj₂ (inj₂ q′ , mq)
    right (R ⨂ Q) P (inj₁ (dr , q)) t y eq with right R P dr t y eq
    right {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq | inj₁ r
      with first {X = Computed P X alg } {Y = μ P}  Q q
    right (R ⨂ Q) P (inj₁ (dr , q)) t y eq | inj₁ r | inj₁ q′        = inj₁ (r , q′) 
    right (R ⨂ Q) P (inj₁ (dr , q)) t y eq | inj₁ r | inj₂ (dq , mq) = inj₂ ((inj₂ (r  , dq)) , mq)
    right (R ⨂ Q) P (inj₁ (dr , q)) t y eq | inj₂ (dr′ , mq)         = inj₂ ((inj₁ (dr′ , q)) , mq)
    right (R ⨂ Q) P (inj₂ (r , dq)) t y eq with right Q P dq t y eq
    right (R ⨂ Q) P (inj₂ (r , dq)) t y eq | inj₁ x          = inj₁ (r , x)
    right (R ⨂ Q) P (inj₂ (r , dq)) t y eq | inj₂ (dq′ , mq) = inj₂ ((inj₂ (r , dq′)) , mq)

  -- unload function
  unload : {X : Set} (R : Reg)
         → (alg : ⟦ R ⟧ X → X)
         → (t : μ R) → (x : X) → Catamorphism R alg t x
         → List (∇ R (Computed R X alg) (μ R))
         → UZipper R X alg ⊎ X
  unload R alg t x eq []       = inj₂ x
  unload R alg t x eq (h ∷ hs) with right R R h t x eq
  unload R alg t x eq (h ∷ hs) | inj₁ r with compute R R r
  ... | (rx , rp) , p                               = unload R alg (In rp) (alg rx) (Cata p) hs
  unload R alg t x eq (h ∷ hs) | inj₂ (dr , q)      = load R q (dr ∷ hs)


  ------------------------------------------------------------------------------
  --                 unload preserves the tree structure

  private
    first-Fmap : ∀ {X Y : Set} (R : Reg)
                   → (r : ⟦ R ⟧ Y) → (r′ : ⟦ R ⟧ X)
                   → (ex : X → Y) → first R r ≡ inj₁ r′ → Fmap ex R r′ r 
    first-Fmap 0′ () r′ ex eq
    first-Fmap 1′ tt tt ex eq = Fmap-1′
    first-Fmap I r r′ ex ()
    first-Fmap (K A) r .r ex refl = Fmap-K
    first-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) r′ ex eq
      with first {X} R r | inspect (first {X} R) r
    first-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) .(inj₁ x) ex refl
      | inj₁ x | Is is = Fmap-⨁₁ (first-Fmap R r x ex is)
    first-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) r′ ex () | inj₂ y | Is is
    first-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) r′ ex eq
      with first {X} Q q | inspect (first {X} Q) q
    first-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) .(inj₂ x) ex refl
      | inj₁ x | Is is = Fmap-⨁₂ (first-Fmap Q q x ex is)
    first-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) r′ ex () | inj₂ y | Is is
    first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex x
      with first {X} R r | inspect (first {X} R) r 
    first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex x | inj₁ x₁ | Is is
      with first {X} Q q | inspect (first {X} Q) q
    first-Fmap {X} {Y} (R ⨂ Q) (r , q) .(r′ , q′) ex refl
      | inj₁ r′ | Is is | inj₁ q′ | Is is′ = Fmap-⨂ (first-Fmap R r r′ ex is) (first-Fmap Q q q′ ex is′)
    first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex () | inj₁ x₁ | Is is | inj₂ y | Is is′
    first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex () | inj₂ y | Is is

    first-Plug : ∀ {X Y : Set} (R : Reg)
                   → (r : ⟦ R ⟧ Y) → (dr : ∇ R X Y)
                   → (y : Y) → (ex : X → Y) → first R r ≡ inj₂ (dr , y) → Plug ex R dr y r
    first-Plug 0′ () dr y ex eq
    first-Plug 1′ r () y ex eq
    first-Plug I r tt .r ex refl = Plug-I
    first-Plug (K A) r () y ex eq
    first-Plug {X} (R ⨁ Q) (inj₁ r) dr y ex eq with first {X} R r | inspect (first {X} R) r
    first-Plug {X} (R ⨁ Q) (inj₁ r) dr y ex () | inj₁ x | Is is
    first-Plug {X} (R ⨁ Q) (inj₁ r) .(inj₁ dr′) .y′ ex refl
      | inj₂ (dr′ , y′) | Is is
      = Plug-⨁-inj₁ (first-Plug R r dr′ y′ ex is)
    first-Plug {X} (R ⨁ Q) (inj₂ q) dr y ex eq with first {X} Q q | inspect (first {X} Q) q
    first-Plug {X} (R ⨁ Q) (inj₂ q) dr y ex () | inj₁ x | Is is
    first-Plug {X} (R ⨁ Q) (inj₂ q) .(inj₂ dq) .y′ ex refl
      | inj₂ (dq , y′) | Is is
      = Plug-⨁-inj₂ (first-Plug Q q dq y′ ex is)
    first-Plug {X} (R ⨂ Q) (r , q) dr y ex eq with first {X} R r | inspect (first {X} R) r
    first-Plug {X} (R ⨂ Q) (r , q) dr y ex eq
      | inj₁ r′ | Is is with first {X} Q q | inspect (first {X} Q) q
    first-Plug {X} (R ⨂ Q) (r , q) dr y ex () | inj₁ r′ | Is is | inj₁ x | Is is′
    first-Plug {X} (R ⨂ Q) (r , q) .(inj₂ (r′ , dq′)) .y′ ex refl
      | inj₁ r′ | Is is | inj₂ (dq′ , y′) | Is is′
      = Plug-⨂-inj₂ (first-Fmap R r r′ ex is) (first-Plug Q q dq′ y′ ex is′)
    first-Plug {X} (R ⨂ Q) (r , q) .(inj₁ (dr′ , q)) .q′ ex refl
      | inj₂ (dr′ , q′) | Is is
      = Plug-⨂-inj₁ (first-Plug R r dr′ q′ ex is)

    right-Fmap : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} (dr : ∇ R (Computed Q X alg) (μ Q))
               → (t : μ Q) → (y : X) → (eq : Catamorphism Q alg t y)
               → (r : ⟦ R ⟧ (Computed Q X alg))
               → right R Q dr t y eq ≡ inj₁ r
               → ∀ e → Plug Computed.Tree R dr t e → Fmap Computed.Tree R r e
    right-Fmap 0′ Q () t y eq r right= e p
    right-Fmap 1′ Q () t y eq r right= e p
    right-Fmap I Q .tt t y eq (.t ,, .y ,, .eq) refl .t Plug-I = Fmap-I
    right-Fmap (K A) Q () t y eq r right= e p
    right-Fmap (R ⨁ Q) P (inj₁ x₁) t y eq r x .(inj₁ _) (Plug-⨁-inj₁ p)
      with right R P x₁ t y eq | inspect (right R P x₁ t y) eq
    right-Fmap (R ⨁ Q) P (inj₁ x₁) t y eq .(inj₁ r′) refl .(inj₁ _) (Plug-⨁-inj₁ p)
      | inj₁ r′ | Is is = Fmap-⨁₁ (right-Fmap R P x₁ t y eq r′ is _ p)
    right-Fmap (R ⨁ Q) P (inj₁ x₁) t y eq r () .(inj₁ _) (Plug-⨁-inj₁ p) | inj₂ _ | Is is
    right-Fmap (R ⨁ Q) P (inj₂ y₁) t y eq r x .(inj₂ _) (Plug-⨁-inj₂ p)
      with right Q P y₁ t y eq | inspect (right Q P y₁ t y) eq
    right-Fmap (R ⨁ Q) P (inj₂ y₁) t y eq .(inj₂ x₁) refl .(inj₂ _) (Plug-⨁-inj₂ p) | inj₁ x₁ | Is is
      = Fmap-⨁₂ (right-Fmap Q P y₁ t y eq x₁ is _ p)
    right-Fmap (R ⨁ Q) P (inj₂ y₁) t y eq r () .(inj₂ _) (Plug-⨁-inj₂ p) | inj₂ y₂ | Is is
    right-Fmap (R ⨂ Q) P (inj₁ (dr , q)) t y eq r′ x (_ , _) (Plug-⨂-inj₁ p)
      with right R P dr t y eq | inspect (right R P dr t y) eq
    right-Fmap {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq r′ x (r′′ , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is
      with first {X = Computed P X alg} {Y = μ P} Q q | inspect (first {X = Computed P X alg} {Y = μ P} Q) q
    right-Fmap {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq .(r′ , q′) refl (r′′ , _) (Plug-⨂-inj₁ p)
      | inj₁ r′ | Is is | inj₁ q′ | Is is′ =  Fmap-⨂  (right-Fmap R P dr t y eq r′ is r′′ p) (first-Fmap Q q q′ Computed.Tree is′)
    right-Fmap {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq r′ () (r′′ , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is | inj₂ y₁ | Is is′
    right-Fmap (R ⨂ Q) P (inj₁ (dr , q)) t y eq r′ () (_ , _) (Plug-⨂-inj₁ p) | inj₂ y₁ | Is is
    right-Fmap (R ⨂ Q) P (inj₂ (r  , dq)) t y eq r′ x e p with right Q P dq t y eq | inspect (right Q P dq t y) eq
    right-Fmap (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(r , x₁) refl (_ , _) (Plug-⨂-inj₂ x p)
      | inj₁ x₁ | Is is
      = Fmap-⨂ x (right-Fmap Q P dq t y eq x₁ is _ p)
    right-Fmap (R ⨂ Q) P (inj₂ (r , dq)) t y eq r′ () e p | inj₂ y₁ | Is is

    right-Plug : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} (dr : ∇ R (Computed Q X alg) (μ Q))
               → (t : μ Q) → (y : X) → (eq : Catamorphism Q alg t y)
               → (dr′ : ∇ R (Computed Q X alg) (μ Q)) → (mq : μ Q) → right R Q dr t y eq ≡ inj₂ (dr′ , mq)
               → ∀ e → Plug Computed.Tree R dr t e → Plug Computed.Tree R dr′ mq e 
    right-Plug 0′ Q dr t y eq dr′ mq x () p
    right-Plug 1′ Q dr t y eq () mq x e p
    right-Plug I Q dr t y eq dr′ mq () e p
    right-Plug (K A) Q dr t y eq () mq x e p
    right-Plug (R ⨁ Q) P (inj₁ x) t y eq x′ mq r-eq .(inj₁ e) (Plug-⨁-inj₁ {e = e} p)
      with right R P x t y eq | inspect (right R P x t y) eq
    right-Plug (R ⨁ Q) P (inj₁ x) t y eq x′ mq () .(inj₁ e) (Plug-⨁-inj₁ {e = e} p) | inj₁ _ | _
    right-Plug (R ⨁ Q) P (inj₁ x) t y eq .(inj₁ dr′) .mq′ refl .(inj₁ e) (Plug-⨁-inj₁ {e = e} p) | inj₂ (dr′ , mq′) | Is is
      = Plug-⨁-inj₁ ((right-Plug R P x t y eq dr′ mq′ is e p))
    right-Plug (R ⨁ Q) P (inj₂ x) t y eq x′ mq r-eq .(inj₂ e) (Plug-⨁-inj₂ {e = e} p)
      with right Q P x t y eq | inspect (right Q P x t y) eq
    right-Plug (R ⨁ Q) P (inj₂ x) t y eq x′ mq () .(inj₂ e) (Plug-⨁-inj₂ {e = e} p) | inj₁ _ | _
    right-Plug (R ⨁ Q) P (inj₂ x) t y eq .(inj₂ dr′) .mq′ refl .(inj₂ e) (Plug-⨁-inj₂ {e = e} p) | inj₂ (dr′ , mq′) | Is is
      = Plug-⨁-inj₂ ((right-Plug Q P x t y eq dr′ mq′ is e p))
    right-Plug (R ⨂ Q) P (inj₁ (dr , q)) t y eq dr′ mq x e p
      with right R P dr t y eq | inspect (right R P dr t y) eq
    right-Plug {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq dr′ mq x (e , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is
      with first {X = Computed P X alg} {Y = μ P} Q q | inspect (first {X = Computed P X alg} {Y = μ P} Q) q
    right-Plug {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq dr′ mq () (e , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is | inj₁ _ | _
    right-Plug {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq .(inj₂ (r , dq)) .mq′ refl (e , _) (Plug-⨂-inj₁ p)
      | inj₁ r | Is is | inj₂ (dq , mq′) | Is is′
      = Plug-⨂-inj₂  (right-Fmap R P dr t y eq r is e p) (first-Plug Q q dq mq′ Computed.Tree is′)
    right-Plug (R ⨂ Q) P (inj₁ (dr , q)) t y eq .(inj₁ (dr′ , q)) .mq′′ refl (dr′′ , .q) (Plug-⨂-inj₁ p) | inj₂ (dr′ , mq′′) | Is is
      = Plug-⨂-inj₁ (right-Plug R P dr t y eq dr′ mq′′ is  dr′′ p)
    right-Plug (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ mq x (_ , _) (Plug-⨂-inj₂ p fm)
      with right Q P dq t y eq | inspect (right Q P dq t y) eq
    right-Plug (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ mq () (_ , _) (Plug-⨂-inj₂ p fm) | inj₁ _ | Is _
    right-Plug (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(inj₂ (r , dq′)) .mq′ refl (_ , _) (Plug-⨂-inj₂ fm p) | inj₂ (dq′ , mq′) | Is is
      = Plug-⨂-inj₂  fm (right-Plug Q P dq t y eq dq′ mq′ is _ p)

  -- unload preserves the structure of the tree
  unload-preserves : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X}
                   → (t : μ R) (x : X) (eq : Catamorphism R alg t x) (s : List (∇ R (Computed R X alg) (μ R)))
                   → (z : UZipper R X alg)
                   → ∀ (e : μ R) → Plug-μ⇑ R t s e → unload R alg t x eq s ≡ inj₁ z → PlugZ-μ⇑ R z e
  unload-preserves R t x eq [] z e pl ()
  unload-preserves R t x eq (h ∷ hs) z e pl unl with right R R h t x eq | inspect (right R R h t x) eq
  unload-preserves R t x eq (h ∷ hs) z e pl unl | inj₁ r | Is is
    with compute R R r | inspect (compute R R) r
  unload-preserves R {alg} t x eq (h ∷ hs) z e (Plug-∷ p pl) unl | inj₁ r | Is is | (rx , rp) , pr | Is is′
    with right-Fmap R R h t x eq r is _ p | compute-Fmap R R r rx rp pr is′
  ... | fm | (fm′ , _) with Fmap-unicity fm fm′
  unload-preserves R {alg} t x eq (h ∷ hs) z e (Plug-∷ p pl) unl
    | inj₁ r | Is is | (rx , rp) , pr | Is is′ | fm | fm′ , _ | refl = unload-preserves R (In rp) (alg rx) (Cata pr) hs z e pl unl
  unload-preserves R t x eq (h ∷ hs) z e (Plug-∷ p pl) unl | inj₂ (dr , q) | Is is
    = load-preserves R q (dr ∷ hs) e (Plug-∷ (right-Plug R R h t x eq dr q is _ p) pl) z unl
  
