
module Dissection.Load where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  open import Function
  open import Data.List
  open import Induction.WellFounded

  -- open import Data.Sum.Extra
  open import Data.List.Extra

  open import Regular.Core
  open import Regular.Equality
    renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Regular.Dissection
    renaming ( Lt to Dissection-Lt
             ; IxLt to Dissection-IxLt
             ; Lt-to-IxLt to Dissection-Lt-to-IxLt
             ; IxLt-WF to Dissection-IxLt-WF
             ; proof-irrelevance to Plug-proof-irrelevance)
  open import Regular.NonRec
    renaming (proof-irrelevance to NonRec-proof-irrelevance)
  open import Regular.Catamorphism

  open import Dissection.Core
  open import Regular.First
  
  ------------------------------------------------------------------------------
  --                           load function

  private
    -- auxiliary function in CPS style that computes a dissection to the
    -- leftmost hole if it exists.
    first-cps-⨁₁ : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
              → (Leaf (R ⨁ Q) X → Stack P X alg → UZipper P X alg ⊎ X)
              → (Leaf R X        → Stack P X alg → UZipper P X alg ⊎ X)
    first-cps-⨁₁ R Q P f (l , x) s = f ((inj₁ l , NonRec-⨁-inj₁ R Q l x)) s

    first-cps-⨁₂ : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
              → (Leaf (R ⨁ Q) X → Stack P X alg → UZipper P X alg ⊎ X)
              → (Leaf Q X        → Stack P X alg → UZipper P X alg ⊎ X)
    first-cps-⨁₂ R Q P f (l , x) s = f (inj₂ l , NonRec-⨁-inj₂ R Q l x) s

    first-cps-⨂-2 : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
               → (Leaf (R ⨂ Q) X     → Stack P X alg → UZipper P X alg ⊎ X)
               → (Leaf R X → Leaf Q X → Stack P X alg → UZipper P X alg ⊎ X)
    first-cps-⨂-2 R Q P f (r , isl-r) (q , isl-q) s = f ((r , q) , NonRec-⨂ R Q r q isl-r isl-q) s

    mutual
      first-cps-⨂-1 : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
                 → (∇ R (Computed P X alg) (μ P) × ⟦ Q ⟧ (μ P) ⊎ ⟦ R ⟧ (Computed P X alg) × ∇ Q (Computed P X alg) (μ P)
                 → ∇ P (Computed P X alg) (μ P))
                 → (Leaf (R ⨂ Q) X → Stack P X alg → UZipper P X alg ⊎ X)
                 → ⟦ Q ⟧ (μ P)
                 → (Leaf R X → Stack P X alg → UZipper P X alg ⊎ X)
      first-cps-⨂-1 R Q P k f q (r , isl) = first-cps Q P q (k ∘ inj₂ ∘ _,_ (coerce r isl)) (first-cps-⨂-2 R Q P f (r , isl))

      first-cps : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X}
            → ⟦ R ⟧ (μ Q)
            → (∇ R (Computed Q X alg) (μ Q) → (∇ Q (Computed Q X alg) (μ Q)))
            → (Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg ⊎ X)
            → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg ⊎ X
      first-cps 0′ Q () _
      first-cps 1′ Q x k f s              = f (tt , NonRec-1′) s
      first-cps I Q (In x) k f s          = first-cps Q Q x id (λ z  → inj₁ ∘ _,_ z) (k tt ∷ s)
      first-cps (K A) Q x k f s           = f (x , NonRec-K A x) s
      first-cps (R ⨁ Q) P (inj₁ x) k f s = first-cps R P x  (k ∘ inj₁) (first-cps-⨁₁ R Q P f) s
      first-cps (R ⨁ Q) P (inj₂ y) k f s = first-cps Q P y  (k ∘ inj₂) (first-cps-⨁₂ R Q P f) s
      first-cps (R ⨂ Q) P (r , q) k f s  = first-cps R P r  (k ∘ inj₁ ∘ (_, q)) (first-cps-⨂-1 R Q P k f q) s

  -- main `load` function
  load : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → μ R → Stack R X alg → UZipper R X alg ⊎ X
  load R (In t) s = first-cps R R t id (λ l → inj₁ ∘ _,_ l) s

  ------------------------------------------------------------------------------
  --                  `load` never delivers a inj₁                          --

  private
    Prop-Not-inj₂ : ∀ (X : Set) (R Q : Reg) (alg : ⟦ Q ⟧ X → X)
                  → (Leaf R X → Stack Q X alg → UZipper Q X alg ⊎ X)
                  → Set
    Prop-Not-inj₂ X R Q alg f = ∀ (l : Leaf R X) → (s : Stack Q X alg) → (x : X) → f l s ≡ inj₂ x → ⊥

    Prop-first-cps-not-inj₂-⨁₁ : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                            {f : Leaf (R ⨁ Q) X → Stack P X alg → UZipper P X alg ⊎ X}
                            → Prop-Not-inj₂ X (R ⨁ Q) P alg f → Prop-Not-inj₂ X R P alg (first-cps-⨁₁ R Q P f)
    Prop-first-cps-not-inj₂-⨁₁ pr (l , isl) s x feq = pr (inj₁ l , NonRec-⨁-inj₁ _ _ l isl) s x feq 

    Prop-first-cps-not-inj₂-⨁₂ : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                             {f : Leaf (R ⨁ Q) X → Stack P X alg → UZipper P X alg ⊎ X}
                             → Prop-Not-inj₂ X (R ⨁ Q) P alg f → Prop-Not-inj₂ X Q P alg (first-cps-⨁₂ R Q P f)
    Prop-first-cps-not-inj₂-⨁₂ pr (l , isl) s x feq = pr (inj₂ l , NonRec-⨁-inj₂ _ _ l isl) s x feq

    Prop-first-cps-not-inj₂-⨂-2 : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                              {l   : ⟦ R ⟧ X}
                              {isl : NonRec R l}
                              {f : Leaf (R ⨂ Q) X → Stack P X alg → UZipper P X alg ⊎ X}
                             → Prop-Not-inj₂ X (R ⨂ Q) P alg f → Prop-Not-inj₂ X Q P alg (first-cps-⨂-2 R Q P f (l , isl))
    Prop-first-cps-not-inj₂-⨂-2 pr (l , isl) s x feq = pr ((_ , l) , NonRec-⨂ _ _ _ l _ isl) s x feq


    mutual
      Prop-first-cps-not-inj₂-⨂-1 : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                                {k : ∇ R (Computed P X alg) (μ P) × ⟦ Q ⟧ (μ P) ⊎ ⟦ R ⟧ (Computed P X alg) × ∇ Q (Computed P X alg) (μ P) → ∇ P (Computed P X alg) (μ P)}
                                {q : ⟦ Q ⟧ (μ P)}
                                {f : Leaf (R ⨂ Q) X → List (∇ P (Computed P X alg) (μ P)) → UZipper P X alg ⊎ X}
                               → Prop-Not-inj₂ X (R ⨂ Q) P alg f → Prop-Not-inj₂ X R P alg (first-cps-⨂-1 R Q P k f q)
      Prop-first-cps-not-inj₂-⨂-1 {R = R} {Q} {P} {k = k} {f = f} pr (l , isl) s x feq
        = first-cps-not-inj₂ Q P _ (k ∘ inj₂ ∘ (_,_ (coerce l isl))) (first-cps-⨂-2 R Q P f (l , isl)) (Prop-first-cps-not-inj₂-⨂-2 pr) s x  feq 

      first-cps-not-inj₂ : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} → (r : ⟦ R ⟧ (μ Q)) 
                     → (k : ∇ R (Computed Q X alg) (μ Q) → ∇ Q (Computed Q X alg) (μ Q))
                     → (f : Leaf R X → Stack Q X alg → UZipper Q X alg ⊎ X)
                     → Prop-Not-inj₂ X R Q alg f
                     → (s : Stack Q X alg)
                     → (x : X)
                     → first-cps R Q r k f s ≡ inj₂ x → ⊥
      first-cps-not-inj₂ 0′ Q () k f pr s x eq
      first-cps-not-inj₂ 1′ Q r k f pr s x eq with f (tt , NonRec-1′) s | inspect (f (tt , NonRec-1′)) s
      first-cps-not-inj₂ 1′ Q r k f pr s x () | inj₁ x₁   | Is is
      first-cps-not-inj₂ 1′ Q r k f pr s .y refl | inj₂ y | Is is = pr (tt , NonRec-1′) s y is
      first-cps-not-inj₂ I Q (In r) k f pr s x eq = first-cps-not-inj₂ Q Q r id (λ z z₁ → inj₁ (z , z₁)) (λ _ _ _ ()) (k tt ∷ s) x eq
      first-cps-not-inj₂ (K A) Q r k f pr s x eq  with f (r , NonRec-K A r) s | inspect (f (r , NonRec-K A r)) s
      first-cps-not-inj₂ (K A) Q r k f pr s x () | inj₁ x₁ | Is is
      first-cps-not-inj₂ (K A) Q r k f pr s .y refl | inj₂ y | Is is = pr (r , NonRec-K A r) s y is
      first-cps-not-inj₂ (R ⨁ Q) P (inj₁ r) k f pr s x eq = first-cps-not-inj₂ R P r (k ∘ inj₁) (first-cps-⨁₁ R Q P f) (Prop-first-cps-not-inj₂-⨁₁ pr) s x eq                         
      first-cps-not-inj₂ (R ⨁ Q) P (inj₂ q) k f pr s x eq = first-cps-not-inj₂ Q P q (k ∘ inj₂) (first-cps-⨁₂ R Q P f) (Prop-first-cps-not-inj₂-⨁₂ pr) s x eq
      first-cps-not-inj₂ (R ⨂ Q) P (r , q) k f pr s x eq  =
        first-cps-not-inj₂ R P r (k ∘ inj₁ ∘ (_, q)) (first-cps-⨂-1 R Q P k f q) (Prop-first-cps-not-inj₂-⨂-1 {_} {R} {Q} {P} {_} {k} {q} {f} pr) s x eq

  load-not-inj₂ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X}
                 → (t : μ R) → (s : Stack R X alg)
                 → (x : X)
                 → load R t s ≡ inj₂ x
                 → ⊥
  load-not-inj₂ R (In t) s x leq = first-cps-not-inj₂ R R t id (λ x → inj₁ ∘ (_,_ x)) (λ _ _ _ ()) s x leq

  ------------------------------------------------------------------------------
  --                  `load` preserves the tree structure                     --

  private

    -- For every tree, we can either dissect it into a dissection plus a subtree
    -- or it has not recursive positions.
    view : {X : Set} → (R Q : Reg) → {alg : ⟦ Q ⟧ X → X} → (r : ⟦ R ⟧ (μ Q))
         → (Σ (∇ R (Computed Q X alg) (μ Q)) λ dr →  Σ (μ Q) λ q → First R r (dr , q))
         ⊎ (Σ (⟦ R ⟧ X) λ l → (NonRec R l × [ R ]-[ μ Q ] r ≈[ X ] l))
    view 0′ Q ()
    view 1′ Q tt   = inj₂ (tt , NonRec-1′ , ≈-1′)
    view I Q r     = inj₁ (tt , r , First-I)
    view (K A) Q r = inj₂ (r , NonRec-K A r , ≈-K)
    view {X} (R ⨁ Q) P (inj₁ x) with view {X} R P x
    view (R ⨁ Q) P (inj₁ x) | inj₁ (dr , mq , f)   = inj₁ ((inj₁ dr) , (mq , (First-⨁-inj₁ f)))
    view (R ⨁ Q) P (inj₁ x) | inj₂ (l , is-l , eq) = inj₂ ((inj₁ l)  , (NonRec-⨁-inj₁ R Q l is-l , ≈-⨁₁ eq))
    view {X} (R ⨁ Q) P (inj₂ y) with view {X} Q P y
    view {X} (R ⨁ Q) P (inj₂ y) | inj₁ (dq , mq , f)   = inj₁ (inj₂ dq , mq , First-⨁-inj₂ f)
    view {X} (R ⨁ Q) P (inj₂ y) | inj₂ (l , is-l , eq) = inj₂ (inj₂ l , NonRec-⨁-inj₂ R Q l is-l , ≈-⨁₂ eq)
    view {X} (R ⨂ Q) P (r , q)  with view {X} R P r
    view {X} (R ⨂ Q) P (r , q) | inj₁ (dr , mq , f)    = inj₁ ((inj₁ (dr , q)) , (mq , First-⨂₁ f))
    view {X} (R ⨂ Q) P {alg} (r , q) | inj₂ (l  , is-l , eq) with view {X} Q P {alg}  q
    view {X} (R ⨂ Q) P (r , q)
      | inj₂ (l , is-l , eq) | inj₁ (dr , mq , f)
      = inj₁ (inj₂ ((coerce r (≈-NonRec l is-l r (≈-sym eq))) , dr) , mq , First-⨂₂ (≈-NonRec l is-l r (≈-sym eq)) f)
    view {X} (R ⨂ Q) P (r , q)
      | inj₂ (l , is-l , eq) | inj₂ (l′ , is-l′ , eq′) = inj₂ ((l , l′) , NonRec-⨂ R Q l l′ is-l is-l′ , ≈-⨂ eq eq′)

    -- auxiliary property used to prove that load preserves the tree
    Prop : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} → ⟦ R ⟧ (μ Q) →  (∇ R (Computed Q X alg) (μ Q) → ∇ Q (Computed Q X alg) (μ Q))
         → List (∇ Q (Computed Q X alg) (μ Q)) → (Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg ⊎ X) → (μ Q) → Set
    Prop {X} R Q r k s f t with view {X} R Q r
    Prop {X} R Q r k s f t | inj₁ (dr , q , _)  = Σ (⟦ Q ⟧ (μ Q)) λ e → Plug Computed.Tree Q (k dr) q e × Plug-μ⇑ Q (In e) s t
    Prop {X} R Q r k s f t | inj₂ (l , isl , _) with f (l , isl) s
    Prop {X} R Q r k s f t | inj₂ (l , isl , _) | inj₁ x = PlugZ-μ⇑ Q x t
    Prop {X} R Q r k s f t | inj₂ (l , isl , _) | inj₂ y = ⊥

    -- for the initial call, Prop holds
    Prop-Init : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (r : ⟦ R ⟧ (μ R)) (s : Stack R X alg) (t : μ R)
              → Plug-μ⇑ R (In r) s t → Prop {X} R R r id s (λ l → inj₁ ∘ _,_ l) t
    Prop-Init {X} R {alg} r s t p with view {X} R R {alg} r
    Prop-Init {X} R r s t p | inj₁ (dr , mr , pl)    = r , ((First-to-Plug pl) , p)
    Prop-Init {X} .1′ .tt s t p | inj₂ (.tt , NonRec-1′ , ≈-1′) = p
    Prop-Init {X} .(K B) .l s t p | inj₂ (l , NonRec-K B .l , ≈-K) = p
    Prop-Init {X} .(R ⨁ Q) .(inj₁ x) s t p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ R Q r isl , ≈-⨁₁ {x = x} eq)
      rewrite coerce-≈ r isl x (≈-sym eq) = p
    Prop-Init {X} .(R ⨁ Q) .(inj₂ x) s t p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ R Q q isl , ≈-⨁₂ {x = x} eq)
      rewrite coerce-≈ q isl x (≈-sym eq) = p
    Prop-Init {X} .(R ⨂ Q) (r , q) s t p | inj₂ (.(r′ , q′) , NonRec-⨂ R Q r′ q′ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      rewrite coerce-≈ r′ isl₁ r (≈-sym eq₁) | coerce-≈ q′ isl₂ q (≈-sym eq₂) = p

  private
    -- auxiliary lemma that deals with all the mutually recursive continuations
    first-cps-lemma : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} → (r : ⟦ R ⟧ (μ Q)) 
                → (k : ∇ R (Computed Q X alg) (μ Q) → ∇ Q (Computed Q X alg) (μ Q))
                → (f : Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg ⊎ X)
                → Prop-Not-inj₂ X R Q alg f
                → (s : List (∇ Q (Computed Q X alg) (μ Q)))
                → (t : μ Q)
                → (z : UZipper Q X alg)
                → first-cps R Q r k f s ≡ inj₁ z → Prop R Q r k s f t → PlugZ-μ⇑ Q z t
    first-cps-lemma {X} R Q {alg} r k f ni s  t z x p with view {X} R Q {alg} r
    first-cps-lemma {X} 0′ Q {alg} () k f ni s t z x (e , plug-e , plugm) | inj₁ (dr , mq , fst)
    first-cps-lemma {X} 1′ Q {alg} r k f ni s t z x (e , plug-e , plugm) | inj₁ (() , mq , fst)
    first-cps-lemma {X} I Q {alg} (In r) k f ni s t z x (e , plug-e , plugm) | inj₁ (tt , .(In r) , First-I)
      = first-cps-lemma Q Q r id (λ l → inj₁ ∘ _,_ l) (λ _ _ _ ()) (k tt ∷ s) t z x (Prop-Init Q r (k tt ∷ s) t (Plug-∷ plug-e plugm))
    first-cps-lemma {X} (K A) Q {alg} r k f ni s t z x (e , plug-e , plugm) | inj₁ (() , mq , fst)
    first-cps-lemma {X} (R ⨁ Q) P {alg} .(inj₁ r) k f ni s t z x (e , plug-e , plugm)
      | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst)
      with view {X} R P {alg} r | first-cps-lemma R P {alg} r (k ∘ inj₁) (first-cps-⨁₁ R Q P f) (Prop-first-cps-not-inj₂-⨁₁ ni) s t z x
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ r) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont
      with First-unicity fst fst′
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ r) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ dr′) , .mq′ , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
      =  cont (e , (plug-e , plugm-e))
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ r) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ dr) , mq , First-⨁-inj₁ {r = r} {dr} fst) | inj₂ (l , isl , eq) | _
      = ⊥-elim (First-NonRec fst (≈-NonRec l isl r (≈-sym eq)))
    first-cps-lemma {X} (R ⨁ Q) P {alg} .(inj₂ q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst)
      with view {X} Q P {alg} q | first-cps-lemma Q P {alg} q (k ∘ inj₂) (first-cps-⨁₂ R Q P f) (Prop-first-cps-not-inj₂-⨁₂ ni) s t z x
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ qx) , mq , First-⨁-inj₂ {q = q} {qx} fst) | inj₁ (dr , mq′ , fst′) | cont
      with First-unicity fst fst′
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dr) , .mq′ , First-⨁-inj₂ {q = q} {.dr} fst) | inj₁ (dr , mq′ , fst′) | cont | refl
      = cont (e , plug-e , plugm-e)
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst) | inj₂ (l , isl , eq) | _
      =  ⊥-elim (First-NonRec fst (≈-NonRec l isl q (≈-sym eq)))
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst)
      with view {X} R P {alg} r
      | first-cps-lemma R P {alg} r (k ∘ inj₁ ∘ (_, q)) (first-cps-⨂-1 R Q P k f q) (Prop-first-cps-not-inj₂-⨂-1 {X} {R} {Q} {P} {alg} {k} {q} {f} ni) s t z x
    first-cps-lemma {X} (R ⨂ Q)  P (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst) | inj₁ (dr′ , mq′ , fst′) | cont
      with First-unicity fst fst′
    first-cps-lemma {X} (R ⨂ Q) P (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (dr′ , q)) , .mq′ , First-⨂₁ {rx = .dr′} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
      = cont (e , plug-e , plugm-e)
    first-cps-lemma {X} (R ⨂ Q) P (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (dr , q)) , mq , First-⨂₁ {rx = dr} fst) | inj₂ (l , isl , eq) | cont
      = ⊥-elim ((First-NonRec fst (≈-NonRec l isl r (≈-sym eq))))
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (_ , qx)) , mq , First-⨂₂ {qx = qx} nr fst)
      with view {X} R P {alg} r
      | first-cps-lemma R P {alg} r (k ∘ inj₁ ∘ (_, q)) (first-cps-⨂-1 R Q P k f q) (Prop-first-cps-not-inj₂-⨂-1 {X} {R} {Q} {P} {alg} {k} {q} {f} ni) s t z x
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₁ (dr′ , mq′ , fst′) | cont
      = ⊥-elim (First-NonRec fst′ nr)
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont
      with first-cps Q P q (k ∘ inj₂ ∘ (_,_ (coerce r′ nr-r))) (first-cps-⨂-2 R Q P f (r′ , nr-r)) s
      | inspect (first-cps Q P q (k ∘ inj₂ ∘ (_,_ (coerce r′ nr-r))) (first-cps-⨂-2 R Q P f (r′ , nr-r))) s 
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | inj₁ z′ | Is is′
      with view {X} Q P {alg} q
      | first-cps-lemma Q P {alg} q (k ∘ inj₂ ∘ (_,_ (coerce r′ nr-r))) ((first-cps-⨂-2 R Q P f (r′ , nr-r)))
                                (Prop-first-cps-not-inj₂-⨂-2 {X} {R} {Q} {P} {alg} {r′} {nr-r} ni) s t z′ is′
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | inj₁ z′ | Is is′
      | inj₁ (dr′′ , mq′′ , fst′′) | cont′
      with First-unicity fst fst′′
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr-r , dr′′)) , .mq′′ , First-⨂₂ {qx = .dr′′} nr-r fst) | inj₂ (r′ , nr-r′ , eq) | cont | inj₁ z′ | Is is′
      | inj₁ (dr′′ , mq′′ , fst′′) | cont′ | refl
      with coerce r nr-r {Computed P X alg} | coerce r′ nr-r′ {Computed P X alg} | coerce-≈-2 r nr-r r′ nr-r′ eq {Z = Computed P X alg}
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr-r , dr′′)) , .mq′′ , First-⨂₂ {_} {_} {.dr′′} nr-r fst) | inj₂ (r′ , nr-r′ , eq) | cont | inj₁ z′ | Is is′
      | inj₁ (dr′′ , mq′′ , fst′′) | cont′ | refl | c₁ | .c₁ | refl =  cont (cont′ (e , (plug-e , plugm-e)))
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst)
      | inj₂ (r′ , nr-r , eq) | cont | inj₁ z′ | Is is′ | inj₂ (l′′ , isl′′ , eq′′) | cont′
      = ⊥-elim (First-NonRec fst (≈-NonRec l′′ isl′′ q (≈-sym eq′′)))
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | inj₂ z′ | Is is′
        = ⊥-elim (first-cps-not-inj₂ Q P q (k ∘ inj₂ ∘ (_,_ (coerce r′ nr-r))) (first-cps-⨂-2 R Q P f (r′ , nr-r))
          (Prop-first-cps-not-inj₂-⨂-2 {X} {R} {Q} {P} {alg} {r′} {nr-r} {f} ni) s z′ is′)
    first-cps-lemma {X} 0′ Q () k f ni s t z x p
      | inj₂ (l , isl , plug)
    first-cps-lemma {X} 1′ Q {alg} .tt k f ni s t z x p
      | inj₂ (.tt , NonRec-1′ , ≈-1′)
      with f (tt , NonRec-1′) s
    first-cps-lemma {X} 1′ Q {alg} .tt k f ni s t .x refl p
      | inj₂ (.tt , NonRec-1′ , ≈-1′) | inj₁ x = p
    first-cps-lemma {X} I Q {alg} r k f ni s t z x p | inj₂ (_ , () , eq)
    first-cps-lemma {X} (K A) Q {alg} .l k f ni s t z x p
      | inj₂ (l , NonRec-K .A .l , ≈-K)
      with f (l , NonRec-K A l) s
    first-cps-lemma {X} (K A) Q {alg} .l k f ni s t .x refl p
      | inj₂ (l , NonRec-K .A .l , ≈-K) | inj₁ x = p
    first-cps-lemma {X} (R ⨁ Q) P {alg} .(inj₁ x) k f ni s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
      with view {X} R P {alg} x | first-cps-lemma R P x (k ∘ inj₁) (first-cps-⨁₁ R Q P f) (Prop-first-cps-not-inj₂-⨁₁ ni) s t z e
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ x) k f ni s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
      | inj₁ (dr , mq , fst) | _ = ⊥-elim (First-NonRec fst (≈-NonRec r isl x (≈-sym eq)))
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ x) k f ni s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont
      with ≈-to-≡ (≈-trans (≈-sym eq-l) eq)
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ x) k f ni s t z e p | inj₂ (.(inj₁ l) , NonRec-⨁-inj₁ .R .Q .l isl , ≈-⨁₁ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl
      with NonRec-proof-irrelevance isl isl′
    first-cps-lemma {X} (R ⨁ Q) P .(inj₁ x) k f ni s t z e p | inj₂ (.(inj₁ l) , NonRec-⨁-inj₁ .R .Q .l .isl′ , ≈-⨁₁ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl | refl = cont p
    first-cps-lemma {X} (R ⨁ Q) P {alg} .(inj₂ x) k f ni s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
      with view {X} Q P {alg} x | first-cps-lemma Q P x (k ∘ inj₂) (first-cps-⨁₂ R Q P f) (Prop-first-cps-not-inj₂-⨁₂ ni) s t z e
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ x) k f ni s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
      | inj₁ (dr , mq , fst) | cont = ⊥-elim (First-NonRec fst (≈-NonRec q isl x (≈-sym eq)))
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ x) k f ni s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont
      with ≈-to-≡ (≈-trans (≈-sym eq-l) eq)
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ x) k f ni s t z e p | inj₂ (.(inj₂ l) , NonRec-⨁-inj₂ .R .Q .l isl , ≈-⨁₂ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl
      with NonRec-proof-irrelevance isl isl′
    first-cps-lemma {X} (R ⨁ Q) P .(inj₂ x) k f ni s t z e p | inj₂ (.(inj₂ l) , NonRec-⨁-inj₂ .R .Q .l .isl′ , ≈-⨁₂ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl | refl = cont p
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      with view {X} R P {alg} r
      | first-cps-lemma R P r (k  ∘ inj₁ ∘ (_, q)) (first-cps-⨂-1 R Q P k f q) (Prop-first-cps-not-inj₂-⨂-1 {X} {R} {Q} {P} {alg} {k} {q} {f} ni) s t z e
    first-cps-lemma {X} (R ⨂ Q) P (r , q) k f ni s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₁ (dr , mq , plug) | _
      = ⊥-elim (First-NonRec plug (≈-NonRec r′ isl₁ r (≈-sym eq₁)))
    first-cps-lemma {X} (R ⨂ Q) P (r , q) k f ni s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont
      with ≈-to-≡ (≈-trans (≈-sym eq) eq₁)
    first-cps-lemma {X} (R ⨂ Q) P (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl
      with NonRec-proof-irrelevance isl₁ isl
    first-cps-lemma {X} (R ⨂ Q) P (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl
      with first-cps Q P q (k ∘ inj₂ ∘ (_,_ (coerce l isl))) (first-cps-⨂-2 R Q P f (l , isl)) s
      | inspect (first-cps Q P q (k ∘ inj₂ ∘ (_,_ (coerce l isl))) (first-cps-⨂-2 R Q P f (l , isl))) s
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | inj₁ z′ | Is f-eq
      with view {X} Q P {alg} q
      | first-cps-lemma Q P q (k ∘ inj₂ ∘ (_,_ (coerce l isl))) ((first-cps-⨂-2 R Q P f (l , isl)))
                          (Prop-first-cps-not-inj₂-⨂-2 ni) s t z′ f-eq
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | inj₁ z′ | Is f-eq | inj₁ (dr , mq , fst) | cont′
      = ⊥-elim (First-NonRec fst (≈-NonRec q′ isl₂ q (≈-sym eq₂)))
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | inj₁ z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′
      with ≈-to-≡ (≈-trans (≈-sym eq′) eq₂)
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | inj₁ z′ | Is f-eq | inj₂ (.q′ , isl′ , eq′) | cont′ | refl
      with NonRec-proof-irrelevance isl′ isl₂
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | inj₁ z′ | Is f-eq | inj₂ (.q′ , .isl₂ , eq′) | cont′ | refl | refl
      = cont (cont′ p)
    first-cps-lemma {X} (R ⨂ Q) P {alg} (r , q) k f ni s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | inj₂ y | Is is
      = ⊥-elim (Prop-first-cps-not-inj₂-⨂-1 {X} {R} {Q} {P} {alg} {k} {q} {f} ni (l , isl) s y is)
   
  -- `load` preserves the tree structure
  load-preserves : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → (r : μ R) → (s : List (∇ R (Computed R X alg) (μ R)))
                  → (z : UZipper R X alg) → load R r s ≡ inj₁ z → ∀ t → Plug-μ⇑ R r s t → PlugZ-μ⇑ R z t
  load-preserves R (In x) s z leq t p = first-cps-lemma R R x id (λ x → inj₁ ∘ (_,_ x)) (λ _ _ _ ()) s t z leq (Prop-Init R x s t p)

  ------------------------------------------------------------------------------
  --            shape of the stack after applying `load`                      --

  private 
    Prop-Stack : ∀ (X : Set) (R Q : Reg) (alg : ⟦ Q ⟧ X → X)
               → (Leaf R X → Stack Q X alg → UZipper Q X alg ⊎ X)
               → Set
    Prop-Stack X R Q alg f = ∀ (l : Leaf R X) →  (s : Stack Q X alg) → (l′ : Leaf Q X) → (s′ : Stack Q X alg) → f l s ≡ inj₁ (l′ , s′)
                             → Σ (Stack Q X alg) λ s′′ → s′ ≡ s′′ ++ s

    Prop-Stack-Init : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} → Prop-Stack X R R alg (λ x → inj₁ ∘ (_,_ x))
    Prop-Stack-Init l s .l .s refl = [] , refl

    Prop-Stack-first-cps-⨁₁ : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                             {f : Leaf (R ⨁ Q) X → List (∇ P (Computed P X alg) (μ P)) → UZipper P X alg ⊎ X}
                             → Prop-Stack X (R ⨁ Q) P alg f → Prop-Stack X R P alg (first-cps-⨁₁ R Q P f)
    Prop-Stack-first-cps-⨁₁ pr (l , isl) s l′ s′ p = pr (inj₁ l , NonRec-⨁-inj₁ _ _ l isl) s l′ s′ p

    Prop-Stack-first-cps-⨁₂ : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                             {f : Leaf (R ⨁ Q) X → List (∇ P (Computed P X alg) (μ P)) → UZipper P X alg ⊎ X}
                             → Prop-Stack X (R ⨁ Q) P alg f → Prop-Stack X Q P alg (first-cps-⨁₂ R Q P f)
    Prop-Stack-first-cps-⨁₂ pr (l , isl) s l′ s′ p = pr (inj₂ l , NonRec-⨁-inj₂ _ _ l isl) s l′ s′ p

    Prop-Stack-first-cps-⨂-2 : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                              {l   : ⟦ R ⟧ X}
                              {isl : NonRec R l}
                              {f : Leaf (R ⨂ Q) X → List (∇ P (Computed P X alg) (μ P)) → UZipper P X alg ⊎ X}
                             → Prop-Stack X (R ⨂ Q) P alg f → Prop-Stack X Q P alg (first-cps-⨂-2 R Q P f (l , isl))
    Prop-Stack-first-cps-⨂-2 pr (l , isl) s (l′ , isl′) s′ ff = pr ((_ , l) , NonRec-⨂ _ _ _ l _ isl) s (l′ , isl′) s′ ff

    mutual
      Prop-Stack-first-cps-⨂-1 : ∀ {X : Set} {R Q P : Reg} {alg : ⟦ P ⟧ X → X}
                                {k : ∇ R (Computed P X alg) (μ P) × ⟦ Q ⟧ (μ P) ⊎ ⟦ R ⟧ (Computed P X alg) × ∇ Q (Computed P X alg) (μ P) → ∇ P (Computed P X alg) (μ P)}
                                {q : ⟦ Q ⟧ (μ P)}
                                {f : Leaf (R ⨂ Q) X → List (∇ P (Computed P X alg) (μ P)) → UZipper P X alg ⊎ X}
                               → Prop-Stack X (R ⨂ Q) P alg f → Prop-Stack X R P alg (first-cps-⨂-1 R Q P k f q)
      Prop-Stack-first-cps-⨂-1 {R = R} {Q} {P} {k = k} {f = f} pr (l , isl) s l′ s′ ff
        = first-cps-lemma-stack Q P _ (k ∘ inj₂ ∘ (_,_ (coerce l isl))) (first-cps-⨂-2 R Q P f (l , isl)) l′ s s′ (Prop-Stack-first-cps-⨂-2 pr) ff 

      first-cps-lemma-stack : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} → (r : ⟦ R ⟧ (μ Q)) 
                        → (k : ∇ R (Computed Q X alg) (μ Q) → ∇ Q (Computed Q X alg) (μ Q))
                        → (f : Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg ⊎ X)
                        → (l : Leaf Q X) → (hs hs′ : Stack Q X alg)
                        → Prop-Stack X R Q alg f
                        → first-cps R Q r k f hs ≡ inj₁ (l , hs′)
                        → Σ (Stack Q X alg)
                          λ s → hs′ ≡ s ++ hs
      first-cps-lemma-stack 0′ Q () k f l hs hs′ p ff
      first-cps-lemma-stack 1′ Q tt k f l hs hs′ p ff   = p (tt , NonRec-1′) hs l hs′ ff 
      first-cps-lemma-stack I Q (In r) k f l hs hs′ p ff  with first-cps-lemma-stack Q Q r id (λ x → inj₁ ∘ (_,_ x)) l (k tt ∷ hs) hs′ Prop-Stack-Init ff
      first-cps-lemma-stack I Q (In r) k f l hs .(s′ ++ k tt ∷ hs) p ff | s′ , refl = (s′ ++ [ k tt ]) , sym (++-assoc s′ (k tt ∷ []) hs)
      first-cps-lemma-stack (K A) Q r k f l hs hs′ p ff = p (r , NonRec-K A r) hs l hs′ ff
      first-cps-lemma-stack (R ⨁ Q) P (inj₁ x) k f l hs hs′ p ff = first-cps-lemma-stack R P x (k ∘ inj₁) (first-cps-⨁₁ R Q P f) l hs hs′ (Prop-Stack-first-cps-⨁₁ p) ff
      first-cps-lemma-stack (R ⨁ Q) P (inj₂ y) k f l hs hs′ p ff = first-cps-lemma-stack Q P y (k ∘ inj₂) (first-cps-⨁₂ R Q P f) l hs hs′ (Prop-Stack-first-cps-⨁₂ p) ff 
      first-cps-lemma-stack (R ⨂ Q) P (r  , q) k f l hs hs′ p ff
        = first-cps-lemma-stack R P r (k ∘ inj₁ ∘ (_, q)) (first-cps-⨂-1 R Q P k f q) l hs hs′ (Prop-Stack-first-cps-⨂-1 {_} {R} {Q} {P} {_} {k} {q} {f} p) ff

  -- shape of the stack after applying the load function
  load-stack-lemma : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (t : μ R) (dr : ∇ R (Computed R X alg) (μ R)) (hs : Stack R X alg)
                   → (l′ : Leaf R X)
                   → (h′ : ∇ R (Computed R X alg) (μ R))
                   → (hs′ : Stack R X alg)
                   → load R t (dr ∷ hs) ≡ inj₁ (l′ , hs′)
                   → Σ (Stack R X alg) λ s
                     → hs′ ≡ s ++ (dr ∷ hs) × PlugZ-μ⇑ R (l′ , s) t
  load-stack-lemma {X} R {alg} (In r) dr hs l′ h′ hs′ x with first-cps-lemma-stack R R r id (λ x → inj₁ ∘ (_,_ x)) l′ (dr ∷ hs) hs′ Prop-Stack-Init x
  load-stack-lemma {X} R {alg} (In r) dr hs l′ h′ .(s ++ dr ∷ hs) x | s , refl
    with load-preserves R (In r) (dr ∷ hs) (l′ , s ++ dr ∷ hs) x (plug-μ⇑ R (In r) (dr ∷ hs)) (plug-μ⇑-to-Plug-μ⇑ R (In r) (dr ∷ hs) (plug-μ⇑ R (In r) (dr ∷ hs)) refl)
  ... | lp     with Plug-μ⇑-to-plug-μ⇑ R _ _ _ lp
  ... | p-to-P with plug-μ⇑-++ R (In (coerce (proj₁ l′) (proj₂ l′))) (In r) s (dr ∷ hs) p-to-P
  ... | p-++   = s , (refl , (plug-μ⇑-to-Plug-μ⇑ R _ s (In r) p-++))
