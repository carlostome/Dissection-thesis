\begin{code}
-- {-# OPTIONS --allow-unsolved-metas #-}
module Thesis.Dissection.Load where

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
  
  ------------------------------------------------------------------------------
  --                           load function

  private
    -- auxiliary function in CPS style that computes a dissection to the
    -- leftmost hole if it exists.
    mutual
      first-⨁₁ : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
                → (Leaf (R ⨁ Q) X → Stack P X alg → UZipper P X alg)
                → (Leaf R X        → Stack P X alg → UZipper P X alg)
      first-⨁₁ R Q P f (l , x) s = f ((inj₁ l , NonRec-⨁-inj₁ R Q l x)) s

      first-⨁₂ : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
                → (Leaf (R ⨁ Q) X → Stack P X alg → UZipper P X alg)
                → (Leaf Q X        → Stack P X alg → UZipper P X alg)
      first-⨁₂ R Q P f (l , x) s = f (inj₂ l , NonRec-⨁-inj₂ R Q l x) s

      first-⨂-2 : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
                 → (Leaf (R ⨂ Q) X     → Stack P X alg → UZipper P X alg)
                 → (Leaf R X → Leaf Q X → Stack P X alg → UZipper P X alg)
      first-⨂-2 R Q P f (r , isl-r) (q , isl-q) s = f ((r , q) , NonRec-⨂ R Q r q isl-r isl-q) s

      first-⨂-1 : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
                 → (∇ R (Computed P X alg) (μ P) × ⟦ Q ⟧ (μ P) ⊎ ⟦ R ⟧ (Computed P X alg) × ∇ Q (Computed P X alg) (μ P)
                 → ∇ P (Computed P X alg) (μ P))
                 → (Leaf (R ⨂ Q) X → Stack P X alg → UZipper P X alg)
                 → ⟦ Q ⟧ (μ P)
                 → (Leaf R X → Stack P X alg → UZipper P X alg)
      first-⨂-1 R Q P k f q (r , isl) = first Q P q (k ∘ inj₂ ∘ _,_ (coerce r isl)) (first-⨂-2 R Q P f (r , isl))

      first : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X}
            → ⟦ R ⟧ (μ Q)
            → (∇ R (Computed Q X alg) (μ Q) → (∇ Q (Computed Q X alg) (μ Q)))
            → (Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg)
            → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg
      first 0′ Q () _
      first 1′ Q x k f s              = f (tt , NonRec-1′) s
      first I Q (In x) k f s          = first Q Q x id _,_ (k tt ∷ s)
      first (K A) Q x k f s           = f (x , NonRec-K A x) s
      first (R ⨁ Q) P (inj₁ x) k f s = first R P x  (k ∘ inj₁) (first-⨁₁ R Q P f) s
      first (R ⨁ Q) P (inj₂ y) k f s = first Q P y  (k ∘ inj₂) (first-⨁₂ R Q P f) s
      first (R ⨂ Q) P (r , q) k f s  = first R P r  (k ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q) s

  -- load function
  load : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → μ R → Stack R X alg → UZipper R X alg ⊎ X
  load R (In t) s = inj₁ (first R R t id _,_ s)


  ------------------------------------------------------------------------------
  --                  load preserves the tree structure

  private

  -- Reification of the function first
    data First {X Y : Set} : (R : Reg) → ⟦ R ⟧ X → ∇ R Y X × X → Set where
      First-⨁-inj₁ : ∀ {R Q} {r} {rx x} → First R r (rx , x) → First (R ⨁ Q) (inj₁ r) (inj₁ rx , x)
      First-⨁-inj₂ : ∀ {R Q} {q} {qx x} → First Q q (qx , x) → First (R ⨁ Q) (inj₂ q) (inj₂ qx , x)
      First-I       : ∀ {x}                                   → First I x (tt , x)
      First-⨂₁     : ∀ {R Q} {rx x} {r q} → First R r (rx , x)     → First (R ⨂ Q) (r , q) (inj₁ (rx , q) , x)
      First-⨂₂     : ∀ {R Q} {qx x} {r q} → (isl : NonRec R r) → First Q q (qx , x) → First  (R ⨂ Q) (r , q) (inj₂ (coerce r isl , qx) , x)

    -- Given a proof that we can dissect some tree, it can not be non-recursive
    First-NonRec : ∀ {X Y : Set} {R : Reg} {r : ⟦ R ⟧ X} {rx : ∇ R Y X} {x : X}
                 → First R r (rx , x) → NonRec R r → ⊥
    First-NonRec () NonRec-1′
    First-NonRec () (NonRec-K B b)
    First-NonRec (First-⨁-inj₁ x₁) (NonRec-⨁-inj₁ R Q r x₂) = First-NonRec x₁ x₂
    First-NonRec (First-⨁-inj₂ x₁) (NonRec-⨁-inj₂ R Q q x₂) = First-NonRec x₁ x₂
    First-NonRec (First-⨂₁ x₁) (NonRec-⨂ R Q r q x₂ x₃)     = First-NonRec x₁ x₂
    First-NonRec (First-⨂₂ isl x₁) (NonRec-⨂ R Q r q x₂ x₃) = First-NonRec x₁ x₃

    -- Plug fails in a contradiction if it is not recursive
    Plug-NonRec : ∀ {X Y : Set} {f : Y → X} {R : Reg} → (x : X) → (dₓ : ∇ R Y X) → (tₓ : ⟦ R ⟧ X) → NonRec R tₓ → Plug f R dₓ x tₓ → ⊥
    Plug-NonRec x .tt .x () Plug-I
    Plug-NonRec x .(inj₁ _) .(inj₁ r) (NonRec-⨁-inj₁ R Q r p) (Plug-⨁-inj₁ nr)          = Plug-NonRec x _ r p nr
    Plug-NonRec x .(inj₂ _) .(inj₂ q) (NonRec-⨁-inj₂ R Q q p) (Plug-⨁-inj₂ nr)          = Plug-NonRec x _ q p nr
    Plug-NonRec x .(inj₁ (_ , q)) .(r , q) (NonRec-⨂ R Q r q p p₁) (Plug-⨂-inj₁ nr)     = Plug-NonRec x _ r p nr
    Plug-NonRec x .(inj₂ (_ , _)) .(r , q) (NonRec-⨂ R Q r q x₁ x₄) (Plug-⨂-inj₂ x₂ x₃) = Plug-NonRec x _ q x₄ x₃

    -- First is a functional relation
    First-unicity : ∀ {X Y : Set} {R : Reg} {r : ⟦ R ⟧ X} {x y : ∇ R Y X × X} → First R r x → First R r y → x ≡ y
    First-unicity (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) with First-unicity f₁ f₂
    First-unicity (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) | refl = refl
    First-unicity (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) with First-unicity f₁ f₂
    First-unicity (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) | refl = refl
    First-unicity First-I First-I = refl
    First-unicity (First-⨂₁ f₁) (First-⨂₁ f₂) with First-unicity f₁ f₂
    First-unicity (First-⨂₁ f₁) (First-⨂₁ f₂) | refl = refl
    First-unicity (First-⨂₁ f₁) (First-⨂₂ x f₂) = ⊥-elim (First-NonRec f₁ x)
    First-unicity (First-⨂₂ x f₁) (First-⨂₁ f₂) = ⊥-elim (First-NonRec  f₂ x)
    First-unicity (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) with First-unicity f₁ f₂
    First-unicity (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) | refl with NonRec-proof-irrelevance x x′
    ... | refl = refl

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


    -- A First dissection can be seen also as a restricted Plug
    First-to-Plug : ∀ {X Y : Set} {f : Y → X} {R : Reg} {r : ⟦ R ⟧ X} {dr : ∇ R Y X} {x : X} → First R r (dr , x) → Plug f R dr x r
    First-to-Plug (First-⨁-inj₁ x₁) = Plug-⨁-inj₁ (First-to-Plug x₁)
    First-to-Plug (First-⨁-inj₂ x₁) = Plug-⨁-inj₂ (First-to-Plug x₁)
    First-to-Plug First-I            = Plug-I
    First-to-Plug (First-⨂₁ x₁)     = Plug-⨂-inj₁ (First-to-Plug x₁)
    First-to-Plug (First-⨂₂ x₁ x₂)  = Plug-⨂-inj₂ (coerce-Fmap _ _ x₁) (First-to-Plug x₂)

    -- auxiliary property used to prove that load preserves the tree
    Prop : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} → ⟦ R ⟧ (μ Q) →  (∇ R (Computed Q X alg) (μ Q) → ∇ Q (Computed Q X alg) (μ Q))
         → List (∇ Q (Computed Q X alg) (μ Q)) → (Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg) → (μ Q) → Set
    Prop {X} R Q r k s f t with view {X} R Q r
    Prop {X} R Q r k s f t | inj₁ (dr , q , _)  = Σ (⟦ Q ⟧ (μ Q)) λ e → Plug Computed.Tree Q (k dr) q e × Plug-μ⇑ Q (In e) s t
    Prop {X} R Q r k s f t | inj₂ (l , isl , _) = PlugZ-μ⇑ Q (f (l , isl) s) t

    -- for the initial call, Prop holds
    Prop-Init : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (r : ⟦ R ⟧ (μ R)) (s : Stack R X alg) (t : μ R)
              → Plug-μ⇑ R (In r) s t → Prop {X} R R r id s _,_ t
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

    
    first-lemma : {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} → (r : ⟦ R ⟧ (μ Q)) 
                → (k : ∇ R (Computed Q X alg) (μ Q) → ∇ Q (Computed Q X alg) (μ Q))
                → (f : Leaf R X → List (∇ Q (Computed Q X alg) (μ Q)) → UZipper Q X alg)
                → (s : List (∇ Q (Computed Q X alg) (μ Q)))
                → (t : μ Q)
                → (z : UZipper Q X alg)
                → first R Q r k f s ≡ z → Prop R Q r k s f t → PlugZ-μ⇑ Q z t
    first-lemma {X} R Q {alg} r k f s  t z x p with view {X} R Q {alg} r
    first-lemma {X} 0′ Q {alg} () k f s t z x (e , plug-e , plugm) | inj₁ (dr , mq , fst)
    first-lemma {X} 1′ Q {alg} r k f s t z x (e , plug-e , plugm) | inj₁ (() , mq , fst)
    first-lemma {X} I Q {alg} r k f s t z x (e , plug-e , plugm) | inj₁ (dr , mq , fst) = {!!}
    first-lemma {X} (K A) Q {alg} r k f s t z x (e , plug-e , plugm) | inj₁ (() , mq , fst)
    first-lemma {X} (R ⨁ Q) P {alg} .(inj₁ r) k f s t z x (e , plug-e , plugm)
      | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst)
      with view {X} R P {alg} r | first-lemma R P {alg} r (k ∘ inj₁) (first-⨁₁ R Q P f) s t z x
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont
      with First-unicity fst fst′
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ dr′) , .mq′ , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
      = cont (e , (plug-e , plugm-e))
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ dr) , mq , First-⨁-inj₁ {r = r} {dr} fst) | inj₂ (l , isl , eq) | _
      = ⊥-elim (First-NonRec fst (≈-NonRec l isl r (≈-sym eq)))
    first-lemma {X} (R ⨁ Q) P {alg} .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst)
      with view {X} Q P {alg} q | first-lemma Q P {alg} q (k ∘ inj₂) (first-⨁₂ R Q P f) s t z x
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ qx) , mq , First-⨁-inj₂ {q = q} {qx} fst) | inj₁ (dr , mq′ , fst′) | cont
      with First-unicity fst fst′
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dr) , .mq′ , First-⨁-inj₂ {q = q} {.dr} fst) | inj₁ (dr , mq′ , fst′) | cont | refl
      = cont (e , plug-e , plugm-e)
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst) | inj₂ (l , isl , eq) | _
      =  ⊥-elim (First-NonRec fst (≈-NonRec l isl q (≈-sym eq)))
    first-lemma {X} (R ⨂ Q) P {alg} (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst)
      with view {X} R P {alg} r | first-lemma R P {alg} r (k ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q) s t z x
    first-lemma {X} (R ⨂ Q)  P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst) | inj₁ (dr′ , mq′ , fst′) | cont
      with First-unicity fst fst′
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (dr′ , q)) , .mq′ , First-⨂₁ {rx = .dr′} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
      = cont (e , plug-e , plugm-e)
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (dr , q)) , mq , First-⨂₁ {rx = dr} fst) | inj₂ (l , isl , eq) | cont
      = ⊥-elim ((First-NonRec fst (≈-NonRec l isl r (≈-sym eq))))


    first-lemma {X} (R ⨂ Q) P {alg} (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (_ , qx)) , mq , First-⨂₂ {qx = qx} nr fst)
      with view {X} R P {alg} r  | first-lemma R P {alg} r (k ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q) s t z x
    first-lemma {X} (R ⨂ Q) P {alg} (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₁ (dr′ , mq′ , fst′) | cont
      = ⊥-elim (First-NonRec fst′ nr)
    first-lemma {X} (R ⨂ Q) P {alg} (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont
      with first Q P q (k ∘ inj₂ ∘ (_,_ (coerce r′ nr-r))) (first-⨂-2 R Q P f (r′ , nr-r)) s
      | inspect (first Q P q (k ∘ inj₂ ∘ (_,_ (coerce r′ nr-r))) (first-⨂-2 R Q P f (r′ , nr-r))) s 
    first-lemma {X} (R ⨂ Q) P {alg} (r , q) k f s t z x (e , plug-e , plugm-e) | inj₁ (.(inj₂ (coerce r nr , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | vv , proj₃ | cont′ = {!proj₃!}
   -- first-⨂-2 : {X : Set} (R Q P : Reg) {alg : ⟦ P ⟧ X → X}
   --              → (Leaf (R ⨂ Q) X     → Stack P X alg → UZipper P X alg)
   --              → (Leaf R X → Leaf Q X → Stack P X alg → UZipper P X alg)
   
  -- first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
    --   | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁
    --   with view {X} Q P q | first-lemma Q P q (λ z₁ → k (inj₂ (r , z₁))) ((first-⨂-2 R Q P f (r′ , nr-r))) s t z′ eq₁
    -- first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
    --   | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁ | inj₁ (dr′′ , mq′′ , fst′′) | cont′
    --   with First-unicity fst fst′′
    -- first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
    --   | inj₁ (.(inj₂ (r , dr′′)) , .mq′′ , First-⨂₂ {qx = .dr′′} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁ | inj₁ (dr′′ , mq′′ , fst′′) | cont′ | refl
    --   = cont (cont′ (e , plug-e , plugm-e))
    -- first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
    --   | inj₁ (.(inj₂ (r , dq)) , mq , First-⨂₂ {qx = dq} isl fst) | inj₂ (l′ , isl′ , eq) | g | z′ | Is eq₁ | inj₂ (l′′ , isl′′ , eq′′) | cont′
    --   = ⊥-elim (First-NonRec Q q dq mq fst (≈-NonRec l′′ isl′′ q (≈-sym eq′′)))
    first-lemma {X} R Q {alg} r k f s t z x p | inj₂ y = {!!}
  -- --   first-lemma {X} 0′ Q () k f s t z x p
  -- --     | inj₂ (l , isl , plug)
  -- --   first-lemma {X} 1′ Q .tt k f s t .(f (tt , NonRec-1′) s) refl p
  -- --     | inj₂ (.tt , NonRec-1′ , ≈-1′)    = p
  -- --   first-lemma {X} I Q r k f s t z x p
  -- --     | inj₂ (l , () , plug)
  -- --   first-lemma {X} (K A) Q r k f s t .(f (r , NonRec-K A r) s) refl p
  -- --     | inj₂ (.r , NonRec-K .A .r , ≈-K) = p
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
  -- --     with view {X} R P x | first-lemma R P x (k ∘ inj₁) (first-⨁₁ R Q P f) s t z e
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
  -- --     | inj₁ (dr , mq , fst) | _ = ⊥-elim (First-NonRec R x dr mq fst (≈-NonRec r isl x (≈-sym eq)))
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
  -- --     | inj₂ (l , isl′ , eq-l) | cont
  -- --     with ≈-to-≡ (≈-trans (≈-sym eq-l) eq)
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ l) , NonRec-⨁-inj₁ .R .Q .l isl , ≈-⨁₁ {x = x} eq)
  -- --     | inj₂ (l , isl′ , eq-l) | cont | refl
  -- --     with NonRec-proof-irrelevance isl isl′
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ l) , NonRec-⨁-inj₁ .R .Q .l .isl′ , ≈-⨁₁ {x = x} eq)
  -- --     | inj₂ (l , isl′ , eq-l) | cont | refl | refl = cont p
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
  -- --     with view {X} Q P x | first-lemma Q P x (k ∘ inj₂) (first-⨁₂ R Q P f) s t z e
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
  -- --     | inj₁ (dr , mq , fst) | cont = ⊥-elim (First-NonRec Q x dr mq fst (≈-NonRec q isl x (≈-sym eq)))
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
  -- --     | inj₂ (l , isl′ , eq-l) | cont
  -- --     with ≈-to-≡ (≈-trans (≈-sym eq-l) eq)
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ l) , NonRec-⨁-inj₂ .R .Q .l isl , ≈-⨁₂ {x = x} eq)
  -- --     | inj₂ (l , isl′ , eq-l) | cont | refl
  -- --     with NonRec-proof-irrelevance isl isl′
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ l) , NonRec-⨁-inj₂ .R .Q .l .isl′ , ≈-⨁₂ {x = x} eq)
  -- --     | inj₂ (l , isl′ , eq-l) | cont | refl | refl = cont p
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     with view {X} R P r | first-lemma R P r (k  ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q r) s t z e
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₁ (dr , mq , plug) | _
  -- --     = ⊥-elim (First-NonRec R r dr mq plug (≈-NonRec r′ isl₁ r (≈-sym eq₁)))
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont
  -- --     with ≈-to-≡ (≈-trans (≈-sym eq) eq₁)
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl
  -- --     with NonRec-proof-irrelevance isl₁ isl
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl | refl
  -- --     with first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (l , isl)) s | inspect (first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (l , isl))) s
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq
  -- --     with view {X} Q P q | first-lemma Q P q (k ∘ inj₂ ∘ (_,_ r)) ((first-⨂-2 R Q P f (l , isl))) s t z′ f-eq
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₁ (dr , mq , fst) | cont′
  -- --     = ⊥-elim (First-NonRec Q q dr mq fst (≈-NonRec q′ isl₂ q (≈-sym eq₂)))
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′
  -- --     with ≈-to-≡ (≈-trans (≈-sym eq′) eq₂)
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , .l′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′ | refl
  -- --     with NonRec-proof-irrelevance isl′ isl₂
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , .l′) , NonRec-⨂ .R .Q _ _ .isl .isl′ , ≈-⨂ eq₁ eq₂)
  -- --     | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′ | refl | refl
  -- --     = cont (cont′ p)

  -- -- load-preserves : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → (r : μ R) → (s : List (∇ R (Computed R X alg) (μ R))) → (t : μ R)
  -- --                → Plug-μ⇑ R r s t → (z : UZipper R X alg) → load R r s ≡ inj₁ z → PlugZ-μ⇑ R z t
  -- -- load-preserves R (In r) s t x z p = {!!}
