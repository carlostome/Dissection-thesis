module Dissection.Core where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  open import Function
  open import Data.List
  open import Data.List.Reverse
  open import Data.List.Properties
  open import Induction.WellFounded

  open import Regular.Core
  open import Regular.NonRec
  open import Regular.Catamorphism
  open import Regular.Dissection

  ----------------------------------------------------------------------------------
  --                              Core definitions                


  -- A leaf of a generic tree is from a code R is
  -- a tree without recursive positions.
  Leaf : Reg → Set → Set
  Leaf R X = Σ (⟦ R ⟧ X) λ l → NonRec R l

  -- embed a leaf into a tree by coercion
  LeafToTree : (R : Reg) → (X : Set) → Leaf R X → ⟦ R ⟧ (μ R)
  LeafToTree R X (l , isl) = coerce l isl
  
  -- Computed holds both a tree and a value and the
  -- proof that the value is the result of applying a
  -- catamorphism on the tree.
  record Computed (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) : Set where
    constructor _,,_,,_
    field
      Tree  : μ R  
      Value : X
      Proof : Catamorphism R alg Tree Value

  -- A Stack is a list of dissections where the recursive positions
  -- to the left of the hole are inhabited by already computed values
  -- and to the right by tree still to be proccesed.
  Stack : (R : Reg) → (X : Set) → (alg : ⟦ R ⟧ X → X) → Set
  Stack R X alg = List (∇ R (Computed R X alg) (μ R))

  -- Un type-Indexed Zipper
  UZipper : (R : Reg) → (X : Set) → (alg : ⟦ R ⟧ X → X) → Set
  UZipper R X alg = Leaf R X × Stack R X alg

  ----------------------------------------------------------------------------------
  --                              Plug and properties
  
  -- Top-bottom plugging operation
  plug-μ⇓ : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → μ R → Stack R X alg → μ R
  plug-μ⇓ R t []       = t
  plug-μ⇓ R t (h ∷ hs) = In (plug R Computed.Tree h (plug-μ⇓ R t hs))

  -- plug-μ⇓ reified as a relation
  data Plug-μ⇓ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} : μ R → Stack R X alg → μ R → Set where
    Plug-[] : ∀ {t} → Plug-μ⇓ R t [] t
    Plug-∷  : ∀ {t} {h} {hs} {e} {e′}
            → Plug-μ⇓ R t hs e → Plug Computed.Tree R h e e′
            → Plug-μ⇓ R t (h ∷ hs) (In e′)

  -- Plug-μ⇓-to-plug-μ⇓ {R = R} (Plug-∷ {h = h} eq e)
  --   with Plug-to-plug e
  -- ... | refl = cong (In ∘ plug R Computed.Tree h) (Plug-μ⇓-to-plug-μ⇓ eq)

  -- handy operator for Zipper
  PlugZ-μ⇓ : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → UZipper R X alg → μ R →  Set
  PlugZ-μ⇓ R ((l , isl) , s) t = Plug-μ⇓ R (In (coerce l isl)) s t

  -- Bottom-up plugging
  plug-μ⇑ : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → μ R → Stack R X alg → μ R
  plug-μ⇑ R t []       = t
  plug-μ⇑ R t (h ∷ hs) = plug-μ⇑ R (In (plug R Computed.Tree h t)) hs

  -- plug-μ⇑ reified as a relation
  data Plug-μ⇑ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} : μ R → Stack R X alg → μ R → Set where
    Plug-[] : ∀ {t} → Plug-μ⇑ R t [] t
    Plug-∷  : ∀ {t} {h} {hs} {e} {e′}
            → Plug Computed.Tree R h t e → Plug-μ⇑ R (In e) hs e′
            → Plug-μ⇑ R t (h ∷ hs) e′

  -- handy operator
  PlugZ-μ⇑ : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → UZipper R X alg → μ R →  Set
  PlugZ-μ⇑ R (l , s) t = Plug-μ⇑ R (In (LeafToTree _ _ l)) s t

  plug-μ⇑-to-Plug-μ⇑ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (t : μ R) (s : Stack R X alg) (o : μ R)
                     → plug-μ⇑ R t s ≡ o → Plug-μ⇑ R t s o
  plug-μ⇑-to-Plug-μ⇑ R t [] .t refl  = Plug-[]
  plug-μ⇑-to-Plug-μ⇑ R t (h ∷ s) o x = Plug-∷ (plug-to-Plug R h t (plug R Computed.Tree h t) refl) (plug-μ⇑-to-Plug-μ⇑ R (In (plug R Computed.Tree h t)) s o x)

  Plug-μ⇑-to-plug-μ⇑ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (t : μ R) (s : Stack R X alg) (o : μ R)
                     → Plug-μ⇑ R t s o → plug-μ⇑ R t s ≡ o 
  Plug-μ⇑-to-plug-μ⇑ R t .[] .t Plug-[] = refl
  Plug-μ⇑-to-plug-μ⇑ R t .(_ ∷ _) o (Plug-∷ pl plm) with Plug-to-plug R _ t _ pl
  Plug-μ⇑-to-plug-μ⇑ R t .(_ ∷ _) o (Plug-∷ pl plm) | refl = Plug-μ⇑-to-plug-μ⇑ R _ _ o plm
  
  Plug-μ⇓-unicity : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {x : μ R} {s : Stack R X alg} {r₁ r₂ : μ R}
                  → Plug-μ⇓ R x s r₁ → Plug-μ⇓ R x s r₂ → r₁ ≡ r₂
  Plug-μ⇓-unicity Plug-[] Plug-[] = refl
  Plug-μ⇓-unicity (Plug-∷ x₁ x₃) (Plug-∷ x₂ x₄) with Plug-μ⇓-unicity x₁ x₂
  ... | refl with Plug-unicity x₃ x₄
  ... | refl = refl

  plug-μ⇑-injective-on-1 : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (x y : μ R) (s : Stack R X alg)
                         → plug-μ⇑ R x s ≡ plug-μ⇑ R y s → x ≡ y
  plug-μ⇑-injective-on-1 R x .x [] refl    = refl
  plug-μ⇑-injective-on-1 R x y (h ∷ s) p   = plug-injective-on-2 R Computed.Tree h x y (In-injective (plug-μ⇑-injective-on-1 R _ _ s p))
   
  plug-μ⇑-++ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (e₁ e₂ : μ R) → (s₁ s₂ : Stack R X alg)
              → plug-μ⇑ R e₁ (s₁ ++ s₂) ≡ plug-μ⇑ R e₂ s₂ → plug-μ⇑ R e₁ s₁ ≡ e₂
  plug-μ⇑-++ R e₁ .e₁ [] [] refl = refl
  plug-μ⇑-++ R e₁ e₂ [] (x₁ ∷ s₂) x = plug-injective-on-2 R Computed.Tree x₁ e₁ e₂ (In-injective (plug-μ⇑-injective-on-1 R _ _ s₂ x))
  plug-μ⇑-++ R e₁ e₂ (x₁ ∷ s₁) s₂ x = plug-μ⇑-++ R (In (plug R Computed.Tree x₁ e₁)) e₂ s₁ s₂ x

  Plug-μ⇓-++ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (e : μ R) (s : Stack R X alg) (e′ : ⟦ R ⟧ (μ R)) (h : ∇ R (Computed R X alg) (μ R))  (t : μ R)
             → Plug-μ⇓ R (In e′) s t → Plug Computed.Tree R h e e′ → Plug-μ⇓ R e (s ++ [ h ]) t
  Plug-μ⇓-++ R e .[] e′ h .(In e′) Plug-[] p            = Plug-∷ Plug-[] p
  Plug-μ⇓-++ R e .(_ ∷ _) e′ h .(In _) (Plug-∷ plμ x) p = Plug-∷ (Plug-μ⇓-++ R e _ e′ h _ plμ p) x

  Plug-μ⇑-to-Plug-μ⇓ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (l : Leaf R X) (s : Stack R X alg) (t : μ R)
                     → PlugZ-μ⇑ R (l , s) t → PlugZ-μ⇓ R (l , reverse s) t
  Plug-μ⇑-to-Plug-μ⇓ {X} R (l , isl) s t p = aux X R _ (In (coerce l isl)) s t p
    where aux : ∀ (X : Set) (R : Reg) (alg : ⟦ R ⟧ X → X) (e : μ R) (s : Stack R X alg) (t : μ R)
               → Plug-μ⇑ R e s t → Plug-μ⇓ R e (reverse s) t
          aux X R alg e .[] .e Plug-[] = Plug-[]
          aux X R alg e .(h ∷ hs) t (Plug-∷ {h = h} {hs} {e′} x pl)
            with aux X R alg (In e′) hs t pl | reverse (h ∷ hs) | unfold-reverse h hs
          aux X R alg e .(h ∷ hs) t (Plug-∷ {h = h} {hs} {e′} x pl) | plμ | .(reverse hs ++ h ∷ []) | refl
            = Plug-μ⇓-++ R e (reverse hs) e′ h t plμ x


  Plug-μ⇑-++ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (e : μ R) (s : Stack R X alg) (e′ : ⟦ R ⟧ (μ R)) (h : ∇ R (Computed R X alg) (μ R))  (t : μ R)
             → Plug-μ⇑ R e s t → Plug Computed.Tree R h t e′ → Plug-μ⇑ R e (s ++ [ h ]) (In e′)
  Plug-μ⇑-++ R e .[] e′ h .e Plug-[] pl            = Plug-∷ pl Plug-[]
  Plug-μ⇑-++ R e .(_ ∷ _) e′ h t (Plug-∷ x plμ) pl = Plug-∷ x (Plug-μ⇑-++ R (In _) _ e′ h t plμ pl)

  Plug-μ⇓-to-Plug-μ⇑ : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (l : Leaf R X) (s : Stack R X alg) (t : μ R)
                     → PlugZ-μ⇓ R (l , s) t → PlugZ-μ⇑ R (l , reverse s) t
  Plug-μ⇓-to-Plug-μ⇑ {X} R {alg} l s t x = aux X R alg (In (LeafToTree R X l)) s t x
    where aux : ∀ (X : Set) (R : Reg) (alg : ⟦ R ⟧ X → X) (e : μ R) (s : Stack R X alg) (t : μ R)
                → Plug-μ⇓ R e s t → Plug-μ⇑ R e (reverse s) t
          aux X R alg e .[] .e Plug-[] = Plug-[]
          aux X R alg e .(h ∷ hs) .(In e′) (Plug-∷ {h = h} {hs} {e′ = e′} x pl)
            with aux X R alg e hs _ x | reverse (h ∷ hs) | unfold-reverse h hs
          aux X R alg e .(h ∷ hs) .(In e′) (Plug-∷ {h = h} {hs} {e′ = e′} x pl) | plμ | .(reverse hs ++ h ∷ []) | refl
            = Plug-μ⇑-++ R e (reverse hs) e′ h _ plμ pl

  -- Top-down type-indexed Zipper
  data Zipper⇓ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) (t : μ R) : Set where
    _,_ : (z : UZipper R X alg) → PlugZ-μ⇓ R z t → Zipper⇓ R X alg t

  -- Bottom-up type-indexed Zipper
  data Zipper⇑ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) (t : μ R) : Set where
    _,_ : (z : UZipper R X alg) → PlugZ-μ⇑ R z t → Zipper⇑ R X alg t 

  Zipper⇓-to-Zipper⇑ : (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : μ R) → Zipper⇓ R X alg t → Zipper⇑ R X alg t
  Zipper⇓-to-Zipper⇑ R X alg t ((l , s) , p) = (l , (reverse s)) , Plug-μ⇓-to-Plug-μ⇑ R l s t p

  Zipper⇑-to-Zipper⇓ : (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : μ R) → Zipper⇑ R X alg t → Zipper⇓ R X alg t
  Zipper⇑-to-Zipper⇓ R X alg t ((l , s) , p) = (l , (reverse s)) , Plug-μ⇑-to-Plug-μ⇓ R l s t p

  -- From a Tree with `Computed` in the leaves, split it into a tree
  -- only holding values and another only holding subtrees.
  -- Also we need a proof that MapFold is retained.
  compute : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X}
      → ⟦ R ⟧ (Computed Q X alg)
      → Σ (⟦ R ⟧ X × ⟦ R ⟧ (μ Q)) λ { (x , mr) → MapFold Q alg R mr x }
  compute 0′ Q ()
  compute 1′ Q tt = (tt , tt) , MapFold-1′
  compute I Q {alg} (.(In i) ,, .(alg o) ,, Cata {i} {o} x) = (alg o , In i) , (MapFold-I x)
  compute (K A) Q x = (x , x) , MapFold-K
  compute (R ⨁ Q) P (inj₁ x) with compute R P x
  ... | (rx , rp) , p = ((inj₁ rx) , (inj₁ rp)) , (MapFold-⨁₁ p)
  compute (R ⨁ Q) P (inj₂ y) with compute Q P y
  ... | (qx , qp) , p = ((inj₂ qx) , (inj₂ qp)) , (MapFold-⨁₂ p)
  compute (R ⨂ Q) P (r , q) with compute R P r | compute Q P q
  compute (R ⨂ Q) P (r , q) | (rx , rp) , p₁ | (qx , qp) , p₂ = ((rx , qx) , (rp , qp)) , MapFold-⨂ p₁ p₂

  -- When we `compute` from a tree the resulting trees can be seen as
  -- the result of fmapping Computed.Tree and Computed.Value
  compute-Fmap : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} (r : ⟦ R ⟧ (Computed Q X alg))
               → (rx : ⟦ R ⟧ X) → (rp : ⟦ R ⟧ (μ Q)) → (eq : MapFold Q alg R rp rx) →
               compute R Q r ≡ ((rx , rp) , eq) → Fmap Computed.Tree R r rp × Fmap Computed.Value R r rx
  compute-Fmap 0′ Q () rx rp eq x
  compute-Fmap 1′ Q tt .tt .tt .MapFold-1′ refl = Fmap-1′ , Fmap-1′
  compute-Fmap I Q {alg} (.(In i) ,, .(alg o) ,, Cata {i} {o} p) .(alg o) .(In i) .(MapFold-I p) refl = Fmap-I , Fmap-I
  compute-Fmap (K A) Q r .r .r .MapFold-K refl = Fmap-K , Fmap-K
  compute-Fmap (R ⨁ Q) P (inj₁ x) rx rp eq p
    with compute R P x | inspect (compute R P) x
  compute-Fmap (R ⨁ Q) P (inj₁ x) .(inj₁ rx′) .(inj₁ rp′) .(MapFold-⨁₁ eq′) refl
    | (rx′ , rp′) , eq′ | Is is
    with compute-Fmap R P x rx′ rp′ eq′ is
  ... | fmrp , fmrx = Fmap-⨁₁ fmrp , Fmap-⨁₁ fmrx
  compute-Fmap (R ⨁ Q) P (inj₂ y) rx rp eq p with compute Q P y | inspect (compute Q P) y
  compute-Fmap (R ⨁ Q) P (inj₂ y) .(inj₂ qx) .(inj₂ qp) .(MapFold-⨁₂ eq′) refl
    | (qx , qp) , eq′ | Is is
    with compute-Fmap Q P y qx qp eq′ is
  ... | fmqp , fmqx = (Fmap-⨁₂ fmqp) , (Fmap-⨁₂ fmqx)
  compute-Fmap (R ⨂ Q) P (r , q) rx rp eq x
    with compute R P r | inspect (compute R P) r | compute Q P q | inspect (compute Q P) q
  compute-Fmap (R ⨂ Q) P (r , q) .(rx′ , qx) .(rp′ , qp) .(MapFold-⨂ eq₁ eq₂) refl
    | (rx′ , rp′) , eq₁ | Is is | (qx , qp) , eq₂ | Is is′
    with compute-Fmap R P r rx′ rp′ eq₁ is | compute-Fmap Q P q qx qp eq₂ is′
  ... | fmrp , fmrx | fmqp , fmqx = (Fmap-⨂ fmrp fmqp) , (Fmap-⨂ fmrx fmqx)

  
