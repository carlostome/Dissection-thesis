module Regular where

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

  open import Data.List.Extra
  open import Data.List.Prefix
  open import Dissection.Core
  open import Dissection.Load
  open import Dissection.Relation
  open import Regular.First
  open import Regular.Last
  open import Regular.Right

  -- prepending a common stack does not influence the Lt relation
  prepend : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {l₁ l₂ : Leaf R X} {s₁ s₂ : Stack R X alg}
          → Lt R X alg (l₁ , s₁) (l₂ , s₂) → ∀ s → Lt R X alg (l₁ , s ++ s₁) (l₂ , s ++ s₂)
  prepend x [] = x
  prepend (Step {h = h′} {s₁} {s₂} x) (h ∷ s) with prepend x (s ++ [ h′ ])
  ... | lt  with (s ++ [ h′ ]) ++ s₁ | (s ++ [ h′ ]) ++ s₂ | ++-assoc s [ h′ ] s₁ | ++-assoc s [ h′ ] s₂
  prepend (Step {h = h′} {s₁} {s₂} x) (h ∷ s)
      | lt | .(s ++ h′ ∷ s₁) | .(s ++ h′ ∷ s₂) | refl | refl = Step lt
  prepend (Base p₁ p₂ r) (h ∷ s)                             = Step (prepend (Base p₁ p₂ r) s) 

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
    | inj₁ r | Is is | (rx , rp) , pr | Is is′ | fm | fm′ , _ | refl
    = unload-preserves R (In rp) (alg rx) (Cata pr) hs z e pl unl
  unload-preserves R t x eq (h ∷ hs) z e (Plug-∷ p pl) unl | inj₂ (dr , q) | Is is
    = load-preserves R q (dr ∷ hs) z unl e (Plug-∷ (right-Plug R h (t ,, x ,, eq) dr q is _ p) pl)

  ------------------------------------------------------------------------------
  --                     `step` function                                      --

  MapFold-init : ∀ {X : Set} (R Q : Reg) {alg : ⟦ R ⟧ X → X} (l : ⟦ Q ⟧ X) (isl : NonRec Q l)
               → MapFold R alg Q (coerce l isl) l
  MapFold-init R .1′ .tt NonRec-1′        = MapFold-1′
  MapFold-init R .(K B) l (NonRec-K B .l) = MapFold-K
  MapFold-init R .(R₁ ⨁ Q) .(inj₁ r) (NonRec-⨁-inj₁ R₁ Q r isl)  = MapFold-⨁₁ (MapFold-init R R₁ r isl)
  MapFold-init R .(R₁ ⨁ Q) .(inj₂ q) (NonRec-⨁-inj₂ R₁ Q q isl)  = MapFold-⨁₂ (MapFold-init R Q q isl)
  MapFold-init R .(R₁ ⨂ Q) .(r , q) (NonRec-⨂ R₁ Q r q isl isl₁) = MapFold-⨂  (MapFold-init R R₁ r isl) (MapFold-init R Q q isl₁)

  Cata-init : ∀ {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} (l : ⟦ R ⟧ X) (isl : NonRec R l)
            → Catamorphism R alg (In (coerce l isl)) (alg l)
  Cata-init R l isl = Cata (MapFold-init R R l isl)
  
  step : {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X)
       → UZipper R X alg
       → UZipper R X alg ⊎ X
  step R alg ((l , isl) , s) = unload R alg (In (coerce l isl)) (alg l) (Cata-init R l isl) s

  step-preserves : {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X)
                   → (z₁ z₂ : UZipper R X alg) → step R alg z₁ ≡ inj₁ z₂
                   → ∀ (t : μ R) → PlugZ-μ⇑ R z₁ t → PlugZ-μ⇑ R z₂ t
  step-preserves R alg ((l , isl) , s) z₂ seq t plug
    = unload-preserves R (In (coerce l isl)) (alg l) (Cata (MapFold-init R R l isl)) s z₂ t plug seq                 

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

  lemma-first-compute : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} 
           → (r  : ⟦ R ⟧ (μ Q))
           → (r′ : ⟦ R ⟧ (Computed Q X alg))
           → first R r ≡ inj₁ r′
           → (rx : ⟦ R ⟧ X) → (rm : ⟦ R ⟧ (μ Q)) → (mf : MapFold Q alg R rm rx) 
           → compute R Q r′ ≡ ((rx , rm) , mf)
           → r ≡ rm
  lemma-first-compute 0′ Q () r′ feq rx rm mf ceq
  lemma-first-compute 1′ Q tt .tt refl .tt .tt MapFold-1′ ceq = refl
  lemma-first-compute I Q r r′ () rx rm mf ceq
  lemma-first-compute (K A) Q .r′ r′ refl .r′ .r′ .MapFold-K refl = refl
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₁ x) r′ feq  rx rm mf ceq
    with first {Y = Computed P X alg} R x | inspect (first {Y = Computed P X alg} R) x
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₁ x) .(inj₁ r) refl rx rm mf ceq | inj₁ r | Is is
    with compute R P r | inspect (compute R P) r
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₁ x) .(inj₁ r) refl .(inj₁ rx′) .(inj₁ rm′) .(MapFold-⨁₁ mf′) refl | inj₁ r | Is is | (rx′ , rm′) , mf′ | Is is′
    = cong inj₁ (lemma-first-compute R P x r is rx′ rm′ mf′ is′)
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₁ x) r′ () rx rm mf ceq | inj₂ y | Is is
 
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₂ y) r′ feq rx rm mf ceq
    with first {Y = Computed P X alg} Q y | inspect (first {Y = Computed P X alg} Q) y
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₂ y) .(inj₂ x) refl rx rm mf ceq | inj₁ x | Is is
    with compute Q P x | inspect (compute Q P) x
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₂ y) .(inj₂ x) refl .(inj₂ rx′) .(inj₂ rm′) .(MapFold-⨁₂ mf′) refl | inj₁ x | Is is | (rx′ , rm′) , mf′ | Is is′
    = cong inj₂ (lemma-first-compute Q P y x is rx′ rm′ mf′ is′)
  lemma-first-compute {X} (R ⨁ Q) P {alg} (inj₂ y) r′ () rx rm mf ceq | inj₂ y₁ | Is is
  lemma-first-compute {X} (R ⨂ Q) P {alg} (r , q) r′ feq rx rm mf ceq
    with first {Y = Computed P X alg} R r | inspect (first {Y = Computed P X alg} R) r
  lemma-first-compute {X} (R ⨂ Q) P {alg} (r , q) r′ feq rx rm mf ceq | inj₁ x | Is is
    with first {Y = Computed P X alg} Q q | inspect (first {Y = Computed P X alg} Q) q
  lemma-first-compute {X} (R ⨂ Q) P {alg} (r , q) .(r′ , q′) refl rx rm mf ceq | inj₁ r′ | Is is | inj₁ q′ | Is is′
    with compute R P r′ | inspect (compute R P) r′ | compute Q P q′ | inspect (compute Q P) q′
  lemma-first-compute {X} (R ⨂ Q) P {alg} (r , q) .(r′ , q′) refl .(rx′ , qx) .(rm′ , qm) .(MapFold-⨂ mf′ mf′′) refl
    | inj₁ r′ | Is is | inj₁ q′ | Is is′ | (rx′ , rm′) , mf′ | Is is-cr | (qx , qm) , mf′′ | Is is-cq
    = cong₂ _,_ (lemma-first-compute R P r r′ is rx′ rm′ mf′ is-cr)
                (lemma-first-compute Q P q q′ is′ qx qm mf′′ is-cq)
  lemma-first-compute {X} (R ⨂ Q) P {alg} (r , q) r′ () rx rm mf ceq | inj₁ x | Is is | inj₂ y | Is is′
  lemma-first-compute {X} (R ⨂ Q) P {alg} (r , q) r′ () rx rm mf ceq | inj₂ y | Is is

  lemma-right-compute : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} 
           → (dr  : ∇ R (Computed Q X alg) (μ Q)) → (t : μ Q)
           → (y : X) → (eq : Catamorphism Q alg t y)
           → (r′ : ⟦ R ⟧ (Computed Q X alg))
           → right R dr (t ,, y ,, eq) ≡ inj₁ r′
           → (rx : ⟦ R ⟧ X) → (rm : ⟦ R ⟧ (μ Q)) → (mf : MapFold Q alg R rm rx) 
           → compute R Q r′ ≡ ((rx , rm) , mf)
           → Plug Computed.Tree R dr t rm
  lemma-right-compute 0′ Q () t y eq r′ req rx rm mf ceq
  lemma-right-compute 1′ Q () t y eq r′ req rx rm mf ceq
  lemma-right-compute I Q {alg} tt .(In _) .(alg _) (Cata x) .(In _ ,, alg _ ,, Cata x) refl .(alg _) .(In _) .(MapFold-I x) refl = Plug-I
  lemma-right-compute (K A) Q () t y eq r′ req rx rm mf ceq
  lemma-right-compute (R ⨁ Q) P (inj₁ dr) t y eq r′ req rx rm mf ceq
    with right R dr (t ,, y ,, eq) | inspect (right R dr) (t ,, y ,, eq)
  lemma-right-compute (R ⨁ Q) P (inj₁ dr) t y eq .(inj₁ x) refl rx rm mf ceq
    | inj₁ x | Is is with compute R P x | inspect (compute R P) x
  lemma-right-compute (R ⨁ Q) P (inj₁ dr) t y eq .(inj₁ x) refl .(inj₁ rx′) .(inj₁ rm′) .(MapFold-⨁₁ mf′) refl
    | inj₁ x | Is is | (rx′ , rm′) , mf′ | Is is′
    = Plug-⨁-inj₁ (lemma-right-compute R P dr t y eq x is rx′ rm′ mf′ is′)
  lemma-right-compute (R ⨁ Q) P (inj₁ dr) t y eq r′ () rx rm mf ceq | inj₂ _ | Is is
  lemma-right-compute (R ⨁ Q) P (inj₂ dq) t y eq r′ req rx rm mf ceq
    with right Q dq (t ,, y ,, eq) | inspect (right Q dq) (t ,, y ,, eq)
  lemma-right-compute (R ⨁ Q) P (inj₂ dq) t y eq .(inj₂ x) refl rx rm mf ceq
    | inj₁ x | Is is with compute Q P x | inspect (compute Q P) x
  lemma-right-compute (R ⨁ Q) P (inj₂ dq) t y eq .(inj₂ x) refl .(inj₂ rx′) .(inj₂ rm′) .(MapFold-⨁₂ mf′) refl
    | inj₁ x | Is is | (rx′ , rm′) , mf′ | Is is′
    = Plug-⨁-inj₂ (lemma-right-compute Q P dq t y eq x is rx′ rm′ mf′ is′)
  lemma-right-compute (R ⨁ Q) P (inj₂ dq) t y eq r′ () rx rm mf ceq | inj₂ _ | Is is
  lemma-right-compute (R ⨂ Q) P (inj₁ (dr , q)) t y eq r′ req rx rm mf ceq
    with right R dr (t ,, y ,, eq) | inspect (right R dr) (t ,, y ,, eq)
  lemma-right-compute {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq r′ req (_ , _) (_ , _) (MapFold-⨂ mf₁ mf₂) ceq
    | inj₁ r | Is is
    with first {Y = Computed P X alg} Q q | inspect (first {Y = Computed P X alg} Q) q
  lemma-right-compute {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq .(r , x) refl (_ , _) (_ , _) (MapFold-⨂ mf₁ mf₂) ceq
    | inj₁ r | Is is | inj₁ x | Is is′
    with compute R P r | inspect (compute R P) r | compute Q P x | inspect (compute Q P) x
  lemma-right-compute {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq .(r , x) refl (_ , _) (_ , _) (MapFold-⨂ .crmf .cqmf) refl
    | inj₁ r | Is is | inj₁ x | Is is′ | (crx , crm) , crmf | Is is-cr | (cqx , cqm) , cqmf | Is is-cq
    with lemma-first-compute Q P q x is′ cqx cqm cqmf is-cq
  lemma-right-compute {X} (R ⨂ Q) P {alg} (inj₁ (dr , .cqm)) t y eq .(r , x) refl (_ , _) (_ , _) (MapFold-⨂ .crmf .cqmf) refl | inj₁ r | Is is | inj₁ x | Is is′ | (crx , crm) , crmf | Is is-cr | (cqx , cqm) , cqmf | Is is-cq | refl = Plug-⨂-inj₁ (lemma-right-compute R P dr t y eq r is crx crm crmf is-cr )
    
  lemma-right-compute {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq r′ () (_ , _) (_ , _) (MapFold-⨂ mf₁ mf₂) ceq | inj₁ r | Is is | inj₂ y₁ | Is is′
  lemma-right-compute (R ⨂ Q) P (inj₁ (dr , q)) t y eq r′ () rx rm mf ceq | inj₂ _ | Is is
  lemma-right-compute (R ⨂ Q) P (inj₂ (r , dq)) t y eq r′ req (_ , _) (_ , _) (MapFold-⨂ mf₁ mf₂) ceq
    with right Q dq (t ,, y ,, eq) | inspect (right Q dq) (t ,, y ,, eq)
  lemma-right-compute (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(r , x) refl (_ , _) (_ , _) (MapFold-⨂ mf₁ mf₂) ceq | inj₁ x | Is is
    with compute R P r | inspect (compute R P) r | compute Q P x | inspect (compute Q P) x
  lemma-right-compute (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(r , x) refl (_ , _) (_ , _) (MapFold-⨂ .crmf .cqmf) refl | inj₁ x | Is is | (crx , crm) , crmf | Is is-cr | (cqx , cqm) , cqmf | Is is-cq = Plug-⨂-inj₂ (proj₁ (compute-Fmap R P r crx crm crmf is-cr)) (lemma-right-compute Q P dq t y eq x is cqx cqm cqmf is-cq )
  lemma-right-compute (R ⨂ Q) P (inj₂ (r , dq)) t y eq r′ () (_ , _) (_ , _) (MapFold-⨂ mf₁ mf₂) ceq | inj₂ y₁ | Is is
  
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
  unload-stack-lemma R .[] post dr t x eq l′ s′ [] last pr | inj₁ r′ | Is is = ⊥-elim (right-¬Last R dr (t ,, x ,, eq) last r′ is)
  unload-stack-lemma R .[] post dr t x eq l′ s′ [] last pr | inj₂ (dr′ , mq) | Is is with load-stack-lemma R mq dr′ post l′ dr′ s′ pr
  unload-stack-lemma R .[] post dr t x eq l′ .(s ++ dr′ ∷ post) [] last pr | inj₂ (dr′ , mq) | Is is | s , refl , plug
    = s , (dr′ , ((t , x) , (eq , (mq , (refl , (Plug-[] , (plug , is)))))))
  unload-stack-lemma R .(x ∷ _) post dr t y eq l′ s′ (_∷_ {x} px all) last pr
    with right R x (t ,, y ,, eq) | inspect (right R x) (t ,, y ,, eq)
  unload-stack-lemma R {alg} .(x ∷ _) post dr t y eq l′ s′ (_∷_ {x} px all) last pr | inj₁ r′ | Is is
    with compute R R r′ | inspect (compute R R) r′
  ... | (rx , rm) , mf | Is is′ with unload-stack-lemma R _ post dr  (In rm) (alg rx) (Cata mf) l′ s′ all last pr
  unload-stack-lemma R {alg} .(x ∷ xs) post dr t y eq l′ .(s ++ dr′ ∷ post) (_∷_ {x} {xs} px all) last pr | inj₁ r′ | Is is
    | (rx , rm) , mf | Is is′ | s , dr′ , (rm′ , x′) , ceq , e′ , refl , pl1 , pl₂ , req
    = s , (dr′ , ((rm′ , x′) , (ceq , (e′ , (refl , (Plug-∷ (lemma-right-compute R R x t y eq r′ is rx rm mf is′) pl1 , (pl₂ , req)))))))
  unload-stack-lemma R .(x ∷ _) post dr t y eq l′ s′ (_∷_ {x} px all) last pr | inj₂ (dr′ , mq) | Is is
    = ⊥-elim (right-Last R x (t ,, y ,, eq) px dr′ mq is)

  -- if all the stack satisfices Last, then unload does not deliver another
  -- Zipper
  unload-all-Last : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X)
                    → ∀ (t : μ R) (e : X) eq (s : Stack R X alg)
                    → ∀ z 
                    → unload R alg t e eq s ≡ inj₁ z
                    → L.All (Last R) s → ⊥
  unload-all-Last R alg t e eq .[] z () []
  unload-all-Last R alg t e eq .(x ∷ _) z ueq (_∷_ {x} px all₁)
    with right R x (t ,, e ,, eq) | inspect (right R x) (t ,, e ,, eq)
  unload-all-Last R alg t e eq .(x ∷ _) z ueq (_∷_ {x} px all₁) | inj₁ r | Is is
    with compute R R r | inspect (compute R R) r
  unload-all-Last R alg t e eq .(x ∷ _) z ueq (_∷_ {x} px all₁)
    | inj₁ r | Is is | (rx , rm) , mf | Is is′
    = unload-all-Last R alg (In rm) (alg rx) (Cata mf) _ z ueq all₁
  unload-all-Last R alg t e eq .(x ∷ _) z ueq (_∷_ {x} px all₁)
    | inj₂ y  | Is is = right-Last R x (t ,, e ,, eq) px _ _ is


  unload-Lt : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → ∀ (l : ⟦ R ⟧ X) (isl : NonRec R l) (l′ : Leaf R X) (s s′ : Stack R X alg) eq
            → unload R alg (In (coerce l isl)) (alg l) eq s ≡ inj₁ (l′ , s′)
            → Lt R X alg (l′ , reverse s′ ) ((l , isl) , reverse s)
  unload-Lt R alg l isl l′ s s′ eq ueq with prefix (Last-Dec R) s
  unload-Lt R alg l isl l′ .[] s′ eq () | AllOf .[] []
  unload-Lt R alg l isl l′ .(x ∷ _) s′ eq ueq | AllOf .(x ∷ _) (_∷_ {x} px all₁)
    with right R x (In (coerce l isl) ,, alg l ,, eq) | inspect (right R x) (In (coerce l isl) ,, alg l ,, eq) 
  unload-Lt R alg l isl l′ .(x ∷ _) s′ eq ueq | AllOf .(x ∷ _) (_∷_ {x} px all₁) | inj₁ x′  | Is is
    with compute R R x′ | inspect (compute R R) x′
  ... | (rx , rm) , mf | Is is′ = ⊥-elim (unload-all-Last R alg (In rm) (alg rx) (Cata mf) _ (l′ , s′) ueq all₁)
  unload-Lt R alg l isl l′ .(x ∷ _) s′ eq ueq | AllOf .(x ∷ _) (_∷_ {x} px all₁) | inj₂ y  | Is is
    = ⊥-elim (right-Last R x (In (coerce l isl) ,, alg l ,, eq) px _ _ is)
  unload-Lt R alg l isl l′ .(pre ++ x ∷ post) s′ eq ueq | OnlyPrefix pre x post all last
    with unload-stack-lemma R pre post x (In (coerce l isl)) (alg l) eq  l′ s′ all last ueq
  unload-Lt R alg l isl l′ .(pre ++ x ∷ post) .(s ++ dr ∷ post) eq ueq | OnlyPrefix pre x post all last
    | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req
    with reverse (s ++ dr ∷ post) | reverse-++-commute s (dr ∷ post) | reverse (pre ++ x ∷ post) | reverse-++-commute pre (x ∷ post)
  unload-Lt R alg l isl l′ .(pre ++ x ∷ post) .(s ++ dr ∷ post) eq ueq | OnlyPrefix pre x post all last
    | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req
    | .(reverse (dr ∷ post) ++ reverse s) | refl | .(reverse (x ∷ post) ++ reverse pre) | refl
    with reverse (dr ∷ post) | unfold-reverse dr post | reverse (x ∷ post) | unfold-reverse x post
  unload-Lt R alg l isl l′ .(pre ++ x ∷ post) .(s ++ dr ∷ post) eq ueq | OnlyPrefix pre x post all last
    | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req
    | .(reverse (dr ∷ post) ++ reverse s) | refl | .(reverse (x ∷ post) ++ reverse pre) | refl
    | .(reverse post ++ dr ∷ []) | refl | .(reverse post ++ x ∷ []) | refl
    with (reverse post ++ [ dr ]) ++ reverse s | ++-assoc (reverse post) [ dr ] (reverse s)
    | (reverse post ++ [ x ]) ++ reverse pre | ++-assoc (reverse post) [ x ] (reverse pre)
  unload-Lt R alg l isl l′ .(pre ++ x ∷ post) .(s ++ dr ∷ post) eq ueq | OnlyPrefix pre x post all last
    | s , dr , (mr , x′) , ceq , mq′ , refl , plug₁ , plug₂ , req
    | .(reverse (dr ∷ post) ++ reverse s) | refl | .(reverse (x ∷ post) ++ reverse pre) | refl
    | .(reverse post ++ dr ∷ []) | refl | .(reverse post ++ x ∷ []) | refl
    | .(reverse post ++ dr ∷ reverse s) | refl | .(reverse post ++ x ∷ reverse pre) | refl
    = prepend (Base (Plug-μ⇑-to-Plug-μ⇓ R l′ s mq′ plug₂) (Plug-μ⇑-to-Plug-μ⇓ R (l , isl) pre mr plug₁)
                    (right-Lt R R x mr x′ ceq dr mq′ req)) (reverse post)
 
  step-Lt : ∀ {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → (l l′ : Leaf R X) (s s′ : Stack R X alg)
          → step R alg (l , s) ≡ inj₁ (l′ , s′) → Lt R X alg (l′ , reverse s′ ) (l , reverse s)
  step-Lt {X} R alg (l , isl) l′ s s′ x = unload-Lt R alg l isl l′ s s′ (Cata-init R l isl) x

  step-Ix : {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) → (t : μ R)
          → Zipper⇑ R X alg t
          → Zipper⇑ R X alg t ⊎ X
  step-Ix R alg t (z , x) with step R alg z | inspect (step R alg) z
  step-Ix R alg t (z , x) | inj₁ z′ | Is is = inj₁ (z′ , (step-preserves R alg z z′ is t x))
  step-Ix R alg t (z , x) | inj₂ x′ | Is is = inj₂ x′

  step-Ix-Lt : {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) → (t : μ R)
             → (z₁ z₂ : Zipper⇑ R X alg t)
             → step-Ix R alg t z₁ ≡ inj₁ z₂ → IxLt⇑ R X alg t z₂ z₁
  step-Ix-Lt R alg t (((l , isl) , s) , plug₁) (((l′ , isl′) , s′) , plug₂) x with step R alg ((l , isl) , s) | inspect (step R alg) ((l , isl) , s)
  step-Ix-Lt R alg t (((l , isl) , s) , plug₁) (((.l′ , .isl′) , .s′) , .(step-preserves R alg ((l , isl) , s) ((l′ , isl′) , s′) is t plug₁)) refl
    | inj₁ ((l′ , isl′) , s′) | Is is = ixLt⇑ (((l′ , isl′) , s′) , step-preserves R alg ((l , isl) , s) ((l′ , isl′) , s′) is t plug₁)
                                              (((l , isl) , s) , plug₁) (Lt-to-IxLt⇓
                                              (Plug-μ⇑-to-Plug-μ⇓ R (l′ , isl′) s′ t (step-preserves R alg ((l , isl) , s) ((l′ , isl′) , s′) is t plug₁))
                                              (Plug-μ⇑-to-Plug-μ⇓ R (l , isl) s t plug₁) (step-Lt R alg (l , isl) (l′ , isl′) s s′ is))
  step-Ix-Lt R alg t (((l , isl) , s) , plug₁) (((l′ , isl′) , s′) , plug₂) () | inj₂ y | Is is

  rec : {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R) → (z : Zipper⇑ R X alg t) → Acc (IxLt⇑ R X alg t) z → X
  rec R alg t z (acc rs) with step-Ix R alg t z | inspect (step-Ix R alg t) z
  rec R alg t z (acc rs) | inj₁ x | Is is = rec R alg t x (rs x (step-Ix-Lt R alg t z x is))
  rec R alg t z (acc rs) | inj₂ y | Is is = y

  tail-rec-cata : {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X) → μ R → X
  tail-rec-cata {X} R alg x with load {X} R {alg} x [] | inspect (load {X} R {alg} x) []
  tail-rec-cata {X} R alg x | inj₁ ((l , isl) , s) | Is is
    = rec R alg x (((l , isl) , s) , (load-preserves R x [] ((l , isl) , s) is x Plug-[]))
                  (IxLt⇑-WF R X alg x (((l , isl) , s) , load-preserves R x [] ((l , isl) , s) is x Plug-[]))
  tail-rec-cata {X} R alg x | inj₂ y | Is _ = y


  ------------------------------------------------------------------------------
  --                           Correctness proof                              --

  unload-correct : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X)
                     (t : μ R) (x : X) (eq : Catamorphism R alg t x) (s : Stack R X alg)
                 → ∀ (y : X) → unload R alg t x eq s ≡ inj₂ y
                 → ∀ (e : μ R) → Plug-μ⇑ R t s e → Catamorphism R alg e y
  unload-correct R alg t x eq [] .x refl .t Plug-[] = eq
  unload-correct R alg t x eq (h ∷ hs) y ul e pl
    with right R h (t ,, x ,, eq) | inspect (right R h) (t ,, x ,, eq)
  unload-correct R alg t x eq (h ∷ hs) y ul e pl | inj₁ r | Is is
    with compute R R r | inspect (compute R R) r
  unload-correct {X} R alg t x eq (h ∷ hs) y ul e (Plug-∷ pl plμ) | inj₁ r | Is is | (rx , rm) , mFold | Is is′
    with Plug-unicity pl (lemma-right-compute R R h t x eq r is rx rm mFold is′)
  ... | refl = unload-correct R alg (In _) (alg rx) (Cata mFold) hs y ul e plμ
  unload-correct R alg t x eq (h ∷ hs) y ul e pl | inj₂ (dr , mq) | Is _ = ⊥-elim (load-not-inj₂ R mq (dr ∷ hs) y ul)

  step-Ix-correct : {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R) → (z : Zipper⇑ R X alg t)
                  → ∀ (x : X) → step-Ix R alg t z ≡ inj₂ x → Catamorphism R alg t x
  step-Ix-correct R alg t (l , eq) x seq with step R alg l | inspect (step R alg) l
  step-Ix-correct R alg t (l , eq) x () | inj₁ _ | Is is
  step-Ix-correct R alg t (((l , isl) , s) , eq) .y refl | inj₂ y | Is is
    = unload-correct R alg (In (coerce l isl)) (alg l) (Cata (MapFold-init R R l isl)) s y is t eq
 
  rec-correct : {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R) → (z : Zipper⇑ R X alg t) → (ac : Acc (IxLt⇑ R X alg t) z)
              → Catamorphism R alg t (rec R alg t z ac) 
  rec-correct R alg t z (acc rs) with step-Ix R alg t z | inspect (step-Ix R alg t) z
  rec-correct R alg t z (acc rs)  | inj₁ z′ | Is is  = rec-correct R alg t z′ (rs z′ (step-Ix-Lt R alg t z z′ is))
  rec-correct R alg t z (acc rs)  | inj₂ y  | Is is  = step-Ix-correct R alg t z y is

  correctness : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R)
              → Catamorphism R alg t (tail-rec-cata R alg t)
  correctness {X} R alg t with load {X} R {alg} t [] | inspect (load {X} R {alg} t) []
  correctness {X} R alg t | inj₁ ((l , isl) , s)  | Is is
    = rec-correct R alg t (((l , isl) , s) , (load-preserves R t [] ((l , isl) , s) is t Plug-[]))
                                             (IxLt⇑-WF R X alg t (((l , isl) , s) , load-preserves R t [] ((l , isl) , s) is t Plug-[]))
  correctness {X} R alg t | inj₂ y  | Is is       = ⊥-elim (load-not-inj₂ R t [] y is)
 

  -- the tail-recursive catamorphism is correct
  correct : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R)
          → cata R alg t ≡ tail-rec-cata R alg t
  correct R alg t = Cata-to-cata R alg t (tail-rec-cata R alg t) (correctness R alg t)
