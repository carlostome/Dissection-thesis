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
  open import Data.Maybe

  open import Thesis.Regular.Core
  open import Thesis.Regular.Equality renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open import Thesis.Regular.Dissection
  open import Thesis.Regular.NonRec   renaming (proof-irrelevance to NonRec-proof-irrelevance)
  -- Un-indexed type of a Zipper
  UZipper : Reg → Set
  UZipper R = ⟦ R ⟧ (μ R) × List (∇ R (μ R) (μ R))

  -- Top-bottom plugging operation
  plug-μ⇓ : (R : Reg) → μ R → List (∇ R (μ R) (μ R)) → μ R
  plug-μ⇓ R t []       = t
  plug-μ⇓ R t (h ∷ hs) = In (plug R h (plug-μ⇓ R t hs))

  -- plug-μ⇓ reified as a type
  data Plug-μ⇓ (R : Reg) : μ R → List (∇ R (μ R) (μ R)) → μ R → Set where
    Plug-[] : ∀ {t} → Plug-μ⇓ R t [] t
    Plug-∷  : ∀ {t} {h} {hs} {e} {e′}
            → Plug-μ⇓ R t hs e → Plug R h e e′
            → Plug-μ⇓ R t (h ∷ hs) (In e′)

  PlugZ-μ⇓ : (R : Reg) → UZipper R → μ R →  Set
  PlugZ-μ⇓ R (l , s) t = Plug-μ⇓ R (In l) s t

  -- Bottom-up plugging
  plug-μ⇑ : (R : Reg) → μ R → List (∇ R (μ R) (μ R)) → μ R
  plug-μ⇑ R t []       = t
  plug-μ⇑ R t (h ∷ hs) = plug-μ⇑ R (In (plug R h t)) hs

  data Plug-μ⇑ (R : Reg) : μ R → List (∇ R (μ R) (μ R)) → μ R → Set where
    Plug-[] : ∀ {t} → Plug-μ⇑ R t [] t
    Plug-∷  : ∀ {t} {h} {hs} {e} {e′}
            → Plug R h t e → Plug-μ⇑ R (In e) hs e′
            → Plug-μ⇑ R t (h ∷ hs) e′

  PlugZ-μ⇑ : (R : Reg) → UZipper R → μ R →  Set
  PlugZ-μ⇑ R (l , s) t = Plug-μ⇑ R (In l) s t

  plug-μ⇓-++ : (R : Reg) → (t : μ R) → (hs : List (∇ R (μ R) (μ R))) → (h : ∇ R (μ R) (μ R))
             → plug-μ⇓ R t (hs ++ [ h ]) ≡ plug-μ⇓ R (In (plug R h t)) hs
  plug-μ⇓-++ R t [] h       = refl
  plug-μ⇓-++ R t (x ∷ hs) h = cong (In ∘ (plug R x)) (plug-μ⇓-++ R t hs h)

  plug-μ⇑-++ : (R : Reg) → (t : μ R) → (hs : List (∇ R (μ R) (μ R))) → (h : ∇ R (μ R) (μ R))
             → plug-μ⇑ R t (hs ++ [ h ]) ≡ In (plug R h (plug-μ⇑ R t hs))
  plug-μ⇑-++ R t [] h       = refl
  plug-μ⇑-++ R t (x ∷ hs) h = plug-μ⇑-++ R (In (plug R x t)) hs h
  
  -- plug-μ⇓ and plug-μ⇑ are related by reversing the stack
  plug-μ⇓-to-plug-μ⇑ : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
                     → plug-μ⇓ R t s ≡ plug-μ⇑ R t (reverse s)
  plug-μ⇓-to-plug-μ⇑ R t s = aux R t s (reverseView s)
        where aux : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
                  → Reverse s → plug-μ⇓ R t s ≡ plug-μ⇑ R t (reverse s)
              aux R t .[] []                          = refl
              aux R t .(hs ++ h ∷ []) (hs ∶ re ∶ʳ h)
                with reverse (hs ++ [ h ]) | reverse-++-commute hs [ h ]
              aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ reverse hs)
                | refl with plug-μ⇓ R t (hs ++ [ h ]) | plug-μ⇓-++ R t hs h
              aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ reverse hs)
                | refl | .(plug-μ⇓ R (In (plug R h t)) hs) | refl
                = aux R (In (plug R h t)) hs re
  
  plug-μ⇑-to-plug-μ⇓ : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
                     → plug-μ⇑ R t s ≡ plug-μ⇓ R t (reverse s)
  plug-μ⇑-to-plug-μ⇓ R t s = aux R t s (reverseView s)
    where aux : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
              → Reverse s → plug-μ⇑ R t s ≡ plug-μ⇓ R t (reverse s)
          aux R t .[] [] = refl
          aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h)
            with reverse (hs ++ [ h ]) | reverse-++-commute hs [ h ]
          aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ reverse hs)
            | refl with plug-μ⇑ R t (hs ++ [ h ]) | plug-μ⇑-++ R t hs h
          aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ foldl _ [] hs)
            | refl | .(In (plug R h (plug-μ⇑ R t hs))) | refl
            = cong (In ∘ plug R h) (aux R t hs re)
  
  PlugZ-μ⇓-to-PlugZ-μ⇑ : (R : Reg) → (l : ⟦ R ⟧ (μ R)) → (s : List (∇ R (μ R) (μ R))) → (t : μ R)
                       → PlugZ-μ⇓ R (l , s) t → PlugZ-μ⇑ R (l , reverse s) t
  PlugZ-μ⇓-to-PlugZ-μ⇑ R l .[] .(In l) Plug-[] = Plug-[]
  PlugZ-μ⇓-to-PlugZ-μ⇑ R l .(_ ∷ _) .(In _) (Plug-∷ x x₁) = {!!} 

  data Zipper⇓ (R : Reg) (t : μ R) : Set where
    _,_ : (z : UZipper R) → PlugZ-μ⇓ R z t → Zipper⇓ R t

  data Zipper⇑ (R : Reg) (t : μ R) : Set where
    _,_ : (z : UZipper R) → PlugZ-μ⇑ R z t → Zipper⇑ R t 

  Zipper⇓-to-Zipper⇑ : (R : Reg) → (t : μ R) → Zipper⇓ R t → Zipper⇑ R t
  Zipper⇓-to-Zipper⇑ R t ((l , s) , p) = (l , (reverse s)) , {!plug-μ⇓-to-plug-μ⇑ !}

  Zipper⇑-to-Zipper⇓ : (R : Reg) → (t : μ R) → Zipper⇑ R t → Zipper⇓ R t
  Zipper⇑-to-Zipper⇓  = {!!}

  data lt (R : Reg) : (t : μ R) → Zipper⇓ R t → Zipper⇓ R t → Set where
    lt-step  : ∀ {t} {t′} {t₁ t₂} {h} {s₁ s₂} eq₁ eq₂ q₁ q₂
             →  lt R t′ ((t₁ , s₁) , eq₁) ((t₂ ,  s₂) ,  eq₂)
             →  lt R (In t) ((t₁ , h ∷ s₁) , Plug-∷ eq₁ q₁) ((t₂ , h  ∷ s₂) , Plug-∷ eq₂ q₂)
             
    lt-base  : ∀ {t} {h₁ h₂} {s₁ s₂} {t₁ t₂} eq₁ eq₂ q₁ q₂
             → ∇-[[ μ R , R , t ]] (h₁ ,, plug-μ⇓ R (In t₁) s₁ ,,  q₁) < (h₂ ,, plug-μ⇓ R (In t₂) s₂ ,, q₂)
             → lt R (In t) ((t₁ , h₁ ∷ s₁) , Plug-∷ eq₁ q₁) ((t₂ , h₂ ∷ s₂) , Plug-∷ eq₂ q₂)

  porp : (X : Set) → (R : Reg) → (dr : ∇ R X X) (x : X) (r : ⟦ R ⟧ X) → (a : Plug R dr x r) → (b : Plug R dr x r) → a ≡ b
  porp X .I .tt e .e Plug-I Plug-I = refl
  porp X .(R ⨁ Q) .(inj₁ r) e .(inj₁ r′) (Plug-⨁-inj₁ {R} {Q} {r = r} {r′} a) (Plug-⨁-inj₁ b) = cong Plug-⨁-inj₁ (porp X R r e r′ a b)
  porp X .(R ⨁ Q) .(inj₂ q) e .(inj₂ q′) (Plug-⨁-inj₂ {R} {Q} {q = q} {q′} a) (Plug-⨁-inj₂ b) = cong Plug-⨁-inj₂ (porp X Q q e q′ a b)
  porp X (R ⨂ Q) .(inj₁ (dr , q)) x (dr′ , q) (Plug-⨂-inj₁ {dr = dr} a) (Plug-⨂-inj₁ b) = cong Plug-⨂-inj₁ (porp X R dr x dr′ a b)
  porp X (R ⨂ Q) .(inj₂ (r , dq)) x (r , dq′) (Plug-⨂-inj₂ {dq = dq} a) (Plug-⨂-inj₂ b) = cong Plug-⨂-inj₂ (porp X Q dq x dq′ a b)

  acc-base : (R : Reg) → (r : ⟦ R ⟧ (μ R)) → ∀ dr e t s eq eqq → (∀ t dr → Plug R dr t r → Well-founded (lt R t))
               → Acc (lt R e) ((t , s) , eq)
               → Acc (∇-[[ μ R , R , r ]]_<_) (dr ,, e ,, eqq)
               → WfRec (lt R (In r)) (Acc (lt R (In r)))
                                     ((t , dr ∷ s) , Plug-∷ eq eqq)
  acc-base R r dr e t s eq eqq x (acc rs) x₂ .((t₁ , dr ∷ s₁) , Plug-∷ eq₁ q₁) (lt-step {t₁ = t₁} {s₁ = s₁} eq₁ .eq q₁ .eqq p)
    with porp (μ R) R dr e r eqq q₁
  acc-base R r dr e t s eq eqq x (acc rs) x₂ .((t₁ , dr ∷ s₁) , Plug-∷ eq₁ eqq) (lt-step {t₁ = t₁} {s₁ = s₁} eq₁ .eq .eqq .eqq p) | refl
    = acc (acc-base R r dr e t₁ s₁ eq₁ eqq x (rs ((t₁ , s₁) , eq₁) p) x₂ )
  acc-base R r dr .(plug-μ⇓ R (In t) s) t s eq eqq x (acc _) (acc rs) .((t₁ , h₁ ∷ s₁) , Plug-∷ eq₁ q₁) (lt-base {h₁ = h₁} {s₁ = s₁} {t₁ = t₁} eq₁ .eq q₁ .eqq p)
    = acc (acc-base R r h₁ (plug-μ⇓ R (In t₁) s₁) t₁ s₁ eq₁ q₁ x (x (plug-μ⇓ R (In t₁) s₁) h₁ q₁ ((t₁ , s₁) , eq₁)) (rs (h₁ ,, plug-μ⇓ R (In t₁) s₁ ,, q₁) p) ) 

  data AllR (A : Set) (P : A → Set) : (R : Reg) → ⟦ R ⟧ A → Set₁ where
    AllR-I       : (x : A) → P x → AllR A P I x
    AllR-⨂      : (R Q : Reg) → (r : ⟦ R ⟧ A) → (q : ⟦ Q ⟧ A) → AllR A P R r → AllR A P Q q → AllR A P (R ⨂ Q) (r , q)
    AllR-⨁-inj₁ : (R Q : Reg) (r : ⟦ R ⟧ A) → AllR A P R r → AllR A P (R ⨁ Q) (inj₁ r)
    AllR-⨁-inj₂ : (R Q : Reg) (q : ⟦ Q ⟧ A) → AllR A P Q q → AllR A P (R ⨁ Q) (inj₂ q)
    AllR-1′      : AllR A P 1′ tt
    AllR-K       : (B : Set) → (b : B) → AllR A P (K B) b  

  prop : (R Q : Reg) (P : μ R → Set) → ∀ t → AllR (μ R) P Q t → (∀ r dr → Plug Q dr r t → P r)
  prop R .I P t (AllR-I .t x) .t .tt Plug-I = x
  prop R .(R₁ ⨂ Q) P .(r₁ , q) (AllR-⨂ R₁ Q r₁ q x x₂) r (inj₁ (r′ , .q)) (Plug-⨂-inj₁ x₁)   = prop R R₁ P r₁ x r r′ x₁ 
  prop R .(R₁ ⨂ Q) P .(r₁ , q) (AllR-⨂ R₁ Q r₁ q x x₂) r (inj₂ .(r₁ , _)) (Plug-⨂-inj₂ x₁)   = prop R Q P q x₂ r _ x₁
  prop R .(R₁ ⨁ Q) P .(inj₁ r₁) (AllR-⨁-inj₁ R₁ Q r₁ x) r .(inj₁ _) (Plug-⨁-inj₁ x₁)         = prop R R₁ P r₁ x r _ x₁
  prop R .(R₁ ⨁ Q) P .(inj₂ q) (AllR-⨁-inj₂ R₁ Q q x) r .(inj₂ q₁) (Plug-⨁-inj₂ {q = q₁} x₁) = prop R Q P q x r q₁ x₁
  prop R .1′ P .tt AllR-1′ r () x₁
  prop R .(K B) P t (AllR-K B .t) r () x₁
  
  lt-WF : (R : Reg) (t : μ R) → Well-founded (lt R t)
  lt-WF R t x = acc (aux R t x)
    where
       all-is-wf : (R Q : Reg) → (t : ⟦ Q ⟧ (μ R)) → AllR (μ R) (λ t → Well-founded (lt R t)) Q t
       all-is-wf R 0′ ()
       all-is-wf R 1′ tt             = AllR-1′
       all-is-wf R I t               = AllR-I t (lt-WF R t)
       all-is-wf R (K A) t           = AllR-K A t
       all-is-wf R (Q ⨁ P) (inj₁ x) = AllR-⨁-inj₁ Q P x (all-is-wf R Q x)
       all-is-wf R (Q ⨁ P) (inj₂ y) = AllR-⨁-inj₂ Q P y (all-is-wf R P y)
       all-is-wf R (Q ⨂ P) (q , p)  = AllR-⨂ Q P q p (all-is-wf R Q q) (all-is-wf R P p)

       aux : ∀ (R : Reg) → (t : (μ R)) → (x : Zipper⇓ R t) → WfRec (lt R t) (Acc (lt R t)) x
       aux R (In t) .((t₂ , h ∷ s₂) , Plug-∷ eq₂ q₂) .((t₁ , h ∷ s₁) , Plug-∷ eq₁ q₁) (lt-step {t′ = t′} {t₁} {t₂} {h} {s₁} {s₂} eq₁ eq₂ q₁ q₂ p)
         = acc (acc-base R t h t′ t₁ s₁ eq₁ q₁ (prop R R (λ t → Well-founded (lt R t)) t (all-is-wf R R t))
                                               (prop R R (λ t → Well-founded (lt R t)) t (all-is-wf R R t) t′ h q₂ ((t₁ , s₁) , eq₁))
                                               (∇-WF (μ R) R t (h ,, t′ ,, q₁)))

       aux R (In t) .((t₂ , h₂ ∷ s₂) , Plug-∷ eq₂ q₂) .((t₁ , h₁ ∷ s₁) , Plug-∷ eq₁ q₁) (lt-base {h₁ = h₁} {h₂} {s₁} {s₂} {t₁} {t₂} eq₁ eq₂ q₁ q₂ x₁)
         = acc (acc-base R t h₁ (plug-μ⇓ R (In t₁) s₁) t₁ s₁ eq₁ q₁
                                (prop R R (λ t → Well-founded (lt R t)) t (all-is-wf R R t))
                                (prop R R (λ t → Well-founded (lt R t)) t (all-is-wf R R t) (plug-μ⇓ R (In t₁) s₁) h₁ q₁ ((t₁ , s₁) , eq₁))
                                (∇-WF (μ R) R t (h₁ ,, plug-μ⇓ R (In t₁) s₁ ,, q₁)))
    

  Leaf : Reg → Set → Set
  Leaf R X = Σ (⟦ R ⟧ X) λ l → NonRec R l


  UZipper' : Reg → Set → Set
  UZipper' R X = Leaf R X × List (∇ R (μ R) (μ R))


  PlugZ'-μ⇑ : {X : Set} → (R : Reg) → UZipper' R X → μ R →  Set
  PlugZ'-μ⇑ R ((x , nr) , s) t = Plug-μ⇑ R (In (coerce x nr)) s t

  data First {X : Set} : (R : Reg) → ⟦ R ⟧ X → ∇ R X X × X → Set where
    First-⨁-inj₁ : ∀ {R Q} {r} {rx x} → First R r (rx , x) → First (R ⨁ Q) (inj₁ r) (inj₁ rx , x)
    First-⨁-inj₂ : ∀ {R Q} {q} {qx x} → First Q q (qx , x) → First (R ⨁ Q) (inj₂ q) (inj₂ qx , x)
    First-I       : ∀ {x} → First I x (tt , x)
    First-⨂₁     : ∀ {R Q} {rx x} {r q} → First R r (rx , x) → First (R ⨂ Q) (r , q) (inj₁ (rx , q) , x)
    First-⨂₂     : ∀ {R Q} {qx x} {r q} → NonRec {X} R r     → First Q q (qx , x) → First (R ⨂ Q) (r , q) (inj₂ (r , qx) , x)

  First-NonRec : ∀ {X : Set} R r rx (x : X) → First R r (rx , x) → NonRec R r → ⊥
  First-NonRec .1′ .tt rx x () NonRec-1′
  First-NonRec .(K B) r rx x () (NonRec-K B .r)
  First-NonRec .(R ⨁ Q) .(inj₁ r) .(inj₁ _) x (First-⨁-inj₁ x₁) (NonRec-⨁-inj₁ R Q r x₂)     = First-NonRec R r _ x x₁ x₂
  First-NonRec .(R ⨁ Q) .(inj₂ q) .(inj₂ _) x (First-⨁-inj₂ x₁) (NonRec-⨁-inj₂ R Q q x₂)     = First-NonRec Q q _ x x₁ x₂
  First-NonRec .(R ⨂ Q) .(r , q) .(inj₁ (_ , q)) x (First-⨂₁ x₁) (NonRec-⨂ R Q r q x₂ x₃)    = First-NonRec R r _ x x₁ x₂
  First-NonRec .(R ⨂ Q) .(r , q) .(inj₂ (r , _)) x (First-⨂₂ x₁ x₄) (NonRec-⨂ R Q r q x₂ x₃) = First-NonRec Q q _ x x₄ x₃
 
  First-Unique : ∀ {X : Set} {R : Reg} {r : ⟦ R ⟧ X} {x y} → First R r x → First R r y → x ≡ y
  First-Unique (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) with First-Unique f₁ f₂
  First-Unique (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) | refl = refl
  First-Unique (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) with First-Unique f₁ f₂
  First-Unique (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) | refl = refl
  First-Unique First-I First-I = refl
  First-Unique (First-⨂₁ f₁) (First-⨂₁ f₂) with First-Unique f₁ f₂
  First-Unique (First-⨂₁ f₁) (First-⨂₁ f₂) | refl = refl
  First-Unique (First-⨂₁ f₁) (First-⨂₂ x f₂) = ⊥-elim (First-NonRec _ _ _ _ f₁ x)
  First-Unique (First-⨂₂ x f₁) (First-⨂₁ f₂) = ⊥-elim (First-NonRec _ _ _ _ f₂ x)
  First-Unique (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) with First-Unique f₁ f₂
  First-Unique (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) | refl = refl
   
  view : {X : Set} → (R : Reg) → (Q : Reg) → (r : ⟦ R ⟧ (μ Q)) → (Σ (∇ R (μ Q) (μ Q)) λ dr
                                                               →  Σ (μ Q) λ q → First R r (dr , q))
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
  view {X} (R ⨂ Q) P (r , q) | inj₂ (l  , is-l , eq) with view {X} Q P q
  view {X} (R ⨂ Q) P (r , q) | inj₂ (l , is-l , eq) | inj₁ (dr , mq , f)      = inj₁ ((inj₂ (r , dr)) , (mq , First-⨂₂ (≈-NonRec l is-l r (≈-sym eq)) f))
  view {X} (R ⨂ Q) P (r , q) | inj₂ (l , is-l , eq) | inj₂ (l′ , is-l′ , eq′) = inj₂ ((l , l′) , NonRec-⨂ R Q l l′ is-l is-l′ , ≈-⨂ eq eq′)

  First-to-Plug : ∀ {X : Set} {R : Reg} {r : ⟦ R ⟧ X} {dr : ∇ R X X} {x : X} → First R r (dr , x) → Plug R dr x r
  First-to-Plug (First-⨁-inj₁ x₁) = Plug-⨁-inj₁ (First-to-Plug x₁)
  First-to-Plug (First-⨁-inj₂ x₁) = Plug-⨁-inj₂ (First-to-Plug x₁)
  First-to-Plug First-I            = Plug-I
  First-to-Plug (First-⨂₁ x₁)     = Plug-⨂-inj₁ (First-to-Plug x₁)
  First-to-Plug (First-⨂₂ x₁ x₂)  = Plug-⨂-inj₂ (First-to-Plug x₂)
  
  mutual

    first-⨁₁ : {X : Set} (R Q P : Reg) → (Leaf (R ⨁ Q) X → List (∇ P (μ P) (μ P)) → UZipper' P X)
                              → (Leaf R X → List (∇ P (μ P) (μ P)) → UZipper' P X)
    first-⨁₁ R Q P f (l , x) s = f ((inj₁ l , NonRec-⨁-inj₁ R Q l x)) s


    first-⨁₂ : {X : Set} (R Q P : Reg) → (Leaf (R ⨁ Q) X → List (∇ P (μ P) (μ P)) → UZipper' P X)
                              → (Leaf Q X → List (∇ P (μ P) (μ P)) → UZipper' P X)
    first-⨁₂ R Q P f (l , x) s = f (inj₂ l , NonRec-⨁-inj₂ R Q l x) s

    first-⨂-2 : {X : Set} (R Q P : Reg) → (Leaf (R ⨂ Q) X → List (∇ P (μ P) (μ P)) → UZipper' P X)
                               → (Leaf R X → Leaf Q X → List (∇ P (μ P) (μ P)) → UZipper' P X)
    first-⨂-2 R Q P f (r , isl-r) (q , isl-q) s = f ((r , q) , NonRec-⨂ R Q r q isl-r isl-q) s

    first-⨂-1 : {X : Set} (R Q P : Reg) → (∇ R (μ P) (μ P) × ⟦ Q ⟧ (μ P) ⊎ ⟦ R ⟧ (μ P) × ∇ Q (μ P) (μ P) → ∇ P (μ P) (μ P)) →
                 (Leaf (R ⨂ Q) X → List (∇ P (μ P) (μ P)) → UZipper' P X)
                 → ⟦ Q ⟧ (μ P) → ⟦ R ⟧ (μ P) → (Leaf R X → List (∇ P (μ P) (μ P)) → UZipper' P X)
    first-⨂-1 R Q P k f q r r′ = first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f r′)

    first : {X : Set} → (R Q : Reg) → ⟦ R ⟧ (μ Q) → (∇ R (μ Q) (μ Q) → (∇ Q (μ Q) (μ Q)))
                                      → (Leaf R X → List (∇ Q (μ Q) (μ Q)) → UZipper' Q X)
                                      → List (∇ Q (μ Q) (μ Q))
                                      → UZipper' Q X
    first 0′ Q () _
    first 1′ Q x k f s              = f (tt , NonRec-1′) s
    first I  Q x  k f s             = to-left Q x (k tt ∷ s)
    first (K A) Q x k f s           = f (x , NonRec-K A x) s
    first (R ⨁ Q) P (inj₁ x) k f s = first R P x  (k ∘ inj₁) (first-⨁₁ R Q P f) s
    first (R ⨁ Q) P (inj₂ y) k f s = first Q P y  (k ∘ inj₂) (first-⨁₂ R Q P f) s
    first (R ⨂ Q) P (r , q) k f s  = first R P r  (k ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q r) s

    to-left : {X : Set} (R : Reg) → μ R → List (∇ R (μ R) (μ R)) → UZipper' R X
    to-left R (In t) s = first R R t id _,_ s

  Prop : {X : Set} (R : Reg) → (Q : Reg) → ⟦ R ⟧ (μ Q) →  (∇ R (μ Q) (μ Q) → ∇ Q (μ Q) (μ Q))
       → List (∇ Q (μ Q) (μ Q)) → (Leaf R X → List (∇ Q (μ Q) (μ Q)) → UZipper' Q X) → (μ Q) → Set
  Prop {X} R Q r k s f t with view {X} R Q r
  Prop {X} R Q r k s f t | inj₁ (dr , q , _)  = Σ (⟦ Q ⟧ (μ Q)) λ e → Plug Q (k dr) q e × Plug-μ⇑ Q (In e) s t
  Prop {X} R Q r k s f t | inj₂ (l , isl , _) = PlugZ'-μ⇑ Q (f (l , isl) s) t

  propR : ∀ {X : Set} R r s t → Plug-μ⇑ R (In r) s t → Prop {X} R R r id s _,_ t
  propR {X} R r s t p with view {X} R R r
  propR {X} R r s t p | inj₁ (dr , mr , pl)    = r , (First-to-Plug pl , p)
  propR {X} .1′ .tt s t p | inj₂ (.tt , NonRec-1′ , ≈-1′) = p
  propR {X} .(K B) .l s t p | inj₂ (l , NonRec-K B .l , ≈-K) = p
  propR {X} .(R ⨁ Q) .(inj₁ x) s t p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ R Q r isl , ≈-⨁₁ {x = x} eq)
    rewrite coerce-≈ r isl x (≈-sym eq) = p
  propR {X} .(R ⨁ Q) .(inj₂ x) s t p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ R Q q isl , ≈-⨁₂ {x = x} eq)
    rewrite coerce-≈ q isl x (≈-sym eq) = p
  propR {X} .(R ⨂ Q) (r , q) s t p | inj₂ (.(r′ , q′) , NonRec-⨂ R Q r′ q′ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
    rewrite coerce-≈ r′ isl₁ r (≈-sym eq₁) | coerce-≈ q′ isl₂ q (≈-sym eq₂) = p

  Plug-NonRec : ∀ {X : Set} {R : Reg} → (x : X) → (dₓ : ∇ R X X) → (tₓ : ⟦ R ⟧ X) → NonRec R tₓ → Plug R dₓ x tₓ → ⊥
  Plug-NonRec x .tt .x () Plug-I
  Plug-NonRec x .(inj₁ _) .(inj₁ r) (NonRec-⨁-inj₁ R Q r p) (Plug-⨁-inj₁ nr)      = Plug-NonRec x _ r p nr
  Plug-NonRec x .(inj₂ _) .(inj₂ q) (NonRec-⨁-inj₂ R Q q p) (Plug-⨁-inj₂ nr)      = Plug-NonRec x _ q p nr
  Plug-NonRec x .(inj₁ (_ , q)) .(r , q) (NonRec-⨂ R Q r q p p₁) (Plug-⨂-inj₁ nr) = Plug-NonRec x _ r p nr
  Plug-NonRec x .(inj₂ (r , _)) .(r , q) (NonRec-⨂ R Q r q p p₁) (Plug-⨂-inj₂ nr) = Plug-NonRec x _ q p₁ nr
    

  mutual
    first-lemma : {X : Set} (R Q : Reg) → (r : ⟦ R ⟧ (μ Q)) 
                → (k : ∇ R (μ Q) (μ Q) → ∇ Q (μ Q) (μ Q))
                → (f : Leaf R X → List (∇ Q (μ Q) (μ Q)) → UZipper' Q X)
                → (s : List (∇ Q (μ Q) (μ Q)))
                → (t : μ Q)
                → (z : UZipper' Q X)
                → first R Q r k f s ≡ z → Prop R Q r k s f t → PlugZ'-μ⇑ Q z t
    first-lemma {X} R Q r k f s  t z x p with view {X} R Q r
    first-lemma {X} 0′ Q () k f s t z x (e , plug-e , plugm-e)
      | inj₁ (dr , mq , fst)
    first-lemma {X} 1′ Q r k f s t z x (e , plug-e , plugm-e)
      | inj₁ (() , mq , fst)
    first-lemma {X} I Q r k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.tt , .r , First-I)
      = to-left-preserves Q r (k tt ∷ s) t (Plug-∷ plug-e plugm-e) z x
    first-lemma {X} (K A) Q r k f s t z x (e , plug-e , plugm-e)
      | inj₁ (() , mq , fst)
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst)
      with view {X} R P r | first-lemma R P r (k ∘ inj₁) (first-⨁₁ R Q P f) s t z x
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont
      with First-Unique fst fst′
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ dr′) , .mq′ , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
      = cont (e , (plug-e , plugm-e))
    first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ dr) , mq , First-⨁-inj₁ {r = r} {dr} fst) | inj₂ (l , isl , eq) | _
      = ⊥-elim (First-NonRec R r dr mq fst (≈-NonRec l isl r (≈-sym eq)))
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst)
      with view {X} Q P q | first-lemma Q P q (k ∘ inj₂) (first-⨁₂ R Q P f) s t z x
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ qx) , mq , First-⨁-inj₂ {q = q} {qx} fst) | inj₁ (dr , mq′ , fst′) | cont
      with First-Unique fst fst′
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dr) , .mq′ , First-⨁-inj₂ {q = q} {.dr} fst) | inj₁ (dr , mq′ , fst′) | cont | refl = cont (e , plug-e , plugm-e)
    first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst) | inj₂ (l , isl , eq) | _
      =  ⊥-elim (First-NonRec Q q dq mq fst (≈-NonRec l isl q (≈-sym eq)))
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e) | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst)
      with view {X} R P r | first-lemma R P r (λ z₁ → k (inj₁ (z₁ , q))) (first-⨂-1 R Q P k f q r) s t z x
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst) | inj₁ (dr′ , mq′ , fst′) | cont
      with First-Unique fst fst′
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (dr′ , q)) , .mq′ , First-⨂₁ {rx = .dr′} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
      = cont (e , plug-e , plugm-e)
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₁ (dr , q)) , mq , First-⨂₁ {rx = dr} fst) | inj₂ (l , isl , eq) | cont
      = ⊥-elim ((First-NonRec R r dr mq fst (≈-NonRec l isl r (≈-sym eq))))
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (_ , qx)) , mq , First-⨂₂ {qx = qx} nr fst)
      with view {X} R P r  | first-lemma R P r (λ z₁ → k (inj₁ (z₁ , q))) (first-⨂-1 R Q P k f q r) s t z x
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₁ (dr′ , mq′ , fst′) | cont
      = ⊥-elim (First-NonRec R r dr′ mq′ fst′ nr)
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont
      with first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (r′ , nr-r)) s | inspect (first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (r′ , nr-r))) s 
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁
      with view {X} Q P q | first-lemma Q P q (λ z₁ → k (inj₂ (r , z₁))) ((first-⨂-2 R Q P f (r′ , nr-r))) s t z′ eq₁
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁ | inj₁ (dr′′ , mq′′ , fst′′) | cont′
      with First-Unique fst fst′′
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (r , dr′′)) , .mq′′ , First-⨂₂ {qx = .dr′′} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁ | inj₁ (dr′′ , mq′′ , fst′′) | cont′ | refl
      = cont (cont′ (e , plug-e , plugm-e))
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
      | inj₁ (.(inj₂ (r , dq)) , mq , First-⨂₂ {qx = dq} isl fst) | inj₂ (l′ , isl′ , eq) | g | z′ | Is eq₁ | inj₂ (l′′ , isl′′ , eq′′) | cont′
      = ⊥-elim (First-NonRec Q q dq mq fst (≈-NonRec l′′ isl′′ q (≈-sym eq′′)))
    
    first-lemma {X} 0′ Q () k f s t z x p
      | inj₂ (l , isl , plug)
    first-lemma {X} 1′ Q .tt k f s t .(f (tt , NonRec-1′) s) refl p
      | inj₂ (.tt , NonRec-1′ , ≈-1′)    = p
    first-lemma {X} I Q r k f s t z x p
      | inj₂ (l , () , plug)
    first-lemma {X} (K A) Q r k f s t .(f (r , NonRec-K A r) s) refl p
      | inj₂ (.r , NonRec-K .A .r , ≈-K) = p
    first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
      with view {X} R P x | first-lemma R P x (k ∘ inj₁) (first-⨁₁ R Q P f) s t z e
    first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
      | inj₁ (dr , mq , fst) | _ = ⊥-elim (First-NonRec R x dr mq fst (≈-NonRec r isl x (≈-sym eq)))
    first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ .R .Q r isl , ≈-⨁₁ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont
      with ≈-to-≡ (≈-trans (≈-sym eq-l) eq)
    first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ l) , NonRec-⨁-inj₁ .R .Q .l isl , ≈-⨁₁ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl
      with NonRec-proof-irrelevance isl isl′
    first-lemma {X} (R ⨁ Q) P .(inj₁ x) k f s t z e p | inj₂ (.(inj₁ l) , NonRec-⨁-inj₁ .R .Q .l .isl′ , ≈-⨁₁ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl | refl = cont p
    first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
      with view {X} Q P x | first-lemma Q P x (k ∘ inj₂) (first-⨁₂ R Q P f) s t z e
    first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
      | inj₁ (dr , mq , fst) | cont = ⊥-elim (First-NonRec Q x dr mq fst (≈-NonRec q isl x (≈-sym eq)))
    first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ .R .Q q isl , ≈-⨁₂ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont
      with ≈-to-≡ (≈-trans (≈-sym eq-l) eq)
    first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ l) , NonRec-⨁-inj₂ .R .Q .l isl , ≈-⨁₂ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl
      with NonRec-proof-irrelevance isl isl′
    first-lemma {X} (R ⨁ Q) P .(inj₂ x) k f s t z e p | inj₂ (.(inj₂ l) , NonRec-⨁-inj₂ .R .Q .l .isl′ , ≈-⨁₂ {x = x} eq)
      | inj₂ (l , isl′ , eq-l) | cont | refl | refl = cont p
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      with view {X} R P r | first-lemma R P r (k  ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q r) s t z e
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₁ (dr , mq , plug) | _
      = ⊥-elim (First-NonRec R r dr mq plug (≈-NonRec r′ isl₁ r (≈-sym eq₁)))
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((r′ , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont
      with ≈-to-≡ (≈-trans (≈-sym eq) eq₁)
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl
      with NonRec-proof-irrelevance isl₁ isl
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl
      with first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (l , isl)) s | inspect (first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (l , isl))) s
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq
      with view {X} Q P q | first-lemma Q P q (k ∘ inj₂ ∘ (_,_ r)) ((first-⨂-2 R Q P f (l , isl))) s t z′ f-eq
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₁ (dr , mq , fst) | cont′
      = ⊥-elim (First-NonRec Q q dr mq fst (≈-NonRec q′ isl₂ q (≈-sym eq₂)))
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , q′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′
      with ≈-to-≡ (≈-trans (≈-sym eq′) eq₂)
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , .l′) , NonRec-⨂ .R .Q _ _ .isl isl₂ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′ | refl
      with NonRec-proof-irrelevance isl′ isl₂
    first-lemma {X} (R ⨂ Q) P (r , q) k f s t z e p | inj₂ ((.l , .l′) , NonRec-⨂ .R .Q _ _ .isl .isl′ , ≈-⨂ eq₁ eq₂)
      | inj₂ (l , isl , eq) | cont | refl | refl | z′ | Is f-eq | inj₂ (l′ , isl′ , eq′) | cont′ | refl | refl
      = cont (cont′ p)

    to-left-preserves : {X : Set} (R : Reg) → (r : μ R) → (s : List (∇ R (μ R) (μ R))) → (t : μ R)
                      → Plug-μ⇑ R r s t → (z : UZipper' R X) → to-left R r s ≡ z → PlugZ'-μ⇑ R z t
    to-left-preserves R (In r) s t x z p = first-lemma R R r id _,_ s  t z p (propR R r s t x)


  -- mutual
  --   unload : {X : Set} (R Q : Reg) → μ R → List (∇ R (μ R) (μ R)) → UZipper' R X ⊎ ⊤
  --   unload R Q x [] = inj₂ tt
  --   unload R Q x (dr ∷ s) = {!!}

  --   first' : {X : Set} → (R Q : Reg) → ⟦ R ⟧ (μ Q) → (∇ R (μ Q) (μ Q) → (∇ Q (μ Q) (μ Q)))
  --                                     → (Leaf R X → List (∇ Q (μ Q) (μ Q)) → UZipper' Q X)
  --                                     → List (∇ Q (μ Q) (μ Q))
  --                                     → UZipper' Q X
  --   first' 0′ Q () _
  --   first' 1′ Q x k f s              = f (tt , NonRec-1′) s
  --   first' I  Q x  k f s             = {!!}
  --   first' (K A) Q x k f s           = f (x , NonRec-K A x) s
  --   first' (R ⨁ Q) P (inj₁ x) k f s = first' R P x  (k ∘ inj₁) (first-⨁₁ R Q P f) s
  --   first' (R ⨁ Q) P (inj₂ y) k f s = first' Q P y  (k ∘ inj₂) (first-⨁₂ R Q P f) s
  --   first' (R ⨂ Q) P (r , q) k f s  = first' R P r  (k ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q r) s


  --   right : {X : Set} (R Q : Reg) → (∇ R (μ Q) (μ Q) → μ Q) → ∇ R (μ Q) (μ Q) →  UZipper' Q X ⊎ ⊤
  --   right 0′ Q t ()
  --   right 1′ Q t ()
  --   right I Q t x  = {!!}
  --   right (K A) Q t ()
  --   right (R ⨁ Q) P t (inj₁ x) = {!!}
  --   right (R ⨁ Q) P t (inj₂ y) = {!!}
  --   right (R ⨂ Q) P t (inj₁ (dr , q)) = right R P {!i!} dr
  --   right (R ⨂ Q) P t (inj₂ y) = {!!}
