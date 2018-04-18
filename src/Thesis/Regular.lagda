\begin{code}
module Thesis.Regular where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
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
  open import Thesis.Regular.Equality
  open import Thesis.Regular.Dissection
  open import Thesis.Regular.NonRec
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
    

  module _ (A : Set) where

    Leaf : Reg → Set
    Leaf R = Σ (⟦ R ⟧ A) λ l → NonRec R l
      
    UZipper' : Reg → Set
    UZipper' R = Leaf R × List (∇ R (μ R) (μ R))

    PlugZ'-μ⇑ : (R : Reg) → UZipper' R → μ R →  Set
    PlugZ'-μ⇑ R ((x , nr) , s) t = Plug-μ⇑ R (In (coerce x nr)) s t

    view : (R : Reg) → (Q : Reg) → (r : ⟦ R ⟧ (μ Q)) → (Σ (∇ R (μ Q) (μ Q)) λ dr → Σ (μ Q) λ q → Plug R dr q r)
                                                     ⊎ (Σ (⟦ R ⟧ A) λ l → (NonRec R l × [ R ]-[ μ Q ] r ≈[ A ] l))
    view 0′ Q ()
    view 1′ Q r    = inj₂ (r , (NonRec-1′ , ≈-1′))
    view I Q r     = inj₁ (tt , r , Plug-I)
    view (K A) Q r = inj₂ (r , NonRec-K A r , ≈-K)
    view (R ⨁ Q) P (inj₁ x) with view R P x
    view (R ⨁ Q) P (inj₁ x) | inj₁ (dr , p , plug) = inj₁ (inj₁ dr , p , Plug-⨁-inj₁ plug)
    view (R ⨁ Q) P (inj₁ x) | inj₂ (l , isl , eq)  = inj₂ (inj₁ l , NonRec-⨁-inj₁ R Q l isl , ≈-⨁₁ eq)
    view (R ⨁ Q) P (inj₂ y) with view Q P y
    view (R ⨁ Q) P (inj₂ y) | inj₁ (dq , p , plug) = inj₁ (inj₂ dq , p , Plug-⨁-inj₂ plug)
    view (R ⨁ Q) P (inj₂ y) | inj₂ (l , isl , eq)  = inj₂ (inj₂ l , NonRec-⨁-inj₂ R Q l isl , ≈-⨁₂ eq)
    view (R ⨂ Q) P (r , q) with view R P r
    view (R ⨂ Q) P (r , q) | inj₁ (dr , p , plug) = inj₁ (inj₁ (dr , q) , p , Plug-⨂-inj₁ plug)
    view (R ⨂ Q) P (r , q) | inj₂ (l , isl , eq)  with view Q P q
    view (R ⨂ Q) P (r , q) | inj₂ (l , isl , eq) | inj₁ (dq , p , plug)   = inj₁ (inj₂ (r , dq) , p , Plug-⨂-inj₂ plug)
    view (R ⨂ Q) P (r , q) | inj₂ (l , isl , eq) | inj₂ (l′ , isl′ , eq′) = inj₂ ((l , l′) , NonRec-⨂ R Q l l′ isl isl′ , ≈-⨂ eq eq′)

  --   embed-≈ : (R : Reg) → (l : ⟦ R ⟧ A)
  --           → (isl : IsLeaf R l) → ∀ Q → (r : ⟦ R ⟧ (μ Q)) → [ R ]-[ μ Q ] r ≈[ A ] l → embed R Q (leaf l isl) ≡ r   
  --   embed-≈ .1′ .tt IsLeaf-1′ Q .tt ≈-1′ = refl
  --   embed-≈ .(K B) l (IsLeaf-K B .l) Q .l ≈-K = refl
  --   embed-≈ .(R ⨁ Q) .(inj₁ r) (IsLeaf-⨁-inj₁ R Q r isl) P .(inj₁ x) (≈-⨁₁ {.R} {.Q} {x = x} {.r} p) = cong inj₁ (embed-≈ R r isl P x p)
  --   embed-≈ .(R ⨁ Q) .(inj₂ q) (IsLeaf-⨁-inj₂ R Q q isl) P .(inj₂ x) (≈-⨁₂ {Q = .Q} {x = x} p)       = cong inj₂ (embed-≈ Q q isl P x p)
  --   embed-≈ .(R ⨂ Q) .(r , q) (IsLeaf-⨂ R Q r q islr islq) P (r′ , q′) (≈-⨂ {x₁ = x₁} eq-r eq-q)     = cong₂ _,_ (embed-≈ R r islr P r′ eq-r)
  --                                                                                                                  (embed-≈ Q q islq P q′ eq-q)
    mutual

      first-⨁₁ : (R Q P : Reg) → (Leaf (R ⨁ Q) → List (∇ P (μ P) (μ P)) → UZipper' P)
                                → (Leaf R → List (∇ P (μ P) (μ P)) → UZipper' P)
      first-⨁₁ R Q P f (l , x) s = f ((inj₁ l , NonRec-⨁-inj₁ R Q l x)) s


      first-⨁₂ : (R Q P : Reg) → (Leaf (R ⨁ Q) → List (∇ P (μ P) (μ P)) → UZipper' P)
                                → (Leaf Q → List (∇ P (μ P) (μ P)) → UZipper' P)
      first-⨁₂ R Q P f (l , x) s = f (inj₂ l , NonRec-⨁-inj₂ R Q l x) s

      first-⨂-2 : (R Q P : Reg) → (Leaf (R ⨂ Q) → List (∇ P (μ P) (μ P)) → UZipper' P)
                                 → (Leaf R → Leaf Q → List (∇ P (μ P) (μ P)) → UZipper' P)
      first-⨂-2 R Q P f (r , isl-r) (q , isl-q) s = f ((r , q) , NonRec-⨂ R Q r q isl-r isl-q) s

      first-⨂-1 : (R Q P : Reg) → (∇ R (μ P) (μ P) × ⟦ Q ⟧ (μ P) ⊎ ⟦ R ⟧ (μ P) × ∇ Q (μ P) (μ P) → ∇ P (μ P) (μ P)) →
                   (Leaf (R ⨂ Q) → List (∇ P (μ P) (μ P)) → UZipper' P)
                   → ⟦ Q ⟧ (μ P) → ⟦ R ⟧ (μ P) → (Leaf R → List (∇ P (μ P) (μ P)) → UZipper' P)
      first-⨂-1 R Q P k f q r r′ = first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f r′)

      first : (R Q : Reg) → ⟦ R ⟧ (μ Q) → (∇ R (μ Q) (μ Q) → (∇ Q (μ Q) (μ Q)))
                                        → (Leaf R → List (∇ Q (μ Q) (μ Q)) → UZipper' Q)
                                        → List (∇ Q (μ Q) (μ Q))
                                        → UZipper' Q
      first 0′ Q () _
      first 1′ Q x k f s              = f (tt , NonRec-1′) s
      first I  Q x  k f s             = to-left Q x (k tt ∷ s)
      first (K A) Q x k f s           = f (x , NonRec-K A x) s
      first (R ⨁ Q) P (inj₁ x) k f s = first R P x  (k ∘ inj₁) (first-⨁₁ R Q P f) s
      first (R ⨁ Q) P (inj₂ y) k f s = first Q P y  (k ∘ inj₂) (first-⨁₂ R Q P f) s
      first (R ⨂ Q) P (r , q) k f s  = first R P r  (k ∘ inj₁ ∘ (_, q)) (first-⨂-1 R Q P k f q r) s
                                                   
      to-left : (R : Reg) → μ R → List (∇ R (μ R) (μ R)) → UZipper' R
      to-left R (In t) s = first R R t id _,_ s

  
  --   Prop : (R : Reg) → (Q : Reg) → ⟦ R ⟧ (μ Q) →  (∇ R (μ Q) (μ Q) → ∇ Q (μ Q) (μ Q)) → List (∇ Q (μ Q) (μ Q)) → (Leaf R → List (∇ Q (μ Q) (μ Q)) → UZipper' Q) → (μ Q) → Set
  --   Prop R Q r k s f t with view R Q r
  --   Prop R Q r k s f t | inj₁ (dr , q , _)  = Σ (⟦ Q ⟧ (μ Q)) λ e → Plug Q (k dr) q e × Plug-μ⇑ Q (In e) s t
  --   Prop R Q r k s f t | inj₂ (l  , pr , _) = PlugZ'-μ⇑ Q (f (leaf l pr) s) t
  
  --   propR : ∀ R r s t → Plug-μ⇑ R (In r) s t → Prop R R r id s _,_ t
  --   propR R r s t p with view R R r
  --   propR R r s t p | inj₁ (dr , mr , pl) = r , (pl , p)
  --   propR .1′ .tt s t p | inj₂ (.tt , isl , ≈-1′) = p
  --   propR .(K B) r s t p | inj₂ (.r , IsLeaf-K B .r , ≈-K) = p
  --   propR .(R ⨁ Q) .(inj₁ x) s t p | inj₂ (.(inj₁ r) , IsLeaf-⨁-inj₁ R Q r isl , ≈-⨁₁ {.R} {.Q} {x = x} {.r} eq)
  --     rewrite embed-≈ R r isl (R ⨁ Q) x eq = p
  --   propR .(R ⨁ Q) .(inj₂ x) s t p | inj₂ (.(inj₂ q) , IsLeaf-⨁-inj₂ R Q q isl , ≈-⨁₂ {.R} {.Q} {x = x} {.q} eq)
  --     rewrite embed-≈ Q q isl (R ⨁ Q) x eq = p
  --   propR .(R ⨂ Q) (r′ , q′) s t p | inj₂ (.(r , q) , IsLeaf-⨂ R Q r q islr islq , ≈-⨂ eq-r eq-q)
  --     rewrite embed-≈ R r islr (R ⨂ Q) r′ eq-r | embed-≈ Q q islq (R ⨂ Q) q′ eq-q = p

  --   mutual
  --     first-lemma : (R Q : Reg) → (r : ⟦ R ⟧ (μ Q)) 
  --                 → (k : ∇ R (μ Q) (μ Q) → ∇ Q (μ Q) (μ Q)) → (f : Leaf R → List (∇ Q (μ Q) (μ Q)) → UZipper' Q) → (s : List (∇ Q (μ Q) (μ Q)))
  --                 → (t : μ Q)
  --                 → (z : UZipper' Q)
  --                 → first R Q r k f s ≡ z → Prop R Q r k s f t → PlugZ'-μ⇑ Q z t
  --     first-lemma 0′ Q () k f s t z x p
  --     first-lemma 1′ Q r k f s t z x p with view 1′ Q r
  --     first-lemma 1′ Q r k f s t z x p | inj₁ (() , _)
  --     first-lemma 1′ Q r k f s t .(f (leaf tt IsLeaf-1′) s) refl p | inj₂ y = p
  --     first-lemma I Q r k f s t z x p with view I Q r
  --     first-lemma I Q r k f s t z x (q′ , pl , pm) | inj₁ (tt , q) = to-left-preserves Q r (k tt ∷ s) t (Plug-∷ pl (pm)) z x
  --     first-lemma I Q r k f s t z x p | inj₂ (_ , () , _)
  --     first-lemma (K A) Q r k f s t z x p     with view (K A) Q r
  --     first-lemma (K A) Q r k f s t z x p | inj₁ (() , _)
  --     first-lemma (K A) Q r k f s t .(f (leaf r (IsLeaf-K A r)) s) refl p | inj₂ (a , isla) = p
  --     first-lemma (R ⨁ Q) P (inj₁ r) k f s t z x p with view R P r
  --     first-lemma (R ⨁ Q) P (inj₁ r) k f s t z x (pm′ , plP , plmP ) | inj₁ (dr , pm , plug) = 
  --       first-lemma R P r (k ∘ inj₁) (first-⨁₁ R Q P f) s t z x {!!}
  --     first-lemma (R ⨁ Q) P (inj₁ r) k f s z t x p | inj₂ (ra , isl , eq) =
  --       first-lemma R P r (k ∘ inj₁) (first-⨁₁ R Q P f) s z t x {!!}
  --     first-lemma (R ⨁ Q) P (inj₂ q) k f s t z x p = {!!}
  --     first-lemma (R ⨂ Q) P (r , q) k f s t z x p with view R P r
  --     first-lemma (R ⨂ Q) P (r , q) k f s t z x (a , b , c) | inj₁ (proj₃ , proj₄ , proj₅) = {!!}
  --     first-lemma (R ⨂ Q) P (r , q) k f s t z x p | inj₂ y = {!!}
      
  --     to-left-preserves : (R : Reg) → (r : μ R) → (s : List (∇ R (μ R) (μ R))) → (t : μ R)
  --                       → Plug-μ⇑ R r s t → (z : UZipper' R) → to-left R r s ≡ z → PlugZ'-μ⇑ R z t
  --     to-left-preserves R (In r) s t x z p = first-lemma R R r id _,_ s t z p (propR R r s t x)
   

  -- --   --   first-preserves-V : ∀ Q x k f z t s →  first V Q x k f s ≡ z → Plug-μ⇑ Q x (k tt ∷ s) t → PlugZ'-μ⇑ Q z t
  -- --   --   first-preserves-V Q x k f z t s x₁ x₂ = to-left-preserves Q x (k tt ∷ s) t x₂ z x₁

  -- --   -- --   first-preserves-⨁₁ : ∀ R Q r k f s z t → first R (R ⨁ Q) r k f ≡ z → Plug-μ⇑ (R ⨁ Q) (In (inj₁ r)) s t → PlugZ'-μ⇑ (R ⨁ Q) z t
  -- --   -- --   first-preserves-⨁₁ 0′ Q r k f s z t x x₁ = {!!}
  -- --   -- --   first-preserves-⨁₁ 1′ Q r k f s z t x x₁ = {!!}
  -- --   -- --   first-preserves-⨁₁ V Q (In (inj₁ v)) k f s z t x x₁ = first-preserves-V (V ⨁ Q) v {!!} {!!} z t x (Plug-∷ {!!} {!!})
  -- --   -- --   first-preserves-⨁₁ V Q (In (inj₂ y)) k f s z t x x₁ = {!!}
  -- --   -- --   first-preserves-⨁₁ (K A) Q r k f s z t x x₁ = {!!}
  -- --   -- --   first-preserves-⨁₁ (R ⨁ R₁) Q r k f s z t x x₁ = {!!}
  -- --   -- --   first-preserves-⨁₁ (R ⨂ R₁) Q r k f s z t x x₁ = {!!}

  -- --   --   first-preserves-⨂₁ : ∀ (R Q : Reg) (r : ⟦ R ⟧ (μ (R ⨁ Q)))
  -- --   --                           (k : ∇ R (μ (R ⨁ Q)) (μ (R ⨁ Q)) ⊎ ∇ Q (μ (R ⨁ Q)) (μ (R ⨁ Q)) → ∇ R (μ (R ⨁ Q)) (μ (R ⨁ Q)) ⊎ ∇ Q (μ (R ⨁ Q)) (μ (R ⨁ Q)))
  -- --   --                           (f : Leaf (R ⨁ Q) → (List (∇ R (μ (R ⨁ Q)) (μ (R ⨁ Q)) ⊎ ∇ Q (μ (R ⨁ Q)) (μ (R ⨁ Q)))) → UZipper' (R ⨁ Q))
  -- --   --                           s z t → first R (R ⨁ Q) r (k ∘ inj₁) (λ { (leaf l x) → f (leaf (inj₁ l) (IsLeaf-⨁-inj₁ R Q l x)) }) s ≡ z →
  -- --   --                          Plug-μ⇑ (R ⨁ Q) (In (inj₁ r)) s t → PlugZ'-μ⇑ (R ⨁ Q) z t
  -- --   --   first-preserves-⨂₁ 0′ Q r k f s z t x x₁ = {!!}
  -- --   --   first-preserves-⨂₁ 1′ Q r k f s z t x x₁ = {!!}
  -- --   --   first-preserves-⨂₁ V Q r k f s z t x x₁ = {!!}
  -- --   --   first-preserves-⨂₁ (K A) Q r k f s z t x x₁ = {!!}
  -- --   --   first-preserves-⨂₁ (R ⨁ P) Q (inj₁ r) k f s z t x x₁ = {!!}
  -- --   --   first-preserves-⨂₁ (R ⨁ P) Q (inj₂ y) k f s z t x x₁ = {!!}
  -- --   --   first-preserves-⨂₁ (R ⨂ R₁) Q r k f s z t x x₁ = {!!}
      
  -- --   --   first-preserves : ∀ R r k f s z t → first R R r k f s ≡ z → Plug-μ⇑ R (In r) s t → PlugZ'-μ⇑ R z t
  -- --   --   first-preserves 0′ r k f s z t x p = {!!}
  -- --   --   first-preserves 1′ r k f s z t x p = {!!}
  -- --   --   first-preserves V r k f s z t x p = {!!}
  -- --   --   first-preserves (K A) r k f s z t x p = {!!}
  -- --   --   first-preserves (R ⨁ Q) (inj₁ r) k f s z t x p = {!p!}
  -- --   --   first-preserves (R ⨁ Q) (inj₂ q) k f s z t x p = {!!}
  -- --   --   first-preserves (R ⨂ R₁) r k f s z t x p = {!!}
  -- --   --   -- first-preserves 0′ () s z t x p
  -- --   --   -- first-preserves 1′ r s .(leaf tt IsLeaf-1′ , s) t refl p = p
  -- --   --   -- first-preserves V r s z t x p = to-left-preserves V r (tt ∷ s) t (Plug-∷ Plug-V p) z x
  -- --   --   -- first-preserves (K A) r s .(leaf r (IsLeaf-K A r) , s) t refl p = p
  -- --   --   -- first-preserves (R ⨁ Q) (inj₁ x₁) s z t x p = {!!}
  -- --   --   -- first-preserves (R ⨁ Q) (inj₂ y) s z t x p = {!!}
  -- --   --   -- first-preserves (R ⨂ Q) r s z t x p = {!!}
      
  -- --   --   to-left-preserves : (R : Reg) → (r : μ R) → (s : List (∇ R (μ R) (μ R))) → (t : μ R)
  -- --   --                     → Plug-μ⇑ R r s t → (z : UZipper' R) → to-left R r s ≡ z → PlugZ'-μ⇑ R z t
  -- --   --   to-left-preserves R (In r) s t x z p = first-preserves R r id _,_ s z  t p x
   
