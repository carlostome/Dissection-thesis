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

  ----------------------------------------------------------------------------------
  --                              Core definitions                

  -- A leaf of a generic tree is from a code R is
  -- a tree without recursive positions.
  Leaf : Reg → Set → Set
  Leaf R X = Σ (⟦ R ⟧ X) λ l → NonRec R l

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


  -- UnIndexed Zipper
  UZipper : (R : Reg) → (X : Set) → (alg : ⟦ R ⟧ X → X) → Set
  UZipper R X alg = Leaf R X × Stack R X alg


  ----------------------------------------------------------------------------------
  --                              Plug
  
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

  Plug-μ⇓-to-plug-μ⇓ : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {t : μ R} {s : Stack R X alg} {o : μ R}
                     → Plug-μ⇓ R t s o → o ≡ plug-μ⇓ R t s
  Plug-μ⇓-to-plug-μ⇓ Plug-[] = refl
  Plug-μ⇓-to-plug-μ⇓ {R = R} (Plug-∷ {h = h} eq e)
    with Plug-to-plug e
  ... | refl = cong (In ∘ plug R Computed.Tree h) (Plug-μ⇓-to-plug-μ⇓ eq)
  
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

  PlugZ-μ⇑ : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → UZipper R X alg → μ R →  Set
  PlugZ-μ⇑ R (l , s) t = Plug-μ⇑ R (In (LeafToTree _ _ l)) s t

  -- --  
  -- plug-μ⇓-++ : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → (t : μ R) → (hs : Stack R X alg) → (h : ∇ R (Computed R X alg) (μ R))
  --            → plug-μ⇓ R t (hs ++ [ h ]) ≡ plug-μ⇓ R (In (plug R Computed.Tree h t)) hs
  -- plug-μ⇓-++ R t [] h       = refl
  -- plug-μ⇓-++ R t (x ∷ hs) h = cong (In ∘ (plug R Computed.Tree x)) (plug-μ⇓-++ R t hs h)

  -- plug-μ⇑-++ : (R : Reg) → (t : μ R) → (hs : List (∇ R (μ R) (μ R))) → (h : ∇ R (μ R) (μ R))
  --            → plug-μ⇑ R t (hs ++ [ h ]) ≡ In (plug R h (plug-μ⇑ R t hs))
  -- plug-μ⇑-++ R t [] h       = refl
  -- plug-μ⇑-++ R t (x ∷ hs) h = plug-μ⇑-++ R (In (plug R x t)) hs h
  
  -- -- -- plug-μ⇓ and plug-μ⇑ are related by reversing the stack
  -- -- plug-μ⇓-to-plug-μ⇑ : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
  -- --                    → plug-μ⇓ R t s ≡ plug-μ⇑ R t (reverse s)
  -- -- plug-μ⇓-to-plug-μ⇑ R t s = aux R t s (reverseView s)
  -- --       where aux : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
  -- --                 → Reverse s → plug-μ⇓ R t s ≡ plug-μ⇑ R t (reverse s)
  -- --             aux R t .[] []                          = refl
  -- --             aux R t .(hs ++ h ∷ []) (hs ∶ re ∶ʳ h)
  -- --               with reverse (hs ++ [ h ]) | reverse-++-commute hs [ h ]
  -- --             aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ reverse hs)
  -- --               | refl with plug-μ⇓ R t (hs ++ [ h ]) | plug-μ⇓-++ R t hs h
  -- --             aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ reverse hs)
  -- --               | refl | .(plug-μ⇓ R (In (plug R h t)) hs) | refl
  -- --               = aux R (In (plug R h t)) hs re
  
  -- -- plug-μ⇑-to-plug-μ⇓ : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
  -- --                    → plug-μ⇑ R t s ≡ plug-μ⇓ R t (reverse s)
  -- -- plug-μ⇑-to-plug-μ⇓ R t s = aux R t s (reverseView s)
  -- --   where aux : (R : Reg) → (t : μ R) → (s : List (∇ R (μ R) (μ R)))
  -- --             → Reverse s → plug-μ⇑ R t s ≡ plug-μ⇓ R t (reverse s)
  -- --         aux R t .[] [] = refl
  -- --         aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h)
  -- --           with reverse (hs ++ [ h ]) | reverse-++-commute hs [ h ]
  -- --         aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ reverse hs)
  -- --           | refl with plug-μ⇑ R t (hs ++ [ h ]) | plug-μ⇑-++ R t hs h
  -- --         aux R t .(hs ++ [ h ]) (hs ∶ re ∶ʳ h) | .(h ∷ foldl _ [] hs)
  -- --           | refl | .(In (plug R h (plug-μ⇑ R t hs))) | refl
  -- --           = cong (In ∘ plug R h) (aux R t hs re)
  
  Plug-μ⇓-to-Plug-μ⇑ : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {l : Leaf R X} {s : Stack R X alg} {t : μ R} → PlugZ-μ⇑ R (l , s) t → PlugZ-μ⇓ R (l , reverse s) t
  Plug-μ⇓-to-Plug-μ⇑ Plug-[]       = Plug-[]
  Plug-μ⇓-to-Plug-μ⇑ (Plug-∷ x x₁) = {!!}


  Plug-μ⇑-to-Plug-μ⇓ : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {l : Leaf R X} {s : Stack R X alg} {t : μ R} → PlugZ-μ⇓ R (l , s) t → PlugZ-μ⇑ R (l , reverse s) t
  Plug-μ⇑-to-Plug-μ⇓ = {!!}
  
  data Zipper⇓ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) (t : μ R) : Set where
    _,_ : (z : UZipper R X alg) → PlugZ-μ⇓ R z t → Zipper⇓ R X alg t

  data Zipper⇑ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) (t : μ R) : Set where
    _,_ : (z : UZipper R X alg) → PlugZ-μ⇑ R z t → Zipper⇑ R X alg t 

  Zipper⇓-to-Zipper⇑ : (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : μ R) → Zipper⇓ R X alg t → Zipper⇑ R X alg t
  Zipper⇓-to-Zipper⇑ R X alg t ((l , s) , p) = (l , (reverse s)) , {!!}

  Zipper⇑-to-Zipper⇓ : (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : μ R) → Zipper⇑ R X alg t → Zipper⇓ R X alg t
  Zipper⇑-to-Zipper⇓ R X alg t ((l , s) , p) = (l , (reverse s)) , Plug-μ⇓-to-Plug-μ⇑ p

  ----------------------------------------------------------------------------------------------
  --                               Relation over Indexed Top-Down Zippers


  data IxLt⇓ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) : (t : μ R) → Zipper⇓ R X alg t → Zipper⇓ R X alg t → Set where
    Step  : ∀ {t} {t′} {t₁ t₂} {h} {s₁ s₂} {eq₁} {eq₂} {q₁ q₂}
          →  IxLt⇓ R X alg t′     ((t₁ , s₁) , eq₁)               ((t₂ ,  s₂) ,  eq₂)
          →  IxLt⇓ R X alg (In t) ((t₁ , h ∷ s₁) , Plug-∷ eq₁ q₁) ((t₂ , h  ∷ s₂) , Plug-∷ eq₂ q₂)
             
    Base  : ∀ {t} {h₁ h₂} {s₁ s₂} {t₁ t₂} {eq₁ eq₂ q₁ q₂}
          → Dissection-IxLt (μ R) (Computed R X alg) Computed.Tree R t ((h₁ , plug-μ⇓ R (In (LeafToTree R X t₁)) s₁) ,  q₁)
                                                                       ((h₂ , plug-μ⇓ R (In (LeafToTree R X t₂)) s₂) , q₂)
          → IxLt⇓ R X alg (In t) ((t₁ , h₁ ∷ s₁) , Plug-∷ eq₁ q₁) ((t₂ , h₂ ∷ s₂) , Plug-∷ eq₂ q₂)


  ----------------------------------------------------------------------------------------------
  --                                IxLt⇓ is well founded

  private
    all-to-plug : ∀ {X : Set}  {R Q : Reg} {ex : X → μ Q} {P : μ Q → Set}
                → (∀ {t : ⟦ R ⟧ (μ Q)} → All (μ Q) P R t → (∀ (r : μ Q) (dr : ∇ R X (μ Q)) → Plug ex R dr r t → P r))
    all-to-plug (All-I x) r .tt Plug-I = x
    all-to-plug (All-⨂ x₁ x₂) r .(inj₁ (_ , _)) (Plug-⨂-inj₁ p)   = all-to-plug x₁ r _ p
    all-to-plug (All-⨂ x₁ x₂) r .(inj₂ (_ , _)) (Plug-⨂-inj₂ x p) = all-to-plug x₂ r _ p
    all-to-plug (All-⨁₁ x) r .(inj₁ _) (Plug-⨁-inj₁ p) = all-to-plug x r _ p
    all-to-plug (All-⨁₂ x) r .(inj₂ _) (Plug-⨁-inj₂ p) = all-to-plug x r _ p
    all-to-plug All-1′ r dr ()
    all-to-plug All-K  r dr ()


  acc-Base : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {r : ⟦ R ⟧ (μ R)}
           → ∀ {dr : ∇ R (Computed R X alg) (μ R)} {e : μ R} {t : Leaf R X} {s : Stack R X alg} {eq} {q}
           → (∀ (t : μ R) (dr : ∇ R (Computed R X alg) (μ R)) → Plug Computed.Tree R dr t r → Well-founded (IxLt⇓ R X alg t))
           → Acc (IxLt⇓ R X alg e) ((t , s) , eq)
           → Acc (Dissection-IxLt (μ R) (Computed R X alg) Computed.Tree R r) ((dr , e) , q)
           → WfRec (IxLt⇓ R X alg (In r))
                    (Acc (IxLt⇓ R X alg (In r)))
                    ((t , dr ∷ s) , Plug-∷ eq q)
  acc-Base {q = q} x (acc rs) ac .((_ , _ ∷ _) , Plug-∷ _ q₁) (Step {q₁ = q₁} p)
    with Plug-proof-irrelevance q q₁
  acc-Base {q = q} x (acc rs) ac .((_ , _ ∷ _) , Plug-∷ _ q) (Step {q₁ = .q} p)
    | refl = acc (acc-Base x (rs _ p) ac)
  acc-Base x (acc rs) (acc rs₁) .((_ , _ ∷ _) , Plug-∷ eq₁ q₁) (Base {eq₁ = eq₁} {q₁ = q₁} p)
    =  acc (acc-Base x (x _ _ q₁ _) (rs₁ _ p))

  
  IxLt⇓-WF : (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : μ R) → Well-founded (IxLt⇓ R X alg t)
  IxLt⇓-WF R X alg t x = acc (aux R X alg t x)
    where
       all-is-wf : (X : Set) (R Q : Reg) (alg : ⟦ R ⟧ X → X) → (t : ⟦ Q ⟧ (μ R)) → All (μ R) (λ t → Well-founded (IxLt⇓ R X alg t)) Q t
       all-is-wf X R 0′ alg ()
       all-is-wf X R 1′ alg tt   = All-1′
       all-is-wf X R I alg t     = All-I (IxLt⇓-WF R X alg t)
       all-is-wf X R (K A) alg t = All-K
       all-is-wf X R (Q ⨁ P) alg (inj₁ x) = All-⨁₁ (all-is-wf X R Q alg x)
       all-is-wf X R (Q ⨁ P) alg (inj₂ y) = All-⨁₂ (all-is-wf X R P alg y)
       all-is-wf X R (Q ⨂ P) alg (x , y)  = All-⨂ (all-is-wf X R Q alg x) (all-is-wf X R P alg y)
     
       aux : ∀ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : (μ R)) → (x : Zipper⇓ R X alg t) → WfRec (IxLt⇓ R X alg t) (Acc (IxLt⇓ R X alg t)) x
       aux R X alg .(In _) .((_ , _ ∷ _) , Plug-∷ _ q₂) .((_ , _ ∷ _) , Plug-∷ eq₁ q₁) (Step {eq₁ = eq₁} {q₁ = q₁} {q₂} p)
         = acc (acc-Base (all-to-plug {P = λ t → Well-founded (IxLt⇓ R X alg t)} (all-is-wf X R R alg _))
                         (all-to-plug {P = λ t → Well-founded (IxLt⇓ R X alg t)} (all-is-wf X R R alg _) _ _ q₂ (_ , eq₁))
                         (Dissection-IxLt-WF (μ R) (Computed R X alg) Computed.Tree R _ (_ , q₁)))
       aux R X alg .(In _) .((_ , _ ∷ _) , Plug-∷ _ _) .((_ , _ ∷ _) , Plug-∷ eq₁ q₁) (Base {eq₁ = eq₁} {q₁ = q₁} p)
         = acc (acc-Base (all-to-plug {P = λ t → Well-founded (IxLt⇓ R X alg t)} (all-is-wf X R R alg _))
                         (all-to-plug {P = λ t₁ → Well-founded (IxLt⇓ R X alg t₁)} (all-is-wf X R R alg _) _ _ q₁ (_ , eq₁))
                         (Dissection-IxLt-WF (μ R) (Computed R X alg) Computed.Tree R _ (_ , q₁)))

  -----------------------------------------------------------------------------------------------
  --                 Relation over Bottom-Up Zippers
     
  data IxLt⇑ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) (t : μ R) : Zipper⇑ R X alg t → Zipper⇑ R X alg t → Set where
    ixLt⇑ : ∀ z₁ z₂ → IxLt⇓ R X alg t (Zipper⇑-to-Zipper⇓ R X alg t z₁) (Zipper⇑-to-Zipper⇓ R X alg t z₂) → IxLt⇑ R X alg t z₁ z₂

  IxLt⇑-WF : (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : μ R) → Well-founded (IxLt⇑ R X alg t)
  IxLt⇑-WF R X alg t x = acc (aux R X alg t x (IxLt⇓-WF R X alg t (Zipper⇑-to-Zipper⇓ R X alg t x)))
     where 
      aux : ∀ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) → (t : (μ R)) → (x : Zipper⇑ R X alg t)
          → Acc (IxLt⇓ R X alg t) (Zipper⇑-to-Zipper⇓ R X alg t x) → WfRec (IxLt⇑ R X alg t) (Acc (IxLt⇑ R X alg t)) x
      aux R X alg t x (acc rs) y (ixLt⇑ .y .x p) = acc (aux R X alg t y (rs (Zipper⇑-to-Zipper⇓ R X alg t y) p))


  -----------------------------------------------------------------------------------------------
  --                     UnIndexed version of the smaller-than relation

  data Lt (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) : UZipper R X alg → UZipper R X alg → Set where
    Step  : ∀ {t₁ t₂} {h} {s₁ s₂}
          →  Lt R X alg (t₁ , s₁)     (t₂ ,  s₂)
          →  Lt R X alg (t₁ , h ∷ s₁) (t₂ , h  ∷ s₂)
             
    Base  : ∀ {h₁ h₂} {s₁ s₂} {t₁ t₂}
          → Dissection-Lt (μ R) (Computed R X alg) R
                  (h₁ , plug-μ⇓ R (In (LeafToTree R X t₁)) s₁)
                  (h₂ , plug-μ⇓ R (In (LeafToTree R X t₂)) s₂)
          → Lt R X alg (t₁ , h₁ ∷ s₁) (t₂ , h₂ ∷ s₂)

  -- convert from the un-indexed relation to the indexed once
  -- provided with the proof that the Zippers plug to the same tree
  Lt-to-IxLt⇓ : {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {t : μ R}
             → {z₁ z₂ : UZipper R X alg} → (eq₁ : PlugZ-μ⇓ R z₁ t) → (eq₂ : PlugZ-μ⇓ R z₂ t)
             → Lt R X alg z₁ z₂ → IxLt⇓ R X alg t (z₁ , eq₁) (z₂ , eq₂)
  Lt-to-IxLt⇓ {t = In t} (Plug-∷ eq₁ x₁) (Plug-∷ eq₂ x₂) (Step p)
    with Plug-injective-on-2 x₁ x₂
  ... | refl = Step (Lt-to-IxLt⇓ eq₁ eq₂ p)
  Lt-to-IxLt⇓ {t = In t} (Plug-∷ eq₁ x₁) (Plug-∷ eq₂ x₂) (Base x)
    with Plug-μ⇓-to-plug-μ⇓ eq₁ | Plug-μ⇓-to-plug-μ⇓ eq₂
  ... | refl | refl = Base (Dissection-Lt-to-IxLt x₁ x₂ x)


  ------------------------------------------------------------------------------------------------
  --                           load function
  
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

  load : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → μ R → Stack R X alg → UZipper R X alg ⊎ X
  load R (In t) s = inj₁ (first R R t id _,_ s)

  ------------------------------------------------------------------------------------------
  --                  load preserves the tree

  -- -- data First {X : Set} : (R : Reg) → ⟦ R ⟧ X → ∇ R X X × X → Set where
  -- --   First-⨁-inj₁ : ∀ {R Q} {r} {rx x} → First R r (rx , x) → First (R ⨁ Q) (inj₁ r) (inj₁ rx , x)
  -- --   First-⨁-inj₂ : ∀ {R Q} {q} {qx x} → First Q q (qx , x) → First (R ⨁ Q) (inj₂ q) (inj₂ qx , x)
  -- --   First-I       : ∀ {x} → First I x (tt , x)
  -- --   First-⨂₁     : ∀ {R Q} {rx x} {r q} → First R r (rx , x) → First (R ⨂ Q) (r , q) (inj₁ (rx , q) , x)
  -- --   First-⨂₂     : ∀ {R Q} {qx x} {r q} → NonRec {X} R r     → First Q q (qx , x) → First (R ⨂ Q) (r , q) (inj₂ (r , qx) , x)

  -- -- First-NonRec : ∀ {X : Set} R r rx (x : X) → First R r (rx , x) → NonRec R r → ⊥
  -- -- First-NonRec .1′ .tt rx x () NonRec-1′
  -- -- First-NonRec .(K B) r rx x () (NonRec-K B .r)
  -- -- First-NonRec .(R ⨁ Q) .(inj₁ r) .(inj₁ _) x (First-⨁-inj₁ x₁) (NonRec-⨁-inj₁ R Q r x₂)     = First-NonRec R r _ x x₁ x₂
  -- -- First-NonRec .(R ⨁ Q) .(inj₂ q) .(inj₂ _) x (First-⨁-inj₂ x₁) (NonRec-⨁-inj₂ R Q q x₂)     = First-NonRec Q q _ x x₁ x₂
  -- -- First-NonRec .(R ⨂ Q) .(r , q) .(inj₁ (_ , q)) x (First-⨂₁ x₁) (NonRec-⨂ R Q r q x₂ x₃)    = First-NonRec R r _ x x₁ x₂
  -- -- First-NonRec .(R ⨂ Q) .(r , q) .(inj₂ (r , _)) x (First-⨂₂ x₁ x₄) (NonRec-⨂ R Q r q x₂ x₃) = First-NonRec Q q _ x x₄ x₃
 
  -- -- First-Unique : ∀ {X : Set} {R : Reg} {r : ⟦ R ⟧ X} {x y} → First R r x → First R r y → x ≡ y
  -- -- First-Unique (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) with First-Unique f₁ f₂
  -- -- First-Unique (First-⨁-inj₁ f₁) (First-⨁-inj₁ f₂) | refl = refl
  -- -- First-Unique (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) with First-Unique f₁ f₂
  -- -- First-Unique (First-⨁-inj₂ f₁) (First-⨁-inj₂ f₂) | refl = refl
  -- -- First-Unique First-I First-I = refl
  -- -- First-Unique (First-⨂₁ f₁) (First-⨂₁ f₂) with First-Unique f₁ f₂
  -- -- First-Unique (First-⨂₁ f₁) (First-⨂₁ f₂) | refl = refl
  -- -- First-Unique (First-⨂₁ f₁) (First-⨂₂ x f₂) = ⊥-elim (First-NonRec _ _ _ _ f₁ x)
  -- -- First-Unique (First-⨂₂ x f₁) (First-⨂₁ f₂) = ⊥-elim (First-NonRec _ _ _ _ f₂ x)
  -- -- First-Unique (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) with First-Unique f₁ f₂
  -- -- First-Unique (First-⨂₂ x f₁) (First-⨂₂ x′ f₂) | refl = refl
   
  -- -- view : {X : Set} → (R : Reg) → (Q : Reg) → (r : ⟦ R ⟧ (μ Q)) → (Σ (∇ R (μ Q) (μ Q)) λ dr
  -- --                                                              →  Σ (μ Q) λ q → First R r (dr , q))
  -- --                                                              ⊎ (Σ (⟦ R ⟧ X) λ l → (NonRec R l × [ R ]-[ μ Q ] r ≈[ X ] l))
  -- -- view 0′ Q ()
  -- -- view 1′ Q tt   = inj₂ (tt , NonRec-1′ , ≈-1′)
  -- -- view I Q r     = inj₁ (tt , r , First-I)
  -- -- view (K A) Q r = inj₂ (r , NonRec-K A r , ≈-K)
  -- -- view {X} (R ⨁ Q) P (inj₁ x) with view {X} R P x
  -- -- view (R ⨁ Q) P (inj₁ x) | inj₁ (dr , mq , f)   = inj₁ ((inj₁ dr) , (mq , (First-⨁-inj₁ f)))
  -- -- view (R ⨁ Q) P (inj₁ x) | inj₂ (l , is-l , eq) = inj₂ ((inj₁ l)  , (NonRec-⨁-inj₁ R Q l is-l , ≈-⨁₁ eq))
  -- -- view {X} (R ⨁ Q) P (inj₂ y) with view {X} Q P y
  -- -- view {X} (R ⨁ Q) P (inj₂ y) | inj₁ (dq , mq , f)   = inj₁ (inj₂ dq , mq , First-⨁-inj₂ f)
  -- -- view {X} (R ⨁ Q) P (inj₂ y) | inj₂ (l , is-l , eq) = inj₂ (inj₂ l , NonRec-⨁-inj₂ R Q l is-l , ≈-⨁₂ eq)
  -- -- view {X} (R ⨂ Q) P (r , q)  with view {X} R P r
  -- -- view {X} (R ⨂ Q) P (r , q) | inj₁ (dr , mq , f)    = inj₁ ((inj₁ (dr , q)) , (mq , First-⨂₁ f))
  -- -- view {X} (R ⨂ Q) P (r , q) | inj₂ (l  , is-l , eq) with view {X} Q P q
  -- -- view {X} (R ⨂ Q) P (r , q) | inj₂ (l , is-l , eq) | inj₁ (dr , mq , f)      = inj₁ ((inj₂ (r , dr)) , (mq , First-⨂₂ (≈-NonRec l is-l r (≈-sym eq)) f))
  -- -- view {X} (R ⨂ Q) P (r , q) | inj₂ (l , is-l , eq) | inj₂ (l′ , is-l′ , eq′) = inj₂ ((l , l′) , NonRec-⨂ R Q l l′ is-l is-l′ , ≈-⨂ eq eq′)

  -- -- First-to-Plug : ∀ {X : Set} {R : Reg} {r : ⟦ R ⟧ X} {dr : ∇ R X X} {x : X} → First R r (dr , x) → Plug R dr x r
  -- -- First-to-Plug (First-⨁-inj₁ x₁) = Plug-⨁-inj₁ (First-to-Plug x₁)
  -- -- First-to-Plug (First-⨁-inj₂ x₁) = Plug-⨁-inj₂ (First-to-Plug x₁)
  -- -- First-to-Plug First-I            = Plug-I
  -- -- First-to-Plug (First-⨂₁ x₁)     = Plug-⨂-inj₁ (First-to-Plug x₁)
  -- -- First-to-Plug (First-⨂₂ x₁ x₂)  = Plug-⨂-inj₂ (First-to-Plug x₂)

  -- -- Prop : {X : Set} (R : Reg) → (Q : Reg) → ⟦ R ⟧ (μ Q) →  (∇ R (μ Q) (μ Q) → ∇ Q (μ Q) (μ Q))
  -- --      → List (∇ Q (μ Q) (μ Q)) → (Leaf R X → List (∇ Q (μ Q) (μ Q)) → UZipper' Q X) → (μ Q) → Set
  -- -- Prop {X} R Q r k s f t with view {X} R Q r
  -- -- Prop {X} R Q r k s f t | inj₁ (dr , q , _)  = Σ (⟦ Q ⟧ (μ Q)) λ e → Plug Q (k dr) q e × Plug-μ⇑ Q (In e) s t
  -- -- Prop {X} R Q r k s f t | inj₂ (l , isl , _) = PlugZ'-μ⇑ Q (f (l , isl) s) t

  -- -- propR : ∀ {X : Set} R r s t → Plug-μ⇑ R (In r) s t → Prop {X} R R r id s _,_ t
  -- -- propR {X} R r s t p with view {X} R R r
  -- -- propR {X} R r s t p | inj₁ (dr , mr , pl)    = r , (First-to-Plug pl , p)
  -- -- propR {X} .1′ .tt s t p | inj₂ (.tt , NonRec-1′ , ≈-1′) = p
  -- -- propR {X} .(K B) .l s t p | inj₂ (l , NonRec-K B .l , ≈-K) = p
  -- -- propR {X} .(R ⨁ Q) .(inj₁ x) s t p | inj₂ (.(inj₁ r) , NonRec-⨁-inj₁ R Q r isl , ≈-⨁₁ {x = x} eq)
  -- --   rewrite coerce-≈ r isl x (≈-sym eq) = p
  -- -- propR {X} .(R ⨁ Q) .(inj₂ x) s t p | inj₂ (.(inj₂ q) , NonRec-⨁-inj₂ R Q q isl , ≈-⨁₂ {x = x} eq)
  -- --   rewrite coerce-≈ q isl x (≈-sym eq) = p
  -- -- propR {X} .(R ⨂ Q) (r , q) s t p | inj₂ (.(r′ , q′) , NonRec-⨂ R Q r′ q′ isl₁ isl₂ , ≈-⨂ eq₁ eq₂)
  -- --   rewrite coerce-≈ r′ isl₁ r (≈-sym eq₁) | coerce-≈ q′ isl₂ q (≈-sym eq₂) = p

  -- -- Plug-NonRec : ∀ {X : Set} {R : Reg} → (x : X) → (dₓ : ∇ R X X) → (tₓ : ⟦ R ⟧ X) → NonRec R tₓ → Plug R dₓ x tₓ → ⊥
  -- -- Plug-NonRec x .tt .x () Plug-I
  -- -- Plug-NonRec x .(inj₁ _) .(inj₁ r) (NonRec-⨁-inj₁ R Q r p) (Plug-⨁-inj₁ nr)      = Plug-NonRec x _ r p nr
  -- -- Plug-NonRec x .(inj₂ _) .(inj₂ q) (NonRec-⨁-inj₂ R Q q p) (Plug-⨁-inj₂ nr)      = Plug-NonRec x _ q p nr
  -- -- Plug-NonRec x .(inj₁ (_ , q)) .(r , q) (NonRec-⨂ R Q r q p p₁) (Plug-⨂-inj₁ nr) = Plug-NonRec x _ r p nr
  -- -- Plug-NonRec x .(inj₂ (r , _)) .(r , q) (NonRec-⨂ R Q r q p p₁) (Plug-⨂-inj₂ nr) = Plug-NonRec x _ q p₁ nr
    
  -- -- mutual
  -- --   first-lemma : {X : Set} (R Q : Reg) → (r : ⟦ R ⟧ (μ Q)) 
  -- --               → (k : ∇ R (μ Q) (μ Q) → ∇ Q (μ Q) (μ Q))
  -- --               → (f : Leaf R X → List (∇ Q (μ Q) (μ Q)) → UZipper' Q X)
  -- --               → (s : List (∇ Q (μ Q) (μ Q)))
  -- --               → (t : μ Q)
  -- --               → (z : UZipper' Q X)
  -- --               → first R Q r k f s ≡ z → Prop R Q r k s f t → PlugZ'-μ⇑ Q z t
  -- --   first-lemma {X} R Q r k f s  t z x p with view {X} R Q r
  -- --   first-lemma {X} 0′ Q () k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (dr , mq , fst)
  -- --   first-lemma {X} 1′ Q r k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (() , mq , fst)
  -- --   first-lemma {X} I Q r k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.tt , .r , First-I)
  -- --     = load-preserves Q r (k tt ∷ s) t (Plug-∷ plug-e plugm-e) z x
  -- --   first-lemma {X} (K A) Q r k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (() , mq , fst)
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst)
  -- --     with view {X} R P r | first-lemma R P r (k ∘ inj₁) (first-⨁₁ R Q P f) s t z x
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ _) , mq , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont
  -- --     with First-Unique fst fst′
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ dr′) , .mq′ , First-⨁-inj₁ {r = r} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
  -- --     = cont (e , (plug-e , plugm-e))
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₁ r) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ dr) , mq , First-⨁-inj₁ {r = r} {dr} fst) | inj₂ (l , isl , eq) | _
  -- --     = ⊥-elim (First-NonRec R r dr mq fst (≈-NonRec l isl r (≈-sym eq)))
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst)
  -- --     with view {X} Q P q | first-lemma Q P q (k ∘ inj₂) (first-⨁₂ R Q P f) s t z x
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ qx) , mq , First-⨁-inj₂ {q = q} {qx} fst) | inj₁ (dr , mq′ , fst′) | cont
  -- --     with First-Unique fst fst′
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ dr) , .mq′ , First-⨁-inj₂ {q = q} {.dr} fst) | inj₁ (dr , mq′ , fst′) | cont | refl = cont (e , plug-e , plugm-e)
  -- --   first-lemma {X} (R ⨁ Q) P .(inj₂ q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ dq) , mq , First-⨁-inj₂ {q = q} {dq} fst) | inj₂ (l , isl , eq) | _
  -- --     =  ⊥-elim (First-NonRec Q q dq mq fst (≈-NonRec l isl q (≈-sym eq)))
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e) | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst)
  -- --     with view {X} R P r | first-lemma R P r (λ z₁ → k (inj₁ (z₁ , q))) (first-⨂-1 R Q P k f q r) s t z x
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ (rx , q)) , mq , First-⨂₁ {rx = rx} fst) | inj₁ (dr′ , mq′ , fst′) | cont
  -- --     with First-Unique fst fst′
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ (dr′ , q)) , .mq′ , First-⨂₁ {rx = .dr′} fst) | inj₁ (dr′ , mq′ , fst′) | cont | refl
  -- --     = cont (e , plug-e , plugm-e)
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₁ (dr , q)) , mq , First-⨂₁ {rx = dr} fst) | inj₂ (l , isl , eq) | cont
  -- --     = ⊥-elim ((First-NonRec R r dr mq fst (≈-NonRec l isl r (≈-sym eq))))
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (_ , qx)) , mq , First-⨂₂ {qx = qx} nr fst)
  -- --     with view {X} R P r  | first-lemma R P r (λ z₁ → k (inj₁ (z₁ , q))) (first-⨂-1 R Q P k f q r) s t z x
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₁ (dr′ , mq′ , fst′) | cont
  -- --     = ⊥-elim (First-NonRec R r dr′ mq′ fst′ nr)
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont
  -- --     with first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (r′ , nr-r)) s | inspect (first Q P q (k ∘ inj₂ ∘ (_,_ r)) (first-⨂-2 R Q P f (r′ , nr-r))) s 
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁
  -- --     with view {X} Q P q | first-lemma Q P q (λ z₁ → k (inj₂ (r , z₁))) ((first-⨂-2 R Q P f (r′ , nr-r))) s t z′ eq₁
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (r , qx)) , mq , First-⨂₂ {qx = qx} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁ | inj₁ (dr′′ , mq′′ , fst′′) | cont′
  -- --     with First-Unique fst fst′′
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (r , dr′′)) , .mq′′ , First-⨂₂ {qx = .dr′′} nr fst) | inj₂ (r′ , nr-r , eq) | cont | z′ | Is eq₁ | inj₁ (dr′′ , mq′′ , fst′′) | cont′ | refl
  -- --     = cont (cont′ (e , plug-e , plugm-e))
  -- --   first-lemma {X} (R ⨂ Q) P (r , q) k f s t z x (e , plug-e , plugm-e)
  -- --     | inj₁ (.(inj₂ (r , dq)) , mq , First-⨂₂ {qx = dq} isl fst) | inj₂ (l′ , isl′ , eq) | g | z′ | Is eq₁ | inj₂ (l′′ , isl′′ , eq′′) | cont′
  -- --     = ⊥-elim (First-NonRec Q q dq mq fst (≈-NonRec l′′ isl′′ q (≈-sym eq′′)))
    
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

  -- load-preserves : {X : Set} (R : Reg) {alg : ⟦ R ⟧ X → X} → (r : μ R) → (s : List (∇ R (Solved R X alg) (μ R))) → (t : μ R)
  --                → Plug-μ⇑ R r s t → (z : UZipper R X alg) → load R r s ≡ inj₁ z → PlugZ-μ⇑ R z t
  -- load-preserves R (In r) s t x z p = {!!}


  ---------------------------------------------------------------------------------------------
  --                                  unload function
  
  -- first-aux performs recursion on the functorial layer of the tree either
  -- finding whether there are no more left holes to the right.
  first-aux : {X Y : Set} (R : Reg)
            → ⟦ R ⟧ Y
            → ⟦ R ⟧ X ⊎ (∇ R X Y × Y)
  first-aux 0′ ()
  first-aux 1′ tt   = inj₁ tt
  first-aux I x     = inj₂ (tt , x)
  first-aux (K A) x = inj₁ x
  first-aux {X} {Y} (R ⨁ Q) (inj₁ r) with first-aux {X} {Y} R r
  first-aux (R ⨁ Q) (inj₁ r) | inj₁ x        = inj₁ (inj₁ x)
  first-aux (R ⨁ Q) (inj₁ r) | inj₂ (dr , y) = inj₂ (inj₁ dr , y) 
  first-aux {X} {Y} (R ⨁ Q) (inj₂ q) with first-aux {X} {Y} Q q
  first-aux {X} {Y} (R ⨁ Q) (inj₂ q) | inj₁ x        = inj₁ (inj₂ x)
  first-aux {X} {Y} (R ⨁ Q) (inj₂ q) | inj₂ (dq , y) = inj₂ (inj₂ dq , y)
  first-aux {X} {Y} (R ⨂ Q) (r , q) with first-aux {X} {Y} R r
  first-aux {X} {Y} (R ⨂ Q) (r , q) | inj₁ r′ with first-aux {X} {Y} Q q
  first-aux {X} {Y} (R ⨂ Q) (r , q) | inj₁ r′ | inj₁ q′       = inj₁ (r′ , q′)
  first-aux {X} {Y} (R ⨂ Q) (r , q) | inj₁ r′ | inj₂ (dq , y) = inj₂ (inj₂ (r′ , dq) , y)
  first-aux {X} {Y} (R ⨂ Q) (r , q) | inj₂ (dr , y)           = inj₂ (inj₁ (dr , q) , y)

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
    with first-aux {X = Computed P X alg } {Y = μ P}  Q q
  right (R ⨂ Q) P (inj₁ (dr , q)) t y eq | inj₁ r | inj₁ q′        = inj₁ (r , q′) 
  right (R ⨂ Q) P (inj₁ (dr , q)) t y eq | inj₁ r | inj₂ (dq , mq) = inj₂ ((inj₂ (r  , dq)) , mq)
  right (R ⨂ Q) P (inj₁ (dr , q)) t y eq | inj₂ (dr′ , mq)         = inj₂ ((inj₁ (dr′ , q)) , mq)
  right (R ⨂ Q) P (inj₂ (r , dq)) t y eq with right Q P dq t y eq
  right (R ⨂ Q) P (inj₂ (r , dq)) t y eq | inj₁ x          = inj₁ (r , x)
  right (R ⨂ Q) P (inj₂ (r , dq)) t y eq | inj₂ (dq′ , mq) = inj₂ ((inj₂ (r , dq′)) , mq)

  unload : {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X)
         → (t : μ R) → (x : X) → Catamorphism R alg t x
         → List (∇ R (Computed R X alg) (μ R))
         → UZipper R X alg ⊎ X
  unload R alg t x eq []       = inj₂ x
  unload R alg t x eq (h ∷ hs) with right R R h t x eq
  unload R alg t x eq (h ∷ hs) | inj₁ r             = unload R alg (In (fmap R Computed.Tree r)) (alg (fmap R Computed.Value r)) {!!} hs
  unload R alg t x eq (h ∷ hs) | inj₂ (dr , q)      = load R q (dr ∷ hs)


  step : {X : Set} → (R : Reg) → (alg : ⟦ R ⟧ X → X)
       → UZipper R X alg → UZipper R X alg ⊎ X
  step R alg ((l , isl) , s) = unload R alg (In (coerce l isl)) (alg l) {!!} s

  stepIx : ∀ {X : Set} → (R : Reg) → {t : μ R} → (alg : ⟦ R ⟧ X → X)
         → Zipper⇑ R X alg t → Zipper⇑ R X alg t ⊎ X
  stepIx R alg x = {!!}


  stepIx-Lt : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {t : μ R}
          → (z₁ z₂ : Zipper⇑ R X alg t) → stepIx R alg z₁ ≡ inj₁ z₂ → IxLt⇑ R X alg t z₂ z₁
  stepIx-Lt z₁ z₂ x = {!!}

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
    with first-aux {X = Computed P X alg } {Y = μ P} Q q | inspect (first-aux {X = Computed P X alg } {Y = μ P}Q) q
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

  -- first-aux-Fmap : ∀ {X Y : Set} (R : Reg)
  --                → (r : ⟦ R ⟧ Y) → (r′ : ⟦ R ⟧ X)
  --                → (ex : X → Y) → first-aux R r ≡ inj₁ r′ → Fmap ex R r′ r 
  -- first-aux-Fmap 0′ () r′ ex eq
  -- first-aux-Fmap 1′ tt tt ex eq = Fmap-1′
  -- first-aux-Fmap I r r′ ex ()
  -- first-aux-Fmap (K A) r .r ex refl = Fmap-K
  -- first-aux-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) r′ ex eq
  --   with first-aux {X} R r | inspect (first-aux {X} R) r
  -- first-aux-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) .(inj₁ x) ex refl
  --   | inj₁ x | Is is = Fmap-⨁₁ (first-aux-Fmap R r x ex is)
  -- first-aux-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) r′ ex () | inj₂ y | Is is
  -- first-aux-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) r′ ex eq
  --   with first-aux {X} Q q | inspect (first-aux {X} Q) q
  -- first-aux-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) .(inj₂ x) ex refl
  --   | inj₁ x | Is is = Fmap-⨁₂ (first-aux-Fmap Q q x ex is)
  -- first-aux-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) r′ ex () | inj₂ y | Is is
  -- first-aux-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex x
  --   with first-aux {X} R r | inspect (first-aux {X} R) r 
  -- first-aux-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex x | inj₁ x₁ | Is is
  --   with first-aux {X} Q q | inspect (first-aux {X} Q) q
  -- first-aux-Fmap {X} {Y} (R ⨂ Q) (r , q) .(r′ , q′) ex refl
  --   | inj₁ r′ | Is is | inj₁ q′ | Is is′ = Fmap-⨂ (first-aux-Fmap R r r′ ex is) (first-aux-Fmap Q q q′ ex is′)
  -- first-aux-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex () | inj₁ x₁ | Is is | inj₂ y | Is is′
  -- first-aux-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex () | inj₂ y | Is is

  -- first-aux-Plug : ∀ {X Y : Set} (R : Reg)
  --                → (r : ⟦ R ⟧ Y) → (dr : ∇ R X Y)
  --                → (y : Y) → (ex : X → Y) → first-aux R r ≡ inj₂ (dr , y) → Plug ex R dr y r
  -- first-aux-Plug 0′ () dr y ex eq
  -- first-aux-Plug 1′ r () y ex eq
  -- first-aux-Plug I r tt .r ex refl = Plug-I
  -- first-aux-Plug (K A) r () y ex eq
  -- first-aux-Plug {X} (R ⨁ Q) (inj₁ r) dr y ex eq with first-aux {X} R r | inspect (first-aux {X} R) r
  -- first-aux-Plug {X} (R ⨁ Q) (inj₁ r) dr y ex () | inj₁ x | Is is
  -- first-aux-Plug {X} (R ⨁ Q) (inj₁ r) .(inj₁ dr′) .y′ ex refl
  --   | inj₂ (dr′ , y′) | Is is
  --   = Plug-⨁-inj₁ (first-aux-Plug R r dr′ y′ ex is)
  -- first-aux-Plug {X} (R ⨁ Q) (inj₂ q) dr y ex eq with first-aux {X} Q q | inspect (first-aux {X} Q) q
  -- first-aux-Plug {X} (R ⨁ Q) (inj₂ q) dr y ex () | inj₁ x | Is is
  -- first-aux-Plug {X} (R ⨁ Q) (inj₂ q) .(inj₂ dq) .y′ ex refl
  --   | inj₂ (dq , y′) | Is is
  --   = Plug-⨁-inj₂ (first-aux-Plug Q q dq y′ ex is)
  -- first-aux-Plug {X} (R ⨂ Q) (r , q) dr y ex eq with first-aux {X} R r | inspect (first-aux {X} R) r
  -- first-aux-Plug {X} (R ⨂ Q) (r , q) dr y ex eq
  --   | inj₁ r′ | Is is with first-aux {X} Q q | inspect (first-aux {X} Q) q
  -- first-aux-Plug {X} (R ⨂ Q) (r , q) dr y ex () | inj₁ r′ | Is is | inj₁ x | Is is′
  -- first-aux-Plug {X} (R ⨂ Q) (r , q) .(inj₂ (r′ , dq′)) .y′ ex refl
  --   | inj₁ r′ | Is is | inj₂ (dq′ , y′) | Is is′
  --   = Plug-⨂-inj₂ (first-aux-Fmap R r r′ ex is) (first-aux-Plug Q q dq′ y′ ex is′)
  -- first-aux-Plug {X} (R ⨂ Q) (r , q) .(inj₁ (dr′ , q)) .q′ ex refl
  --   | inj₂ (dr′ , q′) | Is is
  --   = Plug-⨂-inj₁ (first-aux-Plug R r dr′ q′ ex is)

  
  -- -- -- right-Fmap : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} (dr : ∇ R (Solved Q X alg) (μ Q))
  -- -- --            → (t : μ Q) → (y : X) → (eq : cata Q alg t ≡ y)
  -- -- --            → (r : ⟦ R ⟧ (Solved Q X alg)) → right R Q dr t y eq ≡ inj₁ r → ∀ e
  -- -- --            → Plug (proj₁ ∘ proj₁) R dr t e → Fmap (proj₁ ∘ proj₁) R r e
  -- -- -- right-Fmap 0′ Q dr t y eq r x () p
  -- -- -- right-Fmap 1′ Q () t y eq r x e p
  -- -- -- right-Fmap I Q dr t y eq r () e p
  -- -- -- right-Fmap (K A) Q () t y eq r x e p
  -- -- -- right-Fmap (R ⨁ Q) P (inj₁ x₁) t y eq r x .(inj₁ _) (Plug-⨁-inj₁ p)
  -- -- --   with right R P x₁ t y eq | inspect (right R P x₁ t y) eq
  -- -- -- right-Fmap (R ⨁ Q) P (inj₁ x₁) t y eq .(inj₁ r′) refl .(inj₁ _) (Plug-⨁-inj₁ p)
  -- -- --   | inj₁ r′ | Is is = Fmap-⨁₁ (right-Fmap R P x₁ t y eq r′ is _ p)
  -- -- -- right-Fmap (R ⨁ Q) P (inj₁ x₁) t y eq r () .(inj₁ _) (Plug-⨁-inj₁ p) | inj₂ _ | Is is
  -- -- -- right-Fmap (R ⨁ Q) P (inj₂ y₁) t y eq r x .(inj₂ _) (Plug-⨁-inj₂ p)
  -- -- --   with right Q P y₁ t y eq | inspect (right Q P y₁ t y) eq
  -- -- -- right-Fmap (R ⨁ Q) P (inj₂ y₁) t y eq .(inj₂ x₁) refl .(inj₂ _) (Plug-⨁-inj₂ p) | inj₁ x₁ | Is is
  -- -- --   = Fmap-⨁₂ (right-Fmap Q P y₁ t y eq x₁ is _ p)
  -- -- -- right-Fmap (R ⨁ Q) P (inj₂ y₁) t y eq r () .(inj₂ _) (Plug-⨁-inj₂ p) | inj₂ y₂ | Is is
  -- -- -- right-Fmap (R ⨂ Q) P (inj₁ (dr , q)) t y eq r′ x (_ , _) (Plug-⨂-inj₁ p)
  -- -- --   with right R P dr t y eq | inspect (right R P dr t y) eq
  -- -- -- right-Fmap {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq r′ x (r′′ , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is
  -- -- --   with first-aux {X = Σ (X × μ P) λ { (x , t) → cata P alg t ≡ x }} {Y = μ P} Q q | inspect (first-aux {X = Σ (X × μ P) λ { (x , t) → cata P alg t ≡ x }} {Y = μ P} Q) q
  -- -- -- right-Fmap {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq .(r , q′) refl (r′′ , _) (Plug-⨂-inj₁ p)
  -- -- --   | inj₁ r | Is is | inj₁ q′ | Is is′
  -- -- --   = Fmap-⨂ (right-Fmap R P dr t y eq r is r′′ p) (first-aux-Fmap Q q q′ (proj₂ ∘ proj₁) is′)
  -- -- -- right-Fmap {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq r′ () (r′′ , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is | inj₂ y₁ | Is is′ 
  -- -- -- right-Fmap (R ⨂ Q) P (inj₁ (dr , q)) t y eq r′ () (_ , _) (Plug-⨂-inj₁ p) | inj₂ y₁ | Is is
  -- -- -- right-Fmap (R ⨂ Q) P (inj₂ (r  , dq)) t y eq r′ x e p with right Q P dq t y eq | inspect (right Q P dq t y) eq
  -- -- -- right-Fmap (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(r , x₁) refl (_ , _) (Plug-⨂-inj₂ p x)
  -- -- --   | inj₁ x₁ | Is is
  -- -- --   = Fmap-⨂ x (right-Fmap Q P dq t y eq x₁ is _ p)
  -- -- -- right-Fmap (R ⨂ Q) P (inj₂ (r , dq)) t y eq r′ () e p | inj₂ y₁ | Is is
  
  -- -- -- right-Plug : ∀ {X : Set} (R Q : Reg) {alg : ⟦ Q ⟧ X → X} (dr : ∇ R (Solved Q X alg) (μ Q)) → (t : μ Q) → (y : X) → (eq : cata Q alg t ≡ y) →
  -- -- --                   (dr′ : ∇ R (Solved Q X alg) (μ Q)) → (mq : μ Q) → right R Q dr t y eq ≡ inj₂ (dr′ , mq) → ∀ e
  -- -- --                   → Plug (proj₂ ∘ proj₁) R dr t e → Plug (proj₂ ∘ proj₁) R dr′ mq e 
  -- -- -- right-Plug 0′ Q dr t y eq dr′ mq x () p
  -- -- -- right-Plug 1′ Q dr t y eq () mq x e p
  -- -- -- right-Plug I Q tt t y eq .tt .t refl e p = p
  -- -- -- right-Plug (K A) Q dr t y eq () mq x e p
  -- -- -- right-Plug (R ⨁ Q) P (inj₁ x) t y eq x′ mq r-eq .(inj₁ e) (Plug-⨁-inj₁ {e = e} p)
  -- -- --   with right R P x t y eq | inspect (right R P x t y) eq
  -- -- -- right-Plug (R ⨁ Q) P (inj₁ x) t y eq x′ mq () .(inj₁ e) (Plug-⨁-inj₁ {e = e} p) | inj₁ _ | _
  -- -- -- right-Plug (R ⨁ Q) P (inj₁ x) t y eq .(inj₁ dr′) .mq′ refl .(inj₁ e) (Plug-⨁-inj₁ {e = e} p) | inj₂ (dr′ , mq′) | Is is
  -- -- --   = Plug-⨁-inj₁ ((right-Plug R P x t y eq dr′ mq′ is e p))
  -- -- -- right-Plug (R ⨁ Q) P (inj₂ x) t y eq x′ mq r-eq .(inj₂ e) (Plug-⨁-inj₂ {e = e} p)
  -- -- --   with right Q P x t y eq | inspect (right Q P x t y) eq
  -- -- -- right-Plug (R ⨁ Q) P (inj₂ x) t y eq x′ mq () .(inj₂ e) (Plug-⨁-inj₂ {e = e} p) | inj₁ _ | _
  -- -- -- right-Plug (R ⨁ Q) P (inj₂ x) t y eq .(inj₂ dr′) .mq′ refl .(inj₂ e) (Plug-⨁-inj₂ {e = e} p) | inj₂ (dr′ , mq′) | Is is
  -- -- --   = Plug-⨁-inj₂ ((right-Plug Q P x t y eq dr′ mq′ is e p))
  -- -- -- right-Plug (R ⨂ Q) P (inj₁ (dr , q)) t y eq dr′ mq x e p
  -- -- --   with right R P dr t y eq | inspect (right R P dr t y) eq
  -- -- -- right-Plug {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq dr′ mq x (e , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is
  -- -- --   with first-aux {X = Σ (X × μ P) λ { (x , t) → cata P alg t ≡ x }} {Y = μ P} Q q | inspect (first-aux {X = Σ (X × μ P) λ { (x , t) → cata P alg t ≡ x }} {Y = μ P} Q) q
  -- -- -- right-Plug {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq dr′ mq () (e , _) (Plug-⨂-inj₁ p) | inj₁ r | Is is | inj₁ _ | _
  -- -- -- right-Plug {X} (R ⨂ Q) P {alg} (inj₁ (dr , q)) t y eq .(inj₂ (r , dq)) .mq′ refl (e , _) (Plug-⨂-inj₁ p)
  -- -- --   | inj₁ r | Is is | inj₂ (dq , mq′) | Is is′
  -- -- --   = Plug-⨂-inj₂ (first-aux-Plug Q q dq mq′ (proj₂ ∘ proj₁) is′) (right-Fmap R P dr t y eq r is e p)
  -- -- -- right-Plug (R ⨂ Q) P (inj₁ (dr , q)) t y eq .(inj₁ (dr′ , q)) .mq′′ refl (dr′′ , .q) (Plug-⨂-inj₁ p) | inj₂ (dr′ , mq′′) | Is is
  -- -- --   = Plug-⨂-inj₁ (right-Plug R P dr t y eq dr′ mq′′ is  dr′′ p)
  -- -- -- right-Plug (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ mq x (_ , _) (Plug-⨂-inj₂ p fm)
  -- -- --   with right Q P dq t y eq | inspect (right Q P dq t y) eq
  -- -- -- right-Plug (R ⨂ Q) P (inj₂ (r , dq)) t y eq dr′ mq () (_ , _) (Plug-⨂-inj₂ p fm) | inj₁ _ | Is _
  -- -- -- right-Plug (R ⨂ Q) P (inj₂ (r , dq)) t y eq .(inj₂ (r , dq′)) .mq′ refl (_ , _) (Plug-⨂-inj₂ p fm) | inj₂ (dq′ , mq′) | Is is
  -- -- --   = Plug-⨂-inj₂ (right-Plug Q P dq t y eq dq′ mq′ is _ p) fm

  -- propo : ∀ {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {l : ⟦ R ⟧ X} {isl : NonRec R l } → Catamorphism R alg (In (coerce l isl)) (alg l)
  -- propo {isl = NonRec-1′}    = Cata MapFold-1′
  -- propo {isl = NonRec-K B b} = Cata MapFold-K
  -- propo {alg = alg} {isl = NonRec-⨁-inj₁ R Q r isl} with propo {alg =  (alg ∘ inj₁)} {isl = isl}
  -- ... | z = {!!}
  -- propo {isl = NonRec-⨁-inj₂ R Q q isl} = {!!}
  -- propo {isl = NonRec-⨂ R Q r q isl isl₁} = {!!}



  
  -- -- -- unload-preserves : ∀ {X : Set} (R : Reg) (alg : ⟦ R ⟧ X → X) (t : μ R) (x : X) (eq : cata R alg t ≡ x) (hs : List (∇ R (Solved R X alg) (μ R)))
  -- -- --                  → (e : μ R) → (z : UZipper R X alg) → unload R alg t x eq hs ≡ inj₁ z → Plug-μ⇑ R t hs e → PlugZ-μ⇑ R z e
  -- -- -- unload-preserves R alg t x eq [] e z () _
  -- -- -- unload-preserves R alg t x eq (h ∷ hs) e z to-z pl
  -- -- --   with right R R h t x eq | inspect (right R R h t x) eq
  -- -- -- unload-preserves R alg t x eq (h ∷ hs) e z to-z (Plug-∷ pl pl-m) | inj₁ r | Is is
  -- -- --   = unload-preserves R alg {!!} {!!} {!!} hs e z  to-z {!!}
  -- -- -- unload-preserves R alg t x eq (h ∷ hs) e z to-z (Plug-∷ pl plm) | inj₂ (dr , q) | Is is with right-Plug {!R!} R dr q {!!} {!!} {!!} {!!} is {!!} {!!} 
  -- -- -- ... | pp  = {!!} -- load-preserves R q (dr ∷ hs) e (Plug-∷ {!!} plm) z to-z

  -- step-Lt : ∀ (X : Set) (R : Reg) (alg : ⟦ R ⟧ X → X) (z₁ z₂ : UZipper R X alg)
  --         → step R alg z₁ ≡ inj₁ z₂ → Lt R X alg z₂ z₁
  -- step-Lt X R alg ((l , isl) , s) z₂ eq = {!s!}
 
 
