
module Thesis.Dissection.Relation where

  open import Data.Product
  open import Data.Sum
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

  open import Thesis.Dissection.Core
  
  ----------------------------------------------------------------------------------------------
  --                               Relation over Indexed Top-Down Zippers


  data IxLt⇓ (R : Reg) (X : Set) (alg : ⟦ R ⟧ X → X) : (t : μ R) → Zipper⇓ R X alg t → Zipper⇓ R X alg t → Set where
    Step  : ∀ {t} {t′} {t₁ t₂} {h} {s₁ s₂} {eq₁} {eq₂} {q₁ q₂}
          →  IxLt⇓ R X alg t′     ((t₁ , s₁) , eq₁)               ((t₂ ,  s₂) ,  eq₂)
          →  IxLt⇓ R X alg (In t) ((t₁ , h ∷ s₁) , Plug-∷ eq₁ q₁) ((t₂ , h  ∷ s₂) , Plug-∷ eq₂ q₂)
             
    Base  : ∀ {t} {h₁ h₂} {s₁ s₂} {t₁ t₂} {e₁ e₂} {eq₁ eq₂ q₁ q₂}
          → PlugZ-μ⇓ R (t₁ , s₁) e₁
          → PlugZ-μ⇓ R (t₂ , s₂) e₂
          → Dissection-IxLt (μ R) (Computed R X alg) Computed.Tree R t ((h₁ , e₁) , q₁)
                                                                       ((h₂ , e₂) , q₂)
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
  acc-Base x (acc rs) (acc rs₁) .((_ , _ ∷ _) , Plug-∷ _ q₁) (Base {q₁ = q₁} p₁ p₂ r)
    =  acc (acc-Base x (x _ _ q₁ _) (rs₁ _ r))

  
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
       aux R X alg .(In _) .((_ , _ ∷ _) , Plug-∷ _ _) .((_ , _ ∷ _) , Plug-∷ eq₁ q₁) (Base {eq₁ = eq₁} {q₁ = q₁} p₁ p₂ r)
         = acc (acc-Base (all-to-plug {P = λ t → Well-founded (IxLt⇓ R X alg t)} (all-is-wf X R R alg _))
                         (all-to-plug {P = λ t₁ → Well-founded (IxLt⇓ R X alg t₁)} (all-is-wf X R R alg _) _ _ q₁ (_ , eq₁))
                         ((Dissection-IxLt-WF (μ R) (Computed R X alg) Computed.Tree R _ (_ , q₁))))
    

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
             
    Base  : ∀ {h₁ h₂} {s₁ s₂} {t₁ t₂} {e₁ e₂}
          → PlugZ-μ⇓ R (t₁ , s₁) e₁
          → PlugZ-μ⇓ R (t₂ , s₂) e₂
          → Dissection-Lt (μ R) (Computed R X alg) R (h₁ , e₁) (h₂ , e₂)
          → Lt R X alg (t₁ , h₁ ∷ s₁) (t₂ , h₂ ∷ s₂)

  -- convert from the un-indexed relation to the indexed once
  -- provided with the proof that the Zippers plug to the same tree
  Lt-to-IxLt⇓ : {X : Set} {R : Reg} {alg : ⟦ R ⟧ X → X} {t : μ R}
             → {z₁ z₂ : UZipper R X alg} → (eq₁ : PlugZ-μ⇓ R z₁ t) → (eq₂ : PlugZ-μ⇓ R z₂ t)
             → Lt R X alg z₁ z₂ → IxLt⇓ R X alg t (z₁ , eq₁) (z₂ , eq₂)
  Lt-to-IxLt⇓ {t = In t} (Plug-∷ eq₁ x₁) (Plug-∷ eq₂ x₂) (Step p)
    with Plug-injective-on-2 x₁ x₂
  ... | refl = Step (Lt-to-IxLt⇓ eq₁ eq₂ p)
  Lt-to-IxLt⇓ (Plug-∷ eq₁ q₁) (Plug-∷ eq₂ q₂) (Base p₁ p₂ r)
    with Plug-μ⇓-unicity p₁ eq₁ | Plug-μ⇓-unicity p₂ eq₂
  ... | refl | refl = Base p₁ p₂ (Dissection-Lt-to-IxLt q₁ q₂ r)

