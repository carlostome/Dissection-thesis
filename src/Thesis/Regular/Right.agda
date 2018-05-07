module Thesis.Regular.Right where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)
  open import Relation.Nullary
  open import Function
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

  open import Thesis.Regular.Last
  open import Thesis.Regular.First
  
  -- given a dissection and a value, try to find the next hole to the
  -- right along with the value in it.
  right : {X Y : Set} (R : Reg)
         → ∇ R Y X
         → Y
         → (⟦ R ⟧ Y) ⊎ (∇ R Y X × X)
  right 0′ () y
  right 1′ () y
  right I tt y     = inj₁ y
  right (K A) () y
  right (R ⨁ Q) (inj₁ dr) y with right R dr y
  right (R ⨁ Q) (inj₁ dr) y | inj₁ r         = inj₁ (inj₁ r)
  right (R ⨁ Q) (inj₁ dr) y | inj₂ (dr′ , x) = inj₂ (inj₁ dr′ , x)
  right (R ⨁ Q) (inj₂ dq) y with right Q dq y
  right (R ⨁ Q) (inj₂ dq) y | inj₁ q         = inj₁ (inj₂ q)
  right (R ⨁ Q) (inj₂ dq) y | inj₂ (dq′ , x) = inj₂ (inj₂ dq′ , x)
  right (R ⨂ Q) (inj₁ (dr , q)) y with right R dr y
  right {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y | inj₁ r′ with first {Y = Y} Q q
  right {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y | inj₁ r′ | inj₁ q′       = inj₁ (r′ , q′)
  right {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y | inj₁ r′ | inj₂ (dq , x) = inj₂ (inj₂ (r′ , dq) , x)
  right (R ⨂ Q) (inj₁ (dr , q)) y | inj₂ (dr′ , x) = inj₂ (inj₁ (dr′ , q) , x)
  right (R ⨂ Q) (inj₂ (r , dq)) y with right Q dq y
  right (R ⨂ Q) (inj₂ (r , dq)) y | inj₁ q′        = inj₁ (r , q′)
  right (R ⨂ Q) (inj₂ (r , dq)) y | inj₂ (dq′ , x) = inj₂ (inj₂ (r , dq′) , x)

  ------------------------------------------------------------------------------
  --                 unload preserves the tree structure


  right-Fmap : ∀ {X Y : Set} {ex : Y → X} (R : Reg) (dr : ∇ R Y X)
             → (y : Y)
             → (r : ⟦ R ⟧ Y)
             → right R dr y ≡ inj₁ r
             → ∀ e → Plug ex R dr (ex y) e → Fmap ex R r e
  right-Fmap 0′ () y r req e p
  right-Fmap 1′ () y r req e p
  right-Fmap {ex = ex} I tt y .y refl .(ex y) Plug-I = Fmap-I
  right-Fmap (K A) () y r req e p
  right-Fmap (R ⨁ Q) (inj₁ dr) y r req .(inj₁ _) (Plug-⨁-inj₁ p) with right R dr y | inspect (right R dr) y
  right-Fmap (R ⨁ Q) (inj₁ dr) y .(inj₁ x) refl .(inj₁ _) (Plug-⨁-inj₁ p) | inj₁ x | Is is = Fmap-⨁₁ (right-Fmap R dr y x is _ p)
  right-Fmap (R ⨁ Q) (inj₁ dr) y r () .(inj₁ _) (Plug-⨁-inj₁ p) | inj₂ y₁ | Is is
  right-Fmap (R ⨁ Q) (inj₂ dq) y r req e p with right Q dq y | inspect (right Q dq) y
  right-Fmap (R ⨁ Q) (inj₂ dq) y .(inj₂ x) refl .(inj₂ _) (Plug-⨁-inj₂ p) | inj₁ x | Is is = Fmap-⨁₂ (right-Fmap Q dq y x is _ p)
  right-Fmap (R ⨁ Q) (inj₂ dq) y r () .(inj₂ _) (Plug-⨁-inj₂ p) | inj₂ y₁ | Is is
  right-Fmap (R ⨂ Q) (inj₁ (dr , q)) y x req (_ , _) (Plug-⨂-inj₁ p) with right R dr y | inspect (right R dr) y
  right-Fmap {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y x req (_ , _) (Plug-⨂-inj₁ p) | inj₁ x₁ | Is is with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  right-Fmap {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y .(r′ , q′) refl (_ , _) (Plug-⨂-inj₁ p) | inj₁ r′ | Is is | inj₁ q′ | Is is′
    = Fmap-⨂ (right-Fmap R dr y r′ is _ p) (first-Fmap Q q q′ _ is′)
  right-Fmap {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y x () (_ , _) (Plug-⨂-inj₁ p) | inj₁ x₁ | Is is | inj₂ y₁ | Is is′
  right-Fmap (R ⨂ Q) (inj₁ (dr , q)) y x () (_ , _) (Plug-⨂-inj₁ p) | inj₂ y₁ | Is is
  right-Fmap (R ⨂ Q) (inj₂ (r , dq)) y x req e p with right Q dq y | inspect (right Q dq) y
  right-Fmap (R ⨂ Q) (inj₂ (r , dq)) y .(r , q) refl (_ , _) (Plug-⨂-inj₂ fm p) | inj₁ q | Is is = Fmap-⨂ fm (right-Fmap Q dq y q is _ p)
  right-Fmap (R ⨂ Q) (inj₂ (r , dq)) y x () e p | inj₂ y₁ | Is is
  
  right-Plug : ∀ {X Y : Set} {ex : Y → X} (R : Reg) (dr : ∇ R Y X)
             → (y : Y)
             → (dr′ : ∇ R Y X) → (x : X) → right R dr y ≡ inj₂ (dr′ , x)
             → ∀ e → Plug ex R dr (ex y) e → Plug ex R dr′ x e 
  right-Plug 0′ () y dr′ x req e p
  right-Plug 1′ () y dr′ x req e p
  right-Plug I tt y dr′ x () e p
  right-Plug (K A) () y dr′ x req e p
  right-Plug (R ⨁ Q) (inj₁ dr) y dr′ x req e p with right R dr y | inspect (right R dr) y
  right-Plug (R ⨁ Q) (inj₁ dr) y dr′ x () e p | inj₁ r | Is is
  right-Plug (R ⨁ Q) (inj₁ dr) y .(inj₁ dr′) .x′ refl .(inj₁ _) (Plug-⨁-inj₁ p) | inj₂ (dr′ , x′) | Is is
    = Plug-⨁-inj₁ (right-Plug R dr y dr′ x′ is _ p) 
  right-Plug (R ⨁ Q) (inj₂ dq) y dr′ x req e p with right Q dq y | inspect (right Q dq) y
  right-Plug (R ⨁ Q) (inj₂ dq) y dr′ x () e p | inj₁ r | Is is
  right-Plug (R ⨁ Q) (inj₂ dq) y .(inj₂ dq′) .x′ refl .(inj₂ _) (Plug-⨁-inj₂ p) | inj₂ (dq′ , x′) | Is is
    = Plug-⨁-inj₂ (right-Plug Q dq y dq′ x′ is _ p)
  right-Plug (R ⨂ Q) (inj₁ (dr , q)) y dr′ x req e p with right R dr y | inspect (right R dr) y
  right-Plug {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y dr′ x req e p | inj₁ r′ | Is is
    with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  right-Plug {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y dr′ x () e p | inj₁ r′ | Is is | inj₁ q′ | Is is′
  right-Plug {Y = Y} {ex} (R ⨂ Q) (inj₁ (dr , q)) y .(inj₂ (r′ , dq)) .x′ refl (_ , _) (Plug-⨂-inj₁ p) | inj₁ r′ | Is is | inj₂ (dq , x′) | Is is′
    = Plug-⨂-inj₂ (right-Fmap R dr y r′ is _ p) (first-Plug Q q dq x′ ex is′ )
  right-Plug (R ⨂ Q) (inj₁ (dr , q)) y .(inj₁ (dr′′ , q)) .x′ refl (_ , _) (Plug-⨂-inj₁ p) | inj₂ (dr′′ , x′) | Is is
    = Plug-⨂-inj₁ (right-Plug R dr y dr′′ x′ is _ p)
  right-Plug (R ⨂ Q) (inj₂ (r , dq)) y dr′ x req (_ , _) (Plug-⨂-inj₂ x₁ p) with right Q dq y | inspect (right Q dq) y
  right-Plug (R ⨂ Q) (inj₂ (r , dq)) y dr′ x () (_ , _) (Plug-⨂-inj₂ x₁ p) | inj₁ x₂ | Is is
  right-Plug (R ⨂ Q) (inj₂ (r , dq)) y .(inj₂ (r , dq′)) .x′ refl (_ , _) (Plug-⨂-inj₂ x₁ p) | inj₂ (dq′ , x′) | Is is
    = Plug-⨂-inj₂ x₁ (right-Plug Q dq y dq′ x′ is _ p)

  right-Last : ∀ {X Y : Set} (R : Reg)
             → (dr : ∇ R Y X) (y : Y)
             → Last R dr
             → (dr′ : ∇ R Y X) (x : X)
             → right R dr y ≡ inj₂ (dr′ , x) → ⊥
  right-Last 0′ () y last dr′ x req
  right-Last 1′ () y last dr′ x req
  right-Last I tt y last dr′ x ()
  right-Last (K A) () y last dr′ x req
  right-Last (R ⨁ Q) (inj₁ dr) y last dr′ x req
    with right R dr y | inspect (right R dr) y
  right-Last (R ⨁ Q) (inj₁ dr) y last dr′ x () | inj₁ dr′′ | Is is
  right-Last (R ⨁ Q) (inj₁ dr) y (Last-⨁-inj₁ last) .(inj₁ dr′′) .x′ refl
    | inj₂ (dr′′ , x′) | Is is = right-Last R dr y last dr′′ x′ is
  right-Last (R ⨁ Q) (inj₂ dq) y last dr′ x req
    with right Q dq y | inspect (right Q dq) y
  right-Last (R ⨁ Q) (inj₂ dq) y last dr′ x () | inj₁ x₁ | Is is
  right-Last (R ⨁ Q) (inj₂ dq) y (Last-⨁-inj₂ last) .(inj₂ dq′) .x′ refl
    | inj₂ (dq′ , x′) | Is is = right-Last Q dq y last dq′ x′ is
  right-Last (R ⨂ Q) (inj₁ (dr , q)) y last dr′ x req
    with right R dr y | inspect (right R dr) y
  right-Last {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y last dr′ x req | inj₁ r′ | Is is
    with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  right-Last {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y last dr′ x () | inj₁ r′ | Is is | inj₁ x₁ | Is is′
  right-Last {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y (Last-⨂₁ isl last) .(inj₂ (r′ , dq′)) .x′ refl
    | inj₁ r′ | Is is | inj₂ (dq′ , x′) | Is is′
    = First-NonRec (first-to-First Q q dq′ x′ is′) isl 
  right-Last (R ⨂ Q) (inj₁ (dr , q)) y (Last-⨂₁ isl last) .(inj₁ (dr′′ , q)) .x′ refl
    | inj₂ (dr′′ , x′) | Is is = right-Last R dr y last dr′′ x′ is
  right-Last (R ⨂ Q) (inj₂ (r , dq)) y last dr′ x req with right Q dq y | inspect (right Q dq) y
  right-Last (R ⨂ Q) (inj₂ (r , dq)) y last dr′ x () | inj₁ x₁ | Is is
  right-Last (R ⨂ Q) (inj₂ (r , dq)) y (Last-⨂₂ last) .(inj₂ (r , dq′)) .x′ refl
    | inj₂ (dq′ , x′) | Is is = right-Last Q dq y last dq′ x′ is

  right-¬Last : ∀ {X Y : Set} (R : Reg)
              → (dr : ∇ R Y X) (y : Y)
              → ¬ Last R dr
              → (r : ⟦ R ⟧ Y)
              → right R dr y ≡ inj₁ r → ⊥
  right-¬Last 0′ () y last r req
  right-¬Last 1′ () y last r req
  right-¬Last I tt y last .y refl   = last Last-I
  right-¬Last (K A) () y last r req
  right-¬Last (R ⨁ Q) (inj₁ dr) y last r req
    with right R dr y | inspect (right R dr) y
  right-¬Last (R ⨁ Q) (inj₁ dr) y last .(inj₁ x) refl | inj₁ x | Is is =  right-¬Last R dr y (last ∘ Last-⨁-inj₁) x is
  right-¬Last (R ⨁ Q) (inj₁ dr) y last r () | inj₂ _ | Is is
  right-¬Last (R ⨁ Q) (inj₂ dq) y last r req
    with right Q dq y | inspect (right Q dq) y
  right-¬Last (R ⨁ Q) (inj₂ dq) y last .(inj₂ x) refl | inj₁ x | Is is = right-¬Last Q dq y (last ∘ Last-⨁-inj₂) x is
  right-¬Last (R ⨁ Q) (inj₂ dq) y last r () | inj₂ _ | Is is
  right-¬Last (R ⨂ Q) (inj₁ (dr , q)) y last r req  with right R dr y | inspect (right R dr) y
  right-¬Last {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y last r req | inj₁ x | Is is with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  right-¬Last {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y last .(r′ , q′) refl | inj₁ r′ | Is is | inj₁ q′ | Is is′
    = right-¬Last R dr y (last ∘ (Last-⨂₁ (proj₁ (first-NonRec Q q q′ is′)))) r′ is
  right-¬Last {Y = Y} (R ⨂ Q) (inj₁ (dr , q)) y last r () | inj₁ r′ | Is is | inj₂ _ | Is is′
  right-¬Last (R ⨂ Q) (inj₁ (dr , q)) y last r () | inj₂ _ | Is is
  right-¬Last (R ⨂ Q) (inj₂ (r , dq)) y last r′ req with right Q dq y | inspect (right Q dq) y
  right-¬Last (R ⨂ Q) (inj₂ (r , dq)) y last .(r , x) refl | inj₁ x | Is is = right-¬Last Q dq y (last ∘ Last-⨂₂) x is
  right-¬Last (R ⨂ Q) (inj₂ (r , dq)) y last r′ () | inj₂ y₁ | Is is
