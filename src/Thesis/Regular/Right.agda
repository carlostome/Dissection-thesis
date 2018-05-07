
module Thesis.Regular.Right where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)

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
  
  -- `first` finds the leftmost hole and the value in it if it exists.
  first : {X Y : Set} (R : Reg)
        → ⟦ R ⟧ X
        → ⟦ R ⟧ Y ⊎ (∇ R Y X × X)
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

  -- when `first` doesn't find a hole then the input is
  -- heterogeneously equal to the output
  first-≈ : {X Y : Set} (R : Reg)
          → (i : ⟦ R ⟧ X)
          → (o : ⟦ R ⟧ Y)
          → first R i ≡ inj₁ o → [ R ]-[ X ] i ≈[ Y ] o
  first-≈ 0′ () o x
  first-≈ 1′ tt .tt refl = ≈-1′
  first-≈ I i o ()
  first-≈ (K A) i .i refl = ≈-K
  first-≈ {X} {Y} (R ⨁ Q) (inj₁ r) o x with first {X} {Y} R r | inspect (first {X} {Y} R) r
  first-≈ {X} {Y} (R ⨁ Q) (inj₁ r) .(inj₁ o′) refl | inj₁ o′ | Is is = ≈-⨁₁ (first-≈ R r o′ is)
  first-≈ {X} {Y} (R ⨁ Q) (inj₁ r) o ()            | inj₂ o′ | Is is
  first-≈ {X} {Y} (R ⨁ Q) (inj₂ q) o x with first {X} {Y} Q q | inspect (first {X} {Y} Q) q
  first-≈ {X} {Y} (R ⨁ Q) (inj₂ q) .(inj₂ o′) refl | inj₁ o′ | Is is = ≈-⨁₂ (first-≈ Q q o′ is)
  first-≈ {X} {Y} (R ⨁ Q) (inj₂ q) o () | inj₂ o′ | Is is
  first-≈ {X} {Y} (R ⨂ Q) (r , q) o x with first {X} {Y} R r | inspect (first {X} {Y} R) r
  first-≈ {X} {Y} (R ⨂ Q) (r , q) o x | inj₁ r′ | Is is with first {X} {Y} Q q | inspect (first {X} {Y} Q) q
  first-≈ {X} {Y} (R ⨂ Q) (r , q) .(r′ , q′) refl | inj₁ r′ | Is is | inj₁ q′ | Is is′ = ≈-⨂ (first-≈ R r r′ is) (first-≈ Q q q′ is′)
  first-≈ {X} {Y} (R ⨂ Q) (r , q) o () | inj₁ o′ | Is is | inj₂ y | Is is′
  first-≈ {X} {Y} (R ⨂ Q) (r , q) o () | inj₂ y | Is is

  first-Fmap : ∀ {X Y : Set} (R : Reg)
               → (r : ⟦ R ⟧ X) → (r′ : ⟦ R ⟧ Y)
               → (ex : Y → X) → first R r ≡ inj₁ r′ → Fmap ex R r′ r 
  first-Fmap 0′ () r′ ex eq
  first-Fmap 1′ tt tt ex eq = Fmap-1′
  first-Fmap I r r′ ex ()
  first-Fmap (K A) r .r ex refl = Fmap-K
  first-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) r′ ex eq
    with first {X} {Y} R r | inspect (first {X} {Y} R) r
  first-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) .(inj₁ x) ex refl
    | inj₁ x | Is is = Fmap-⨁₁ (first-Fmap R r x ex is)
  first-Fmap {X} {Y} (R ⨁ Q) (inj₁ r) r′ ex () | inj₂ y | Is is
  first-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) r′ ex eq
    with first {X} {Y} Q q | inspect (first {X} {Y} Q) q
  first-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) .(inj₂ x) ex refl
    | inj₁ x | Is is = Fmap-⨁₂ (first-Fmap Q q x ex is)
  first-Fmap {X} {Y} (R ⨁ Q) (inj₂ q) r′ ex () | inj₂ y | Is is
  first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex x
    with first {X} {Y} R r | inspect (first {X} {Y} R) r 
  first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex x | inj₁ x₁ | Is is
    with first {X} {Y} Q q | inspect (first {X} {Y} Q) q
  first-Fmap {X} {Y} (R ⨂ Q) (r , q) .(r′ , q′) ex refl
    | inj₁ r′ | Is is | inj₁ q′ | Is is′ = Fmap-⨂ (first-Fmap R r r′ ex is) (first-Fmap Q q q′ ex is′)
  first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex () | inj₁ x₁ | Is is | inj₂ y | Is is′
  first-Fmap {X} {Y} (R ⨂ Q) (r , q) r′ ex () | inj₂ y | Is is

  first-Plug : ∀ {X Y : Set} (R : Reg)
             → (r : ⟦ R ⟧ X) → (dr : ∇ R Y X)
             → (y : X) → (ex : Y → X) → first R r ≡ inj₂ (dr , y) → Plug ex R dr y r
  first-Plug 0′ () dr y ex eq
  first-Plug 1′ r () y ex eq
  first-Plug I r tt .r ex refl = Plug-I
  first-Plug (K A) r () y ex eq
  first-Plug {Y = Y} (R ⨁ Q) (inj₁ r) dr y ex eq with first {Y = Y} R r | inspect (first {Y = Y} R) r
  first-Plug {Y = Y} (R ⨁ Q) (inj₁ r) dr y ex () | inj₁ x | Is is
  first-Plug {Y = Y} (R ⨁ Q) (inj₁ r) .(inj₁ dr′) .y′ ex refl
    | inj₂ (dr′ , y′) | Is is
    = Plug-⨁-inj₁ (first-Plug R r dr′ y′ ex is)
  first-Plug {Y = Y} (R ⨁ Q) (inj₂ q) dr y ex eq with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  first-Plug {Y = Y} (R ⨁ Q) (inj₂ q) dr y ex () | inj₁ x | Is is
  first-Plug {Y = Y} (R ⨁ Q) (inj₂ q) .(inj₂ dq) .y′ ex refl
    | inj₂ (dq , y′) | Is is
    = Plug-⨁-inj₂ (first-Plug Q q dq y′ ex is)
  first-Plug {Y = Y} (R ⨂ Q) (r , q) dr y ex eq with first {Y = Y} R r | inspect (first {Y = Y} R) r
  first-Plug {Y = Y} (R ⨂ Q) (r , q) dr y ex eq
    | inj₁ r′ | Is is with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  first-Plug {Y = Y} (R ⨂ Q) (r , q) dr y ex () | inj₁ r′ | Is is | inj₁ x | Is is′
  first-Plug {Y = Y} (R ⨂ Q) (r , q) .(inj₂ (r′ , dq′)) .y′ ex refl
    | inj₁ r′ | Is is | inj₂ (dq′ , y′) | Is is′
    = Plug-⨂-inj₂ (first-Fmap R r r′ ex is) (first-Plug Q q dq′ y′ ex is′)
  first-Plug {X} (R ⨂ Q) (r , q) .(inj₁ (dr′ , q)) .q′ ex refl
    | inj₂ (dr′ , q′) | Is is
    = Plug-⨂-inj₁ (first-Plug R r dr′ q′ ex is)

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
