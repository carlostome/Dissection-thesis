module Regular.First where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥; ⊥-elim)
  open import Relation.Binary.PropositionalEquality renaming ([_] to Is_)

  open import Regular.Core
  open import Regular.Equality
    renaming ( refl to ≈-refl
             ; sym  to ≈-sym )
  open import Regular.Dissection
    renaming ( Lt to Dissection-Lt
             ; IxLt to Dissection-IxLt
             ; Lt-to-IxLt to Dissection-Lt-to-IxLt
             ; IxLt-WF to Dissection-IxLt-WF
             ; proof-irrelevance to Plug-proof-irrelevance)
  open import Regular.NonRec
    renaming (proof-irrelevance to NonRec-proof-irrelevance)

  ------------------------------------------------------------------------------
  --                `first` function that finds the leftmost hole             --
  
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

  first-NonRec : {X Y : Set} (R : Reg)
               → (i : ⟦ R ⟧ X)
               → (o : ⟦ R ⟧ Y)
               → first R i ≡ inj₁ o → NonRec R i × NonRec R o
  first-NonRec 0′ () o x
  first-NonRec 1′ tt .tt refl = NonRec-1′ , NonRec-1′
  first-NonRec I i o ()
  first-NonRec (K A) i .i refl = NonRec-K A i , NonRec-K A i
  first-NonRec {Y = Y} (R ⨁ Q) (inj₁ r) o x
    with first {Y = Y} R r | inspect (first {Y = Y} R) r
  first-NonRec {Y = Y} (R ⨁ Q) (inj₁ r) .(inj₁ o′) refl
    | inj₁ o′ | Is is with first-NonRec R r o′ is
  ... | (nr-r , nr-o′) = NonRec-⨁-inj₁ R Q r nr-r , NonRec-⨁-inj₁ R Q o′ nr-o′
  first-NonRec {Y = Y} (R ⨁ Q) (inj₁ r) o () | inj₂ y | Is is
  first-NonRec {Y = Y} (R ⨁ Q) (inj₂ q) o x
    with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  first-NonRec {Y = Y} (R ⨁ Q) (inj₂ q) .(inj₂ o′) refl
    | inj₁ o′ | Is is with first-NonRec Q q o′ is
  ... | nr-q , nr-o = NonRec-⨁-inj₂ R Q q nr-q , NonRec-⨁-inj₂ R Q o′ nr-o
  first-NonRec {Y = Y} (R ⨁ Q) (inj₂ q) o () | inj₂ y | Is is
  first-NonRec {Y = Y} (R ⨂ Q) (r , q) o x
    with first {Y = Y} R r | inspect (first {Y = Y} R) r
  first-NonRec {Y = Y} (R ⨂ Q) (r , q) o x | inj₁ r′ | Is is
    with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  first-NonRec {Y = Y} (R ⨂ Q) (r , q) .(r′ , q′) refl | inj₁ r′ | Is is | inj₁ q′ | Is is′
    with first-NonRec R r r′ is | first-NonRec Q q q′ is′
  ... | nr-r , nr-r′ | nr-q , nr-q′ = NonRec-⨂ R Q r q nr-r nr-q , NonRec-⨂ R Q r′ q′ nr-r′ nr-q′
  first-NonRec {Y = Y} (R ⨂ Q) (r , q) o () | inj₁ r′ | Is is | inj₂ y | Is is′
  first-NonRec {Y = Y} (R ⨂ Q) (r , q) o () | inj₂ y | Is is
  
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

  ------------------------------------------------------------------------------
  --                Reification of `first` as a relation                      --
  
  data First {X Y : Set} : (R : Reg) → ⟦ R ⟧ X → ∇ R Y X × X → Set where
    First-⨁-inj₁ : ∀ {R Q} {r} {rx x} → First R r (rx , x) → First (R ⨁ Q) (inj₁ r) (inj₁ rx , x)
    First-⨁-inj₂ : ∀ {R Q} {q} {qx x} → First Q q (qx , x) → First (R ⨁ Q) (inj₂ q) (inj₂ qx , x)
    First-I       : ∀ {x} → First I x (tt , x)
    First-⨂₁     : ∀ {R Q} {rx x} {r q} → First R r (rx , x) → First (R ⨂ Q) (r , q) (inj₁ (rx , q) , x)
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

  ------------------------------------------------------------------------------
  --                Properties relating `first` and `First`                   --

  first-to-First : ∀ {X Y : Set} (R : Reg) (r : ⟦ R ⟧ X)
                 → (dr : ∇ R Y X) (x : X)
                 → first R r ≡ inj₂ (dr , x) → First R r (dr , x)
  first-to-First 0′ r () x feq
  first-to-First 1′ r () x feq
  first-to-First I r .tt .r refl = First-I
  first-to-First (K A) r () x feq
  first-to-First {Y = Y} (R ⨁ Q) (inj₁ r) dr x feq
    with first {Y = Y} R r | inspect (first {Y = Y} R) r
  first-to-First {Y = Y} (R ⨁ Q) (inj₁ r) dr x () | inj₁ _ | Is is
  first-to-First {Y = Y} (R ⨁ Q) (inj₁ r) .(inj₁ dr′) .x′ refl
    | inj₂ (dr′ , x′) | Is is = First-⨁-inj₁ (first-to-First R r dr′ x′ is)
  first-to-First {Y = Y} (R ⨁ Q) (inj₂ q) dr x feq
    with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  first-to-First {Y = Y} (R ⨁ Q) (inj₂ q) dr x () | inj₁ _ | Is is
  first-to-First {Y = Y} (R ⨁ Q) (inj₂ q) .(inj₂ dq′) .x′ refl
    | inj₂ (dq′ , x′) | Is is = First-⨁-inj₂ (first-to-First Q q dq′ x′ is)
  first-to-First {Y = Y} (R ⨂ Q) (r , q) dr x feq with first {Y = Y} R r | inspect (first {Y = Y} R) r
  first-to-First {Y = Y} (R ⨂ Q) (r , q) dr x feq | inj₁ x₁ | Is is with first {Y = Y} Q q | inspect (first {Y = Y} Q) q
  first-to-First {Y = Y} (R ⨂ Q) (r , q) dr x () | inj₁ x₁ | Is is | inj₁ x₂ | Is is′
  first-to-First {Y = Y} (R ⨂ Q) (r , q) .(inj₂ (r′ , dq)) .x′ refl | inj₁ r′ | Is is | inj₂ (dq , x′) | Is is′
    with first-NonRec R r r′ is
  ... | (nr-r , nr-r′) with coerce-≈ r nr-r r′ (first-≈ R r r′ is)
  first-to-First {Y = Y} (R ⨂ Q) (r , q) .(inj₂ (coerce r nr-r , dq)) .x′ refl
    | inj₁ .(coerce r nr-r) | Is is | inj₂ (dq , x′) | Is is′ | nr-r , nr-r′ | refl
    = First-⨂₂ nr-r (first-to-First {Y = Y} Q q dq x′ is′)
  first-to-First {Y = Y} (R ⨂ Q) (r , q) .(inj₁ (dr′ , q)) .x′ refl
    | inj₂ (dr′ , x′) | Is is = First-⨂₁ (first-to-First R r dr′ x′ is)

--  First-to-first = {!!}

  -- A First-cps dissection can be seen also as a restricted Plug
  First-to-Plug : ∀ {X Y : Set} {f : Y → X} {R : Reg} {r : ⟦ R ⟧ X} {dr : ∇ R Y X} {x : X} → First R r (dr , x) → Plug f R dr x r
  First-to-Plug (First-⨁-inj₁ x₁) = Plug-⨁-inj₁ (First-to-Plug x₁)
  First-to-Plug (First-⨁-inj₂ x₁) = Plug-⨁-inj₂ (First-to-Plug x₁)
  First-to-Plug First-I            = Plug-I
  First-to-Plug (First-⨂₁ x₁)     = Plug-⨂-inj₁ (First-to-Plug x₁)
  First-to-Plug (First-⨂₂ x₁ x₂)  = Plug-⨂-inj₂ (coerce-Fmap _ _ x₁) (First-to-Plug x₂)
