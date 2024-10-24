
module Regular.NonRec where
  
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty
  open import Relation.Binary.PropositionalEquality
    renaming (refl to ≡-refl; proof-irrelevance to ≡-proof-irrelevance)
  open import Relation.Nullary
  open import Regular.Core

  open import Regular.Equality
    renaming (refl to ≈-refl; proof-irrelevance to ≈-proof-irrelevance)

  -- A predicate over values of regular functors to determine
  -- whether they mention recursive positions.
  data NonRec {X : Set} : (R : Reg) → ⟦ R ⟧ X → Set where
    NonRec-1′ : NonRec 1′ tt
    NonRec-K  : (B : Set) → (b : B) → NonRec (K B) b
    NonRec-⨁-inj₁ : (R Q : Reg) → (r : ⟦ R ⟧ X) → NonRec R r → NonRec (R ⨁ Q) (inj₁ r)
    NonRec-⨁-inj₂ : (R Q : Reg) → (q : ⟦ Q ⟧ X) → NonRec Q q → NonRec (R ⨁ Q) (inj₂ q)
    NonRec-⨂      : (R Q : Reg) → (r : ⟦ R ⟧ X) → (q : ⟦ Q ⟧ X) → NonRec R r → NonRec Q q → NonRec (R ⨂ Q) (r , q)

  -- NonRec is decidable
  NonRec-Dec : ∀ {X : Set} (R : Reg) (x : ⟦ R ⟧ X) → Dec (NonRec R x)
  NonRec-Dec 0′ ()
  NonRec-Dec 1′ tt = yes NonRec-1′
  NonRec-Dec I x = no (λ ())
  NonRec-Dec (K A) x = yes (NonRec-K A x)
  NonRec-Dec (R ⨁ Q) (inj₁ x) with NonRec-Dec R x
  NonRec-Dec (R ⨁ Q) (inj₁ x) | yes p = yes (NonRec-⨁-inj₁ R Q x p)
  NonRec-Dec (R ⨁ Q) (inj₁ x) | no ¬p = no λ { (NonRec-⨁-inj₁ _ _ _ x) → ¬p x}
  NonRec-Dec (R ⨁ Q) (inj₂ y) with NonRec-Dec Q y
  NonRec-Dec (R ⨁ Q) (inj₂ y) | yes p = yes (NonRec-⨁-inj₂ R Q y p)
  NonRec-Dec (R ⨁ Q) (inj₂ y) | no ¬p = no λ { (NonRec-⨁-inj₂ _ _ _ x) → ¬p x}
  NonRec-Dec (R ⨂ Q) (x , y) with NonRec-Dec R x | NonRec-Dec Q y
  NonRec-Dec (R ⨂ Q) (x , y) | yes p | yes p₁ = yes (NonRec-⨂ R Q x y p p₁)
  NonRec-Dec (R ⨂ Q) (x , y) | yes p | no ¬p  = no λ { (NonRec-⨂ _ _ _ _ _ z) → ¬p z }
  NonRec-Dec (R ⨂ Q) (x , y) | no ¬p | yes p  = no λ { (NonRec-⨂ _ _ _ _ z _) → ¬p z }
  NonRec-Dec (R ⨂ Q) (x , y) | no ¬p | no ¬p₁ = no λ { (NonRec-⨂ _ _ _ _ z _) → ¬p z }
  
  ≈-NonRec : ∀ {X : Set} {R : Reg} → (x : ⟦ R ⟧ X) → (nr-x : NonRec R x) → ∀ {Y : Set} → (y : ⟦ R ⟧ Y) → [ R ]-[ X ] x ≈[ Y ] y → NonRec R y
  ≈-NonRec .tt nr-x .tt ≈-1′ = NonRec-1′
  ≈-NonRec x nr-x .x ≈-K = NonRec-K _ x
  ≈-NonRec x nr-x .x ≈-I = nr-x
  ≈-NonRec .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr-x) .(inj₁ _) (≈-⨁₁ x₁) = NonRec-⨁-inj₁ R Q _ (≈-NonRec r nr-x _ x₁)
  ≈-NonRec .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr-x) .(inj₂ _) (≈-⨁₂ x₁) = NonRec-⨁-inj₂ R Q _ (≈-NonRec q nr-x _ x₁)
  ≈-NonRec .(r , q) (NonRec-⨂ R Q r q nr-x nr-x₁) .(_ , _) (≈-⨂ x₁ x₂) = NonRec-⨂ R Q _ _ (≈-NonRec r nr-x _ x₁)
                                                                                            (≈-NonRec q nr-x₁ _ x₂)
  coerce : ∀ {X : Set} {R : Reg} → (x : ⟦ R ⟧ X) → NonRec R x
         → ∀ {Y : Set} → ⟦ R ⟧ Y
  coerce .tt NonRec-1′ {Y}     = tt
  coerce x (NonRec-K B .x) {Y} = x
  coerce .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr) {Y} = inj₁ (coerce r nr)
  coerce .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr) {Y} = inj₂ (coerce q nr)
  coerce .(r , q) (NonRec-⨂ R Q r q nr nr₁) {Y} = coerce r nr , coerce q nr₁

  coerce-NonRec : ∀ {X : Set} {R : Reg} (x : ⟦ R ⟧ X) → (nr : NonRec R x)
                → ∀ {Y : Set} → NonRec {Y} R (coerce x nr)
  coerce-NonRec .tt NonRec-1′ = NonRec-1′
  coerce-NonRec x (NonRec-K B .x) = NonRec-K B x
  coerce-NonRec .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr) = NonRec-⨁-inj₁ R Q (coerce r nr) (coerce-NonRec r nr)
  coerce-NonRec .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr) = NonRec-⨁-inj₂ R Q (coerce q nr) (coerce-NonRec q nr)
  coerce-NonRec .(r , q) (NonRec-⨂ R Q r q nr nr₁) = NonRec-⨂ R Q (coerce r nr) (coerce q nr₁) (coerce-NonRec r nr) (coerce-NonRec q nr₁)

  coerce-≈ : ∀ {X : Set} {R : Reg} (x : ⟦ R ⟧ X) → (nr : NonRec R x)
           → ∀ {Y : Set} → (y : ⟦ R ⟧ Y) → [ R ]-[ X ] x ≈[ Y ] y → coerce x nr ≡ y
  coerce-≈ .tt NonRec-1′ .tt ≈-1′   = ≡-refl
  coerce-≈ x (NonRec-K B .x) .x ≈-K = ≡-refl
  coerce-≈ .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr) .(inj₁ _) (≈-⨁₁ eq)   = cong inj₁ (coerce-≈ r nr _ eq)
  coerce-≈ .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr) .(inj₂ _) (≈-⨁₂ eq)   = cong inj₂ (coerce-≈ q nr _ eq)
  coerce-≈ .(r , q) (NonRec-⨂ R Q r q nr nr₁) (_ , _) (≈-⨂ eq₁ eq₂) = cong₂ _,_ (coerce-≈ r nr _ eq₁) (coerce-≈ q nr₁ _ eq₂)

  coerce-≈-2 : ∀ {R : Reg}
             → ∀ {X : Set} → (x : ⟦ R ⟧ X) → (nr-x : NonRec R x)
             → ∀ {Y : Set} → (y : ⟦ R ⟧ Y) → (nr-y : NonRec R y)
             → [ R ]-[ X ] x ≈[ Y ] y → ∀ {Z : Set} → (coerce x nr-x {Z}) ≡ (coerce y nr-y {Z})
  coerce-≈-2 .tt NonRec-1′ .tt NonRec-1′ ≈-1′ = ≡-refl
  coerce-≈-2 .y (NonRec-K B .y) y (NonRec-K .B .y) ≈-K = ≡-refl
  coerce-≈-2 .(inj₁ r) (NonRec-⨁-inj₁ R Q r nr-x) .(inj₁ r₁) (NonRec-⨁-inj₁ .R .Q r₁ nr-y) (≈-⨁₁ x₁) = cong inj₁ (coerce-≈-2 r nr-x r₁ nr-y x₁)
  coerce-≈-2 .(inj₂ q) (NonRec-⨁-inj₂ R Q q nr-x) .(inj₂ q₁) (NonRec-⨁-inj₂ .R .Q q₁ nr-y) (≈-⨁₂ x₁) = cong inj₂ (coerce-≈-2 q nr-x q₁ nr-y x₁)
  coerce-≈-2 .(r , q) (NonRec-⨂ R Q r q nr-x nr-x₁) (_ , _) (NonRec-⨂ .R .Q _ _ nr-y nr-y₁) (≈-⨂ x₁ x₂) = cong₂ _,_ (coerce-≈-2 r nr-x _ nr-y x₁)
                                                                                                                      (coerce-≈-2 q nr-x₁ _ nr-y₁ x₂)
  proof-irrelevance : ∀ {X : Set} {R : Reg} {x : ⟦ R ⟧ X} → (a : NonRec R x) → (b : NonRec R x) → a ≡ b
  proof-irrelevance NonRec-1′ NonRec-1′ = ≡-refl
  proof-irrelevance (NonRec-K B b₁) (NonRec-K .B .b₁) = ≡-refl
  proof-irrelevance (NonRec-⨁-inj₁ R Q r a) (NonRec-⨁-inj₁ .R .Q .r b)  = cong (NonRec-⨁-inj₁ R Q r) (proof-irrelevance a b)
  proof-irrelevance (NonRec-⨁-inj₂ R Q q a) (NonRec-⨁-inj₂ .R .Q .q b)  = cong (NonRec-⨁-inj₂ R Q q) (proof-irrelevance a b)
  proof-irrelevance (NonRec-⨂ R Q r q a a₁) (NonRec-⨂ .R .Q .r .q b b₁) = cong₂ (NonRec-⨂ R Q r q) (proof-irrelevance a b)
                                                                                                     (proof-irrelevance a₁ b₁)
  coerce-Fmap : ∀ {X Y : Set} {f : X → Y} (R : Reg) (r : ⟦ R ⟧ Y) (isl : NonRec R r) → Fmap f R (coerce r isl) r
  coerce-Fmap .1′ .tt NonRec-1′ = Fmap-1′
  coerce-Fmap .(K B) r (NonRec-K B .r) = Fmap-K
  coerce-Fmap .(R ⨁ Q) .(inj₁ r) (NonRec-⨁-inj₁ R Q r isl)  = Fmap-⨁₁ (coerce-Fmap R r isl)
  coerce-Fmap .(R ⨁ Q) .(inj₂ q) (NonRec-⨁-inj₂ R Q q isl)  = Fmap-⨁₂ (coerce-Fmap Q q isl)
  coerce-Fmap .(R ⨂ Q) .(r , q) (NonRec-⨂ R Q r q isl isl₁) = Fmap-⨂ (coerce-Fmap R r isl) (coerce-Fmap Q q isl₁)

