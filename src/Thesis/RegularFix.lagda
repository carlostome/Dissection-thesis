\begin{code}
module RegularFix where

  open import Data.Unit
  open import Data.Empty
  open import Data.Product
  open import Data.Sum
  open import Data.List
  open import Data.Nat
  
  data Reg : Set where
    0′    : Reg
    1′    : Reg
    V     : Reg
    _⨁_  : (r₁ r₂ : Reg) → Reg
    _⨂_  : (r₁ r₂ : Reg) → Reg
    Fix   : Reg → Reg

  mutual

    data μ (R : Reg) (X : Set) : Set where
      In : ⟦ R ⟧ (μ R X) → μ R X

    ⟦_⟧ : Reg → Set → Set
    ⟦ 0′ ⟧ X  = ⊥
    ⟦ 1′ ⟧ X  = ⊤
    ⟦ V ⟧  X  = X
    ⟦ F ⨁ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
    ⟦ F ⨂ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X
   
  ′NatF′ : Reg
  ′NatF′ = 1′ ⨁ V

  ′Nat′ = Fix ′NatF′

  -- from : ∀ {X} → ℕ → ⟦ ′Nat′ ⟧ X
  -- from zero    = inj₁ tt
  -- from (suc x) = inj₂ (In (from x))

  -- to : ∀ {X} → ⟦ ′Nat′ ⟧ X → ℕ
  -- to (inj₁ tt) = zero
  -- to (inj₂ (In x)) = suc (to x)

  mutual
    Ctx : ∀ (R : Reg) → (Set → Set)
    Ctx 0′ X = ⊥
    Ctx 1′ X = ⊥
    Ctx V X  = ⊤
    Ctx (R ⨁ Q) X = Ctx R X ⊎ Ctx Q X
    Ctx (R ⨂ Q) X = Ctx R X × ⟦ Q ⟧ X ⊎ ⟦ R ⟧ X × Ctx Q X
    Ctx (Fix R) X  = Ctx R (μ R X) × Ctxs X R

    data Ctxs (X : Set) (R : Reg) : Set where
      empty : Ctxs X R
      push  : Ctx R (μ R X) → Ctxs X R → Ctxs X R

  data W (S : Set) (P : S → Set) : Set where
    sup : (s : S) → (f : P s → W S P) → W S P

  data Bool : Set where
    true false : Bool

  data So : Bool → Set where
    oh : So true

  data IsInj₁ {A B : Set} : A ⊎ B → Set where
    Isinj₁ : ∀ x → IsInj₁ (inj₁ x)

  notIsInj₁ : ∀ {A B : Set} {X : Set} {x : B} → IsInj₁ {A} {B} (inj₂ x) → X
  notIsInj₁ ()

  notSo : (X : Set) → So false → X
  notSo X ()

  wNat = W Bool So

  wZero : wNat
  wZero = sup false (notSo (W Bool So))

  wSuc : wNat → wNat
  wSuc x = sup true λ {oh → x}


  wBTree : Set → Set → Set
  wBTree L N = W (N ⊎ L) IsInj₁

  wBLeaf : ∀ {L N : Set} → L → wBTree L N
  wBLeaf x = sup (inj₂ x) notIsInj₁

  wBNode : ∀ {L N : Set} → wBTree L N → N → wBTree L N → wBTree L N
  wBNode l n r = sup (inj₁ n) λ { (Isinj₁ _) → {!!}}

  plug : {X : Set} → (R : Reg) → Ctx R X → X → ⟦ R ⟧ X
  plug {X} 0′ () x
  plug {X} 1′ () x
  plug {X} V tt x = x
  plug {X} (R ⨁ Q) (inj₁ c) x = inj₁ (plug R c x)
  plug {X} (R ⨁ Q) (inj₂ c) x = inj₂ (plug Q c x)
  plug {X} (R ⨂ Q) (inj₁ (proj₃ , proj₄)) x = plug R proj₃ x , proj₄
  plug {X} (R ⨂ Q) (inj₂ (proj₃ , proj₄)) x = proj₃ , plug Q proj₄ x
  plug {X} (Fix R) (c , cs) x = unw cs ?
    where
      unw : Ctxs X R → ⟦ Fix R ⟧ X → ⟦ Fix R ⟧ X
      unw empty x = x
      unw (push c cs) x = unw cs {!!}

  -- first :: ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ X → (List (⟦ \
  -- mutual
  --   first-μ : ∀ {X : Set} → (R : Reg) → μ R → List (⟦ ∇ R ⟧₂ X (μ R)) → (List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X)
  --   first-μ {X} R (In x) xs = first-cp R x {!cont-first R xs!} 

  --   cont-first : ∀ {X : Set} (R : Reg) → List (⟦ ∇ R ⟧₂ X (μ R)) → ⟦ R ⟧ X ⊎ (⟦ ∇ R ⟧₂ X (μ R) × μ R) → List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X
  --   cont-first R xs (inj₁ x)       = xs , x
  --   cont-first R xs (inj₂ (y , x)) = first-μ R x (y ∷ xs)
    
  --   first-cp : ∀ {X : Set} → (R : Reg) → ⟦ R ⟧ (μ R) → (⟦ R ⟧ X ⊎ (⟦ ∇ R ⟧₂ X (μ R) × μ R) → List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X) → List (⟦ ∇ R ⟧₂ X (μ R)) × ⟦ R ⟧ X 
  --   first-cp R x₁ x₂ = {!!}

\end{code}
