\begin{code}
module RegularFix where

  open import Data.Nat 
  open import Data.Bool
  open import Data.Fin
  open import Data.Unit
  open import Data.Empty
  open import Data.List
  open import Data.Sum
  open import Data.Product
  open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  open import Data.Maybe

  module SimpleRec where
    data Rec : Set where
      rec norec : Rec
    
    data R : Rec → Set where
      0′   : ∀ {b} → R b
      1′   : ∀ {b} → R b
      _⨁_ : ∀ {b} → R b → R b → R b
      _⨂_ : ∀ {b} → R b → R b → R b

      var  : R norec
      Fix  : R norec → R rec

    mutual
      intNoRec : R norec → (Set → Set)
      intNoRec 0′ X = ⊥
      intNoRec 1′ X = ⊤
      intNoRec (R ⨁ Q) X = intNoRec R X ⊎ intNoRec Q X
      intNoRec (R ⨂ Q) X = intNoRec R X × intNoRec Q X
      intNoRec var X      = X

      intRec : R rec → Set
      intRec 0′ = ⊥
      intRec 1′ = ⊤
      intRec (R ⨁ Q) = (intRec R) ⊎ (intRec Q)
      intRec (R ⨂ Q) = (intRec R) × (intRec Q)
      intRec (Fix R)  = mu R

      data mu (r : R norec) : Set where
        In : intNoRec r (mu r) → mu r

    Natty : R rec
    Natty = Fix (1′ ⨁ var)

    ze : intRec Natty
    ze = In (inj₁ tt)

    su : intRec Natty → intRec Natty
    su x = In (inj₂ x)

    mutual
      CtxRec : (r : R rec) → Set
      CtxRec 0′ = ⊥
      CtxRec 1′ = ⊥
      CtxRec (R ⨁ Q) = CtxRec R ⊎ CtxRec Q
      CtxRec (R ⨂ Q) = CtxRec R × intRec Q ⊎ intRec R × (CtxRec Q)
      CtxRec (Fix x)  = List (CtxNoRec x (mu x))

      CtxNoRec : R norec → (Set → Set)
      CtxNoRec 0′ X = ⊥
      CtxNoRec 1′ X = ⊥
      CtxNoRec (R ⨁ Q) X = (CtxNoRec R) X ⊎ (CtxNoRec Q) X
      CtxNoRec (R ⨂ Q) X = (CtxNoRec R X × intNoRec Q X) ⊎ (intNoRec R X) × CtxNoRec Q X
      CtxNoRec var      X = ⊤

    BinR = Fix (1′ ⨁ (var ⨂ var))
    BinT = intRec BinR
    leaf : BinT
    leaf = In (inj₁ tt)

    node : BinT → BinT → BinT
    node l r = In (inj₂ (l , r))

    p = CtxRec BinR

    mutual
      firstNoRec : ∀ {X : Set} {Result : Set} → (r : R norec) → intNoRec r X → (X → CtxNoRec r X → Maybe Result) → Maybe Result
      firstNoRec 0′ () k
      firstNoRec 1′ tt k = nothing
      firstNoRec (R ⨁ Q) (inj₁ x) k = firstNoRec R x (λ x i → k x (inj₁ i))
      firstNoRec (R ⨁ Q) (inj₂ y) k = {!!}
      firstNoRec (R ⨂ Q) (r , q) k  = {!!}
      firstNoRec var x k             = k x tt

      firstRec : ∀ {Result : Set} → (r : R rec) → intRec r → Maybe Result
      firstRec 0′ ()
      firstRec 1′ tt = nothing
      firstRec (R ⨁ Q) x = {!!}
      firstRec (R ⨂ Q) x = {!!}
      firstRec {Result} (Fix R) x = fstFix x []
        where
          fstFix : mu R → List (CtxNoRec R (mu R)) → Maybe Result 
          fstFix (In x) cs = firstNoRec R x (λ x c → fstFix {!x!} {!!})
  module RegFix where
    data Reg : ℕ → Set where   
      0′   : ∀ {n} → Reg n
      1′   : ∀ {n} → Reg n
      _⨁_ : ∀ {n} → Reg n → Reg n → Reg n
      _⨂_ : ∀ {n} → Reg n → Reg n → Reg n

      var : ∀ {n} → Fin n → Reg n
      Fix : ∀ {n} → Reg (suc n) → Reg n
    
    data Tel : ℕ → Set where
      ε   : Tel 0
      _,_ : ∀ {n} → (Γ : Tel n) → (ρ : Reg n) → Tel (suc n)  

    mutual  
      find : ∀ {n} → Tel n → Fin n → Set
      find (Γ , ρ) zero    = ⟦ ρ ⟧ Γ
      find (Γ , _) (suc n) = find Γ n

      data μ {n : ℕ} (Γ : Tel n) (ρ : Reg (suc n)) : Set where
        ⟨_⟩ : ⟦ ρ ⟧ (Γ , Fix ρ) → μ Γ ρ

      ⟦_⟧_ : ∀ {n : ℕ} → Reg n → Tel n → Set
      ⟦ 0′ ⟧ Γ = ⊥
      ⟦ 1′ ⟧ Γ = ⊤
      ⟦ F ⨁ G ⟧ Γ = (⟦ F ⟧ Γ) ⊎ (⟦ G ⟧ Γ)
      ⟦ F ⨂ G ⟧ Γ = (⟦ F ⟧ Γ) × (⟦ G ⟧ Γ)
      ⟦ var x ⟧ Γ = find Γ x
      ⟦ Fix F ⟧ Γ = μ Γ F

    Nat : ∀ {n} → Reg n
    Nat = Fix (1′ ⨁ var zero)

    ze : ∀ {n} {Γ : Tel n} → ⟦ Nat ⟧ Γ
    ze =  ⟨ (inj₁ tt) ⟩
  
    su : ∀ {n} {Γ : Tel n} → ⟦ Nat ⟧ Γ → ⟦ Nat ⟧ Γ
    su x = ⟨ inj₂ x ⟩

    mutual
      Ctx : ∀ {n} → Tel n → Fin n → Reg n → Set
      Ctx Γ n 0′ = ⊥
      Ctx Γ n 1′ = ⊥
      Ctx Γ n (ρ ⨁ σ) = Ctx Γ n ρ ⊎ Ctx Γ n σ
      Ctx Γ n (ρ ⨂ σ) = Ctx Γ n ρ × (⟦ σ ⟧ Γ) ⊎ (⟦ ρ ⟧ Γ) × Ctx Γ n σ
      Ctx Γ n (var x)  = x ≡ n
      Ctx Γ n (Fix ρ)  = Ctx (Γ , Fix ρ) (inject₁ n) ρ × Ctxs Γ ρ

      data Ctxs {n : ℕ} (Γ : Tel n) (ρ : Reg (suc n)) : Set where
        empty : Ctxs Γ ρ
        push  : Ctx (Γ , Fix ρ) zero ρ → Ctxs Γ ρ → Ctxs Γ ρ

  -- plug : ∀ {n} → (R : Reg n) (Γ : Tel n) → ⟦ Reg  

    p : Set
    p = Ctx (ε , 1′) zero (Fix ((var (suc zero) ⨂ var zero)))

    q : p
    q = {!!} , push (inj₂ (tt , refl)) empty
\end{code}
