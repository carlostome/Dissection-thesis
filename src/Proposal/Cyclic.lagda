\begin{code}
module Proposal.Cyclic where

  open import Data.Nat

  module Original where
    data Shape : Set where
      E : Shape
      P : Shape
      L : Shape
      B : Shape → Shape → Shape

    data Ctx : Set where
      ∎ : Ctx
      _,_ : Shape → Ctx → Ctx

    data Pos : Shape → Set where
      ε   : Pos L
      ε′  : ∀ {σ τ} → Pos (B σ τ)
      DnL : ∀ {σ τ} → Pos σ → Pos (B σ τ)
      DnR : ∀ {σ τ} → Pos τ → Pos (B σ τ)

    data Index : Shape → Ctx → Set where
      here  : ∀ {Γ τ}   → Index τ (τ , Γ)
      there : ∀ {Γ τ σ} → Index τ Γ → Index τ (σ , Γ)

    data PO : Ctx → Set where
      ↙_↑_ : ∀ {Γ τ} → Pos τ → Index τ Γ → PO Γ

    data T : Ctx → Shape → Set where
      ptr  : ∀ {Γ}     → PO Γ → T Γ P
      lf   : ∀ {Γ}     → ℕ    → T Γ L
      bin  : ∀ {Γ τ σ} → T (B E E , Γ) σ → T (B σ E , Γ) τ → T Γ (B σ τ)

    skeleton : ∀ Γ sh → T Γ sh → Shape
    skeleton Γ .P (ptr (↙ x ↑ x₁)) = P
    skeleton Γ .L (lf x) = L
    skeleton Γ .(B _ _) (bin x x₁) = B (skeleton (B E E , Γ) _ x) (skeleton (B _ E , Γ) _ x₁)

  module Mine where

    data Shape : Set where
      E : Shape
      P : Shape
      B : Shape → Shape → Shape

    data Pos : Shape → Set where
      ε   : Pos P
      ε′  : ∀ {σ τ} → Pos (B σ τ)
      DnL : ∀ {σ τ} → Pos σ → Pos (B σ τ)
      DnR : ∀ {σ τ} → Pos τ → Pos (B σ τ)

    data Ctx : Set where
      ∎   : Ctx
      _,_ : Shape → Ctx → Ctx

    data Index : Shape → Ctx → Set where
      here  : ∀ {Γ τ}   → Index τ (τ , Γ)
      there : ∀ {Γ τ σ} → Index τ Γ → Index τ (σ , Γ)
\end{code}
