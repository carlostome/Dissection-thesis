\begin{code}
module Proposal.Expr where

  open import Data.Nat using (ℕ ; zero; suc; _+_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  data Expr : Set where
    Val : ℕ -> Expr
    Add : Expr -> Expr -> Expr

  eval : Expr -> ℕ
  eval (Val x) = x
  eval (Add l r) = eval l + eval r

  data Stack : Set where
    Nil   : Stack
    Left  : Expr -> Stack -> Stack
    Right : ℕ -> Stack -> Stack

  -- From Danvy
  module Refunctionalized where

    data Decomposition : Set where
      Dec : ℕ → ℕ → Stack → Decomposition

    decompose-term : Expr → Stack → (ℕ → ℕ ⊎ Decomposition) → ℕ ⊎ Decomposition
    decompose-term (Val x) stk k    = k x
    decompose-term (Add l r) stk k = decompose-term l (Left r stk)   λ v₁ →
                                      decompose-term r (Right v₁ stk) λ v₂ → inj₂ (Dec v₁ v₂ stk)

  module Raw-load/unload where
    {-# TERMINATING #-}
    mutual
      load : Expr -> Stack -> ℕ
      load (Val x)   stack = unload x stack
      load (Add l r) stack = load l ( Left r stack )

      unload : ℕ -> Stack -> ℕ
      unload v Nil = v
      unload v (Right v' stack) = unload (v + v') stack
      unload v (Left r stack)   = load r (Right v stack)

  module One-Function where
    {-# TERMINATING #-}
    load/unload : Expr ⊎ ℕ → Stack → ℕ
    -- load
    load/unload (inj₁ (Val x)) stk   = load/unload (inj₂ x) stk
    load/unload (inj₁ (Add l r)) stk = load/unload (inj₁ l) (Left r stk)
    -- unload                                                ^^^^^^^^^^
    load/unload (inj₂ v) Nil            = v
    load/unload (inj₂ v) (Left r stk)   = load/unload (inj₁ r) (Right v stk)
    --                                                          ^^^^^^^^^^^
    load/unload (inj₂ v) (Right v' stk) = load/unload (inj₂ (v + v')) stk
\end{code}
