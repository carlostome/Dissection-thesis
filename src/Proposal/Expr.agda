module Proposal.Expr where

  open import Data.Nat using (ℕ ; zero; suc; _+_)

  module Naive where
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

    {-# TERMINATING #-}
    mutual
      load : Expr -> Stack -> ℕ
      load (Val x)   stack = unload x stack
      load (Add l r) stack = load l ( Left r stack )

      unload : ℕ -> Stack -> ℕ
      unload v Nil = v
      unload v (Right v' stack) = unload (v + v') stack
      unload v (Left r stack)   = load r (Right v stack)
