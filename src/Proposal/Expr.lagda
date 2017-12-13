\begin{code}
module Proposal.Expr where

  open import Data.Nat using (ℕ ; zero; suc; _+_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
\end{code}

%<*Expr>
\begin{code}
  data Expr : Set where
    Val : ℕ -> Expr
    Add : Expr -> Expr -> Expr
\end{code}
%</Expr>

%<*Eval>
\begin{code}
  eval : Expr -> ℕ
  eval (Val x) = x
  eval (Add l r) = eval l + eval r
\end{code}
%</Eval>

%<*Stack>
\begin{code}
  data Stack : Set where
    Top   : Stack
    Left  : Expr -> Stack -> Stack
    Right : ℕ -> Stack -> Stack
\end{code}
%</Stack>

\begin{code}
  {-# TERMINATING #-}
\end{code}

%<*load-unload>
\begin{code}
  mutual
    load : Expr -> Stack -> ℕ
    load (Val x)   stack = unload x stack
    load (Add l r) stack = load l ( Left r stack )

    unload : ℕ -> Stack -> ℕ
    unload v Top = v
    unload v (Right v' stack)  = unload (v + v') stack
    unload v (Left r stack)    = load r (Right v stack)

  eval-tr : Expr → ℕ
  eval-tr e = load e Top
\end{code}
%</load-unload>
