\begin{code}
module Proposal.QuickSort where 
  open import Data.List
  open import Function
  open import Data.Bool

  {-# TERMINATING #-}
\end{code}

%<*QS>
\begin{code}
  quickSort : ∀ {A : Set} → (A → A → Bool) → List A → List A
  quickSort p [] = []
  quickSort p (x ∷ xs) = quickSort p (filter (p x) xs)
                           ++ [ x ] ++
                         quickSort p (filter (not ∘ (p x)) xs)
\end{code}
%</QS>

