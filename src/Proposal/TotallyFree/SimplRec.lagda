\begin{code}
module Proposal.TotallyFree.SimplRec where

  data SimplRec (I : Set) (O : Set) : Set where
    return : O → SimplRec I O
    
\end{code}
