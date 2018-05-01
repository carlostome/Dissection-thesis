\begin{code}
module Other where

  open import Data.Nat
  
  data Bin : Set where
    Tip : ℕ → Bin
    Node : Bin → Bin → Bin

  data Strc : Bin → Bin → Set where
    Node-l : ∀ a b → Strc a (Node a b)
    Node-r : ∀ a b → Strc b (Node a b)
    
