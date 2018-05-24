module Thesis.Example.Tree where

  open import Data.Nat
  open import Data.List
  open import Data.Sum
  open import Data.Product
  open import Thesis.Regular.Core
  open import Thesis.Regular

  -- pattern functor for binary trees
  BinF : Reg
  BinF = (K ℕ) ⨁ (I ⨂ (K ℕ) ⨂ I)

  -- fixpoint of pattern functor
  Bin : Set
  Bin = μ BinF

  pattern Tip n      = In (inj₁ n)
  pattern Node l n r = In (inj₂ (l , n , r))

  tree₁ : Bin
  tree₁ = Node (Node (Node (Tip 1) 2 (Tip 3)) 4 (Tip 5)) 6 (Tip 7)

  sumTree : Bin → ℕ
  sumTree = tail-rec-cata BinF sumAlg
    where
      sumAlg : ⟦ BinF ⟧ ℕ → ℕ
      sumAlg (inj₁ x)           = x
      sumAlg (inj₂ (l , n , r)) = l + n + r


  inorder : Bin → List ℕ
  inorder = tail-rec-cata BinF inOrderAlg
    where
      inOrderAlg : ⟦ BinF ⟧ (List ℕ) → List ℕ
      inOrderAlg (inj₁ x)           = [ x ]
      inOrderAlg (inj₂ (l , n , r)) = l ++ [ n ] ++ r
 
