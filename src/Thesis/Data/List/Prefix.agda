
module Thesis.Data.List.Prefix where

  open import Data.List
  open import Data.List.All as L
  open import Relation.Nullary 

  -- a view on list regarding a predicate P over elements.
  data Prefix {X : Set} (P : X → Set) : List X → Set where
    AllOf      : ∀ xs         → L.All P xs  → Prefix P xs
    OnlyPrefix : ∀ pre x post → L.All P pre → ¬ (P x) → Prefix P (pre ++ x ∷ post)

  -- Prefix covers any list given the predicate is decidable
  prefix : {X : Set} {P : X → Set} → (∀ (x : X) → Dec (P x)) → (xs : List X) → Prefix P xs
  prefix dec []                        = AllOf [] []
  prefix dec (x ∷ xs) with prefix dec xs
  prefix dec (x ∷ xs) | AllOf .xs all with dec x
  prefix dec (x ∷ xs) | AllOf .xs all | yes p = AllOf (x ∷ xs) (p ∷ all)
  prefix dec (x ∷ xs) | AllOf .xs all | no ¬p = OnlyPrefix [] x xs [] ¬p
  prefix dec (x ∷ .(pre ++ y ∷ post)) | OnlyPrefix pre y post all ¬py with dec x
  prefix dec (x ∷ .(pre ++ y ∷ post)) | OnlyPrefix pre y post all ¬py | yes p = OnlyPrefix (x ∷ pre) y post (p ∷ all) ¬py
  prefix dec (x ∷ .(pre ++ y ∷ post)) | OnlyPrefix pre y post all ¬py | no ¬p = OnlyPrefix [] x (pre ++ y ∷ post) [] ¬p

