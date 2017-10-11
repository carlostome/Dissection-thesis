\begin{code}
module Proposal.WellFounded.Indexed  where

  IxRel : (I : Set) → (I → Set) -> Set1
  IxRel I A = ∀ (i : I) → A i → A i → Set

  module WFIx {I : Set} {A : I → Set} ([_]_<_ : IxRel I A) where

    data AccIx (i : I) (x : A i) : Set where
      accIx : (∀ y → [ i ] y < x → AccIx i y) → AccIx i x

    Well-founded-Ix : Set
    Well-founded-Ix = ∀ i → ∀ x → AccIx i x

-- module Inverse-image-Well-founded { A B }
-- (_<_ : Rel B)(f : A → B) where
-- _⊰_ : Rel A
-- x ⊰ y = f x < f y

-- ii-acc : ∀ {x} → WF.Acc _<_ (f x) → WF.Acc _⊰_ x
-- ii-acc (WF.acc g) = WF.acc (λ y fy<fx → ii-acc (g (f y) fy<fx))

-- ii-wf : WF.Well-founded _<_ → WF.Well-founded _⊰_
-- ii-wf wf x = ii-acc (wf (f x))
\end{code}
