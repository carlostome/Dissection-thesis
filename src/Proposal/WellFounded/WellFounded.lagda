\begin{code}
module Proposal.WellFounded.WellFounded  where

  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Data.Empty

  ¬ : Set → Set
  ¬ A = A → ⊥

  Rel : Set -> Set1
  Rel A = A -> A -> Set
\end{code}

%<*Acc>
\begin{code}
  data Acc {A : Set} (_<_ : A → A → Set) (x : A) : Set where
    acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x
\end{code}
%</Acc>

%<*WF>
\begin{code}
  Well-founded : {A : Set} → (A → A → Set) → Set
  Well-founded _<_ = ∀ x → Acc _<_ x
\end{code}
%</WF>

%<*Elim>
\begin{code}
  wfr : ∀ {A : Set} {_<_ : A → A → Set}
          (P : A → Set) (a : A) → Acc _<_ a → (∀ x → (∀ y → y < x → P y) → P x) → P a
  wfr P a (acc x) e = e a λ y p → wfr P y (x y p) e
\end{code}
%</Elim>

  -- module Inverse-image-Well-founded { A B }
  --   (_<_ : Rel B)(f : A → B) where
  --   _⊰_ : Rel A
  --   x ⊰ y = f x < f y

  --   private
  --     ii-acc : ∀ {x} → WF.Acc _<_ (f x) → WF.Acc _⊰_ x
  --     ii-acc (WF.acc g) = WF.acc (λ y fy<fx → ii-acc (g (f y) fy<fx))

  --   ii-wf : WF.WellFounded _<_ → WF.WellFounded _⊰_
  --   ii-wf wf x = ii-acc (wf (f x))

  -- _/_ : (A : Set) → Rel A → Set₁
  -- A / R = (x : A) → (y : A) → R x y → Set

  -- module WFPar {A : Set} (R : Rel A) (_<_[_] : A / R) where
  --   data Acc (x : A) : Set where
  --     acc : (∀ y → (pr : R y x) → y < x [ pr ] → Acc y) → Acc x

  --   WellFounded : Set
  --   WellFounded = ∀ x → Acc x

\end{code}
