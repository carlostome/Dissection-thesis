\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module Proposal.WellFounded.Nat where

  open import Data.Nat
  open import Induction.WellFounded
  open import Relation.Binary.PropositionalEquality
  open import Data.Sum
  open import Data.Product
  open import Data.Empty
\end{code}

%<*Rel>
\begin{code}
  data _<₁_ (m : ℕ) : ℕ → Set where
    Base :                      m <₁ suc m
    Step : ∀ {n : ℕ} → m <₁ n → m <₁ suc n

  data _<₂_ : ℕ → ℕ → Set where
    Base : ∀ {n : ℕ}   → 0 <₂ suc n
    Step : ∀ {n m : ℕ} → n <₂ m      → suc n <₂ suc m
\end{code}
%</Rel>

%<*Proof-1>
\begin{code}
  <₁-WF : Well-founded _<₁_
  <₁-WF x = acc (aux x)
    where
      aux : ∀ x y → y <₁ x → Acc _<₁_ y
      aux .(suc y) y Base         = <₁-WF y
      aux .(suc n) y (Step {n} p) = aux n y p
\end{code}
%</Proof-1>

\begin{code}
  module Proof-2-incomplete where
\end{code}

%<*Incomplete>
\begin{code}
    <₂-WF : Well-founded _<₂_
    <₂-WF x = acc (aux x)
      where
        aux : (x y : ℕ) → y <₂ x → Acc _<₂_ y
        aux zero y ()
        aux (suc x) .0 Base                   = {!<₂-WF 0!}
        aux (suc x) .(suc y) (Step {n = y} p) = aux {!!} {!!} {!p!}
\end{code}
%</Incomplete>

%<*Lemma>
\begin{code}
  lemma : ∀ n m → n <₂ suc m → n ≡ m ⊎ n <₂ m
\end{code}
%</Lemma>

\begin{code}
  lemma .0 zero Base    = inj₁ refl
  lemma .0 (suc m) Base = inj₂ Base
  lemma .(suc n) zero (Step {n} {.0} ())
  lemma .(suc n) (suc m) (Step {n} {.(suc m)} x) with lemma _ _ x
  lemma .(suc m) (suc m) (Step {.m} {.(suc m)} x) | inj₁ refl = inj₁ refl
  lemma .(suc n) (suc m) (Step {n} {.(suc m)} x)  | inj₂ y = inj₂ (Step y)
\end{code}

%<*Proof-2>
\begin{code}
  <₂-WF : Well-founded _<₂_
  <₂-WF x = acc (aux x)
    where
      aux : (x y : ℕ) → y <₂ x → Acc _<₂_ y
      aux zero y ()
      aux (suc x) y p with lemma _ _ p
      aux (suc x) .x p | inj₁ refl = <₂-WF x
      aux (suc x) y p  | inj₂ i    = aux x y i
\end{code}
%</Proof-2>
