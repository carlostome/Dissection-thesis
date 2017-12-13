\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module Proposal.WellFounded.List where

  open import Data.Nat hiding (_<_)
  open import Induction.WellFounded
  open import Proposal.WellFounded.Nat
  open import Relation.Binary

  open import Data.Product using (_×_; _,_)
  open import Function using (_∘_; _on_)
  open import Data.Bool
  open import Data.List

  _<_ = _<₁_
  <-WF = <₁-WF

\end{code}

\begin{code}
  module QuickSort {A : Set} where
    open Inverse-image {A = List A} {B = ℕ} {_<_} length public
\end{code}

%<*relation>
\begin{code}
    _⊰_ : List A → List A → Set
    _⊰_ = _<_ on length
\end{code}
%</relation>

%<*lemma1>
\begin{code}
    prlt : ∀ (p : A → A → Bool) → (x : A)
         → (xs : List A) → (filter (p x) xs) ⊰ (x ∷ xs)
    prlt = ∙∙∙
\end{code}
%</lemma1>

\begin{code}
      where ∙∙∙ : ∀ (p : A → A → Bool) → (x : A) → (xs : List A) → (filter (p x) xs) ⊰ (x ∷ xs)
            ∙∙∙ = {!!}
\end{code}

%<*lemma2>
\begin{code}
    prgt : ∀ (p : A → A → Bool) → (x : A) → (xs : List A)
         → (filter (not ∘ p x) xs) ⊰ (x ∷ xs)
    prgt = ∙∙∙
\end{code}
%</lemma2>

\begin{code}
      where ∙∙∙ : ∀ (p : A → A → Bool) → (x : A) → (xs : List A) → (filter (not ∘ p x) xs) ⊰ (x ∷ xs)
            ∙∙∙ = {!!}

\end{code}

%<*WF>
\begin{code}
    ⊰-WF : Well-founded _⊰_
    ⊰-WF = well-founded <-WF
\end{code}
%</WF>

%<*QS>
\begin{code}
    quickSort : (A → A → Bool) → List A → List A
    quickSort p xs = qs xs (⊰-WF xs)
      where
        qs : ∀ (x : List A) → Acc _⊰_ x → List A
        qs [] _              = []
        qs (x ∷ xs) (acc rs) =
          qs (filter (p x) xs) (rs _ (prlt p x xs))
            ++ [ x ] ++
          qs (filter (not ∘ p x) xs)  (rs _ (prgt p x xs))
\end{code}
%</QS>

--   map : ∀ {i : Size} {A B : Set} → (A → B) → List A {i} → List B {i}
--   map f Nil       =  Nil
--   map f (Cons x xs) =  Cons (f x) (map f xs)

--   _++_ : ∀ {i j : Size} {A : Set} → List A {i} → List A {j} → List A {ω}
--   Nil ++ ys       = ys
--   Cons x xs ++ ys = Cons x (xs ++ ys)

--   infixl 40 _++_

--   [_] : ∀ {i : Size} {A : Set} → A → List A {↑ (↑ i)}
--   [ x ] = Cons x Nil

--   module MergeSort where

--     split : ∀ {i : Size} {A : Set} → List A {i} → List A {i} × List A {i}
--     split Nil         = Nil , Nil
--     split (Cons x Nil) = (Cons x Nil) , Nil
--     split (Cons x (Cons y xs)) with split xs
--     ... | (xss , yss) = Cons x xss , Cons y yss

--     merge : ∀ {i : Size} {A : Set} → (leq : A → A → Bool) → List A {i} → List A {i} → List A {ω}
--     merge {.(↑ _)} leq Nil ys          = ys
--     merge {.(↑ _)} leq (Cons x xs) Nil = Cons x xs
--     merge {.(↑ _)} leq (Cons x xs) (Cons y ys) with leq x y
--     ... | true  = Cons x (merge leq xs (Cons y ys))
--     ... | false = Cons y (merge leq (Cons x xs) ys)

--     mergeSort : ∀ {i : Size} {A : Set} → (leq : A → A → Bool) → List A {i} → List A {ω}
--     mergeSort {.(↑ _)} leq Nil               = Nil
--     mergeSort {.(↑ (↑ _))} leq (Cons x Nil)  = Cons x Nil
--     mergeSort {.(↑ (↑ _))} leq (Cons {.(↑ i)} x (Cons {i} y xs)) with split {i} xs
--     ... | xss , yss = merge {ω} leq (mergeSort {↑ i} leq (Cons x xss))
--                                     (mergeSort {↑ i} leq (Cons y yss))

--   module QuickSort-Filter where

--     filter : ∀ {i : Size} {A : Set} → (A → Bool) → List A {i} → List A {i}
--     filter p Nil = Nil
--     filter p (Cons x xs) = if p x then Cons x (filter p xs) else filter p xs

--     quickSort : ∀ {i : Size} {A : Set} → (A → A → Bool) → List A {i} → List A {ω}
--     quickSort {.(↑ i)} p (Nil {i})       = Nil
--     quickSort {.(↑ i)} p (Cons {i} x xs) =
--       quickSort {i} p (filter {i} (p x) xs) ++ [ x ] ++ quickSort {i} p (filter {i} (not ∘ p x) xs)


--   module QuickSort-Partition where

--     partition : ∀ {i : Size} {A : Set} → (A → Bool) → List A {i} → List A {i} × List A {i}
--     partition p Nil         = Nil , Nil
--     partition p (Cons x xs) with partition p xs | p x
--     ... | (xss , yss) | true  = Cons x xss , yss
--     ... | (xss , yss) | false = xss , (Cons x yss)

--     quickSort : ∀ {i : Size} {A : Set} → (A → A → Bool) → List A {i} → List A {ω}
--     quickSort p Nil         = Nil
--     quickSort p (Cons x xs) with partition (p x) xs
--     quickSort p (Cons x xs) | xss , yss = quickSort p xss ++ Cons x (quickSort p yss)
-- \end{code}
