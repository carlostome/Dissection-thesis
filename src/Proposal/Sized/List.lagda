\begin{code}
module Proposal.Sized.List where

  open import Agda.Builtin.Size
  open import Data.Product using (_×_; _,_)
  open import Function using (_∘_)
  open import Data.Bool
\end{code}

%<*List>
\begin{code}
  data List (A : Set) : {_ : Size} → Set where
    Nil  : ∀ {i : Size} → List A {↑ i}
    Cons : ∀ {i : Size} → A → List A {i} → List A {↑ i}
\end{code}
%</List>

\begin{code}
  map : ∀ {i : Size} {A B : Set} → (A → B) → List A {i} → List B {i}
  map f Nil       =  Nil
  map f (Cons x xs) =  Cons (f x) (map f xs)
\end{code}


%<*append>
\begin{code}
  _++_ : ∀ {i j : Size} {A : Set} → List A {i} → List A {j} → List A {ω}
\end{code}
%</append>

\begin{code}
  Nil ++ ys       = ys
  Cons x xs ++ ys = Cons x (xs ++ ys)

  infixl 40 _++_

  [_] : ∀ {i : Size} {A : Set} → A → List A {↑ (↑ i)}
  [ x ] = Cons x Nil

  module MergeSort where

    split : ∀ {i : Size} {A : Set} → List A {i} → List A {i} × List A {i}
    split Nil         = Nil , Nil
    split (Cons x Nil) = (Cons x Nil) , Nil
    split (Cons x (Cons y xs)) with split xs
    ... | (xss , yss) = Cons x xss , Cons y yss

    merge : ∀ {i : Size} {A : Set} → (leq : A → A → Bool) → List A {i} → List A {i} → List A {ω}
    merge {.(↑ _)} leq Nil ys          = ys
    merge {.(↑ _)} leq (Cons x xs) Nil = Cons x xs
    merge {.(↑ _)} leq (Cons x xs) (Cons y ys) with leq x y
    ... | true  = Cons x (merge leq xs (Cons y ys))
    ... | false = Cons y (merge leq (Cons x xs) ys)

    mergeSort : ∀ {i : Size} {A : Set} → (leq : A → A → Bool) → List A {i} → List A {ω}
    mergeSort {.(↑ _)} leq Nil               = Nil
    mergeSort {.(↑ (↑ _))} leq (Cons x Nil)  = Cons x Nil
    mergeSort {.(↑ (↑ _))} leq (Cons {.(↑ i)} x (Cons {i} y xs)) with split {i} xs
    ... | xss , yss = merge {ω} leq (mergeSort {↑ i} leq (Cons x xss))
                                    (mergeSort {↑ i} leq (Cons y yss))
\end{code}

\begin{code}
  module QuickSort-Filter where
\end{code}

%<*Filter>
\begin{code}
    filter : ∀ {i : Size} {A : Set} → (A → Bool) → List A {i} → List A {i}
    filter p Nil = Nil
    filter p (Cons x xs) = if p x then Cons x (filter p xs) else filter p xs
\end{code}
%</Filter>


%<*QS>
\begin{code}
    quickSort : ∀ {i : Size} {A : Set}
              → (A → A → Bool) → List A {i} → List A {ω}
    quickSort {.(↑ i)} p (Nil {i})       = Nil
    quickSort {.(↑ i)} p (Cons {i} x xs) = quickSort {i} p (filter {i} (p x) xs)
                                             ++ [ x ] ++
                                           quickSort {i} p (filter {i} (not ∘ p x) xs)
\end{code}
%</QS>


\begin{code}
  module QuickSort-Partition where

    partition : ∀ {i : Size} {A : Set} → (A → Bool) → List A {i} → List A {i} × List A {i}
    partition p Nil         = Nil , Nil
    partition p (Cons x xs) with partition p xs | p x
    ... | (xss , yss) | true  = Cons x xss , yss
    ... | (xss , yss) | false = xss , (Cons x yss)

    quickSort : ∀ {i : Size} {A : Set} → (A → A → Bool) → List A {i} → List A {ω}
    quickSort p Nil         = Nil
    quickSort p (Cons x xs) with partition (p x) xs
    quickSort p (Cons x xs) | xss , yss = quickSort p xss ++ Cons x (quickSort p yss)

\end{code}
