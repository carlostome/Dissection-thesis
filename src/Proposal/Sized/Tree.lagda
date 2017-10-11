\begin{code}
module Proposal.Sized.Tree where

  open import Agda.Builtin.Size
  open import Data.Product using (_×_; _,_)
  open import Data.Bool
  open import Data.List

  data Tree (A : Set) : {_ : Size} → Set where
    Leaf : ∀ {i : Size}   → A → Tree A {↑ i}
    Node : ∀ {i j : Size} → Tree A {i} → Tree A {j} → Tree A {↑ ( i ⊔ˢ j)}

  mapTree : ∀ {i : Size} {A B : Set} → (A → B) → Tree A {i} → Tree B {i}
  mapTree {.(↑ _)} f (Leaf x)                  = Leaf (f x)
  mapTree {.(↑ (i ⊔ˢ j))} f (Node {i} {j} l r) = Node (mapTree f l) (mapTree f r) -- we need to explicitly give the i and j otherwise error

  data Stack (A : Set) : {_ : Size} → Set where
    Empty : ∀ {i : Size} → Stack A {i}
    Cons  : ∀ {i : Size} {j : Size< i} → Tree A {j} → Stack A {i} → Stack A {i}

  mutual
    load : ∀ {i j h : Size} {A B : Set} → (A → B) → Tree A {i} →  Stack A {j} → List (Tree B) → Tree B {↑ (i ⊔ˢ j)}
    load {.(↑ _)} {j} {h} f (Leaf x) stk xs = {!!}
    load {.(↑ (i₁ ⊔ˢ j₁))} {j} {h} f (Node {i₁} {j₁} t t₁) stk xs = {!!}

    loadl : ∀ {i j : Size} {A B : Set} → (A → B) → Tree A {i} → Tree A {j} →  Stack A {j} → List (Tree B) → Tree B {↑ (i ⊔ˢ j)}
    loadl {i} {j} x p x₂ x₃ = {!!}
    unload : {!!}
    unload = {!!}

  map-tl : ∀ {i : Size} {A B : Set} → (A → B) → Tree A {i} → Tree B {i}
  map-tl {.(↑ _)} f (Leaf x)                  = Leaf (f x)
  map-tl {.(↑ (i ⊔ˢ j))} f (Node {i} {j} x y) = load {i} {j} {{!!}} f x {!Cons!} []

  -- insert p e (Leaf x) with p e x
  -- insert {i} p e (Node {i}x x₁) = {!!}
  -- map f Nil       =  Nil
  -- map f (Cons x xs) =  Cons (f x) (map f xs)

  -- split : ∀ {i : Size} {A : Set} → List A {i} → List A {i} × List A {i}
  -- split Nil         = Nil , Nil
  -- split (Cons x Nil) = (Cons x Nil) , Nil
  -- split (Cons x (Cons y xs)) with split xs
  -- ... | (xss , yss) = Cons x xss , Cons y yss

  -- merge : ∀ {i : Size} {A : Set} → (leq : A → A → Bool) → List A {i} → List A {i} → List A {ω}
  -- merge {.(↑ _)} leq Nil ys          = ys
  -- merge {.(↑ _)} leq (Cons x xs) Nil = Cons x xs
  -- merge {.(↑ _)} leq (Cons x xs) (Cons y ys) with leq x y
  -- ... | true  = Cons x (merge leq xs (Cons y ys))
  -- ... | false = Cons y (merge leq (Cons x xs) ys)

  -- mergeSort : ∀ {i : Size} {A : Set} → (leq : A → A → Bool) → List A {i} → List A {ω}
  -- mergeSort {.(↑ _)} leq Nil               = Nil
  -- mergeSort {.(↑ (↑ _))} leq (Cons x Nil)  = Cons x Nil
  -- mergeSort {.(↑ (↑ _))} leq (Cons {.(↑ i)} x (Cons {i} y xs)) with split {i} xs
  -- ... | xss , yss = merge {ω} leq (mergeSort {↑ i} leq (Cons x xss))
  --                                 (mergeSort {↑ i} leq (Cons y yss))
\end{code}
