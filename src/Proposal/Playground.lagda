\begin{code}
module Proposal.Playground where

  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat
  open import Function
  open import Data.Product hiding (map)
  open import Data.Sum hiding (map)
  open import Data.List 
  open import Induction.WellFounded

  data Cont (r : Set) (a : Set) : Set where
    cont : (c : (a → r) → r) → Cont r a

  reset : ∀ {r} → Cont r r → r
  reset (cont c) = c (λ z → z)

  shift : ∀ {r a} → ((a → r) → Cont r r) → Cont r a
  shift x = cont λ k → reset (x k)

  data Zipper (t : Set → Set) (a : Set) : Set where
    Done : t a → Zipper t a
    Z    : a → (Maybe a → Zipper t a) → Zipper t a

  data Tree : Set where
    Val : ℕ → Tree
    Add : Tree → Tree → Tree

  data Subtree : Tree → Tree → Set where
    Base-l : ∀ {t₁ t₂}     → Subtree t₁ (Add t₁ t₂)
    Base-r : ∀ {t₁ t₂}     → Subtree t₂ (Add t₁ t₂)
    Step-l   : ∀ {t t₁ t₂} → Subtree t t₁ → Subtree t (Add t₁ t₂)
    Step-r   : ∀ {t t₁ t₂} → Subtree t t₂ → Subtree t (Add t₁ t₂)

  Subtree-WF : Well-founded Subtree
  Subtree-WF x = acc (aux x)
    where
      aux : ∀ (x : Tree) → (∀ y → Subtree y x → Acc Subtree y)
      aux (Val _) y ()
      aux (Add t₁ t₂) .t₁ Base-l = Subtree-WF t₁
      aux (Add t₁ t₂) .t₂ Base-r = Subtree-WF t₂
      aux (Add t₁ t₂) y (Step-l p) = aux t₁ y p
      aux (Add t₁ t₂) y (Step-r p) = aux t₂ y p

  foldTree : ∀ {A : Set} → (ℕ → A) → (A → A → A) → Tree → A
  foldTree l n (Val x)     = l x
  foldTree l n (Add t₁ t₂) = n (foldTree l n t₁) (foldTree l n t₂)

  go : ∀ {A : Set} → (ℕ → A) → (A → A → A) → Tree → (A → A) → A
  go leaf node (Val x)   k = k (leaf x)
  go leaf node (Add l r) k = go leaf node l (λ l → go leaf node r (k ∘ (node l)))

  go-fuel : ∀ {A : Set} → (fuel : ℕ) → (ℕ → A) → (A → A → A) → Tree → (ℕ → A → Maybe A) → Maybe A
  go-fuel zero leaf node t k              = nothing
  go-fuel (suc n) leaf node (Val x) k     = k n (leaf x)
  go-fuel (suc n) leaf node (Add t₁ t₂) k = go-fuel n leaf node t₁ (λ f l → go-fuel f leaf node t₂ (λ f′ r → k f′ (node l r)))

  go-simple : (i : Tree × ℕ) → Acc Subtree (proj₁ i) → ℕ
  go-simple (Val r , x)     ac       = r + x
  go-simple (Add t₁ t₂ , x) (acc rs) = go-simple (t₁ , go-simple (t₂ , x) (rs t₂ Base-r)) (rs t₁ Base-l)

  go-simple-2 : (t : Tree) → ℕ → ℕ
  go-simple-2 (Val r) x     = r + x
  go-simple-2 (Add t₁ t₂) x = go-simple-2 t₂ (go-simple-2 t₁ x)

  more-go : Tree ⊎ ℕ → ((Tree ⊎ ℕ) → ℕ) → ℕ
  more-go (inj₁ (Val x)) k     = k (inj₂ x)
  more-go (inj₁ (Add t₁ t₂)) k = more-go (inj₁ t₁) λ { (inj₁ x) → more-go {!!} {!!}
                                                     ; (inj₂ y) → more-go {!inj₁ t₂!} λ x → {!!}}
  more-go (inj₂ n) k = k (inj₂ n)

  t : Tree
  t = Add (Add (Val 2) (Val 3)) (Val 1)


  eval : Tree → ℕ
  eval t = go id (_+_) t id

  evalN : Tree → ℕ → Maybe ℕ
  evalN t n = go-fuel n id (_+_) t λ _ x → just x

  data X : Set where
    x-cons : X → X

  data Empty : Set where

  to : X → Empty
  to (x-cons x) = to x

  from : Empty → X
  from ()

\end{code}
