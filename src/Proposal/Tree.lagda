\begin{code}
module Proposal.Tree where

  open import Data.Maybe
  open import Data.Unit
  open import Data.Empty

  open import Data.Sum
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Induction.WellFounded
  open import Induction.Nat
  open import Data.Empty
  open import Data.Maybe
  open import Data.List
  open import Data.Bool
  open import Function
  open import Data.Unit
  open import Data.Product


  data Tree : Set where
    Tip  : Tree
    Node : Tree → Tree → Tree

  Node-inj : ∀ {t₁ t₂ t₃ t₄} → Node t₁ t₂ ≡ Node t₃ t₄ → t₁ ≡ t₃ × t₂ ≡ t₄
  Node-inj refl = refl , refl

  module UnBound where

    data Stack : Set where
      Left  : ∀ (t : Tree) → Stack → Stack
      Right : ∀ (t : Tree) → Stack → Stack
      Top   : Stack

    _⊳_ : Tree → Stack → Tree
    t ⊳ Top       = t
    t ⊳ Left x s  = Node (t ⊳ s) x
    t ⊳ Right x s = Node x (t ⊳ s)

    plug : Tree × Stack → Tree
    plug (t , s) = t ⊳ s

    data _<S_ : Tree × Stack → Tree × Stack → Set where
      <S-Right-Step : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Right t s₁) <S  (t₂ , Right t s₂)

      <S-Left-Step  : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Left t s₁) <S (t₂ , Left t s₂)

      <S-Right-Left : ∀ {t₁ t₂ s₁ s₂}   → (t₁ , Right (t₂ ⊳ s₂) s₁) <S (t₂ , Left (t₁ ⊳ s₁) s₂)

      <S-Right-Base : ∀ {t t₁ s₁}       → (t , Right t₁ s₁) <S (Node t₁ (t ⊳ s₁) , Top)

      <S-Left-Base  : ∀ {t t₁ s₁}       → (Node (t ⊳ s₁) t₁ , Top)    <S (t , Left t₁ s₁)

    related : ∀ t₁ s₁ t₂ s₂ →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊳ s₁ ) ≡ (t₂ ⊳ s₂)
    related t₁ Top t₂ Top ()
    related .(Node (t₂ ⊳ s₂) x₁) Top t₂ (Left x₁ s₂) <S-Left-Base = refl
    related t₁ Top t₂ (Right x₁ s₂) ()
    related t₁ (Left x₁ s₁) t₂ Top ()
    related t₁ (Left x₁ s₁) t₂ (Left .x₁ s₂) (<S-Left-Step x) = cong (λ x → Node x x₁) (related t₁ s₁ t₂ s₂ x)
    related t₁ (Left x₁ s₁) t₂ (Right x₂ s₂) ()
    related t₁ (Right x₁ s₁) .(Node x₁ (t₁ ⊳ s₁)) Top <S-Right-Base = refl
    related t₁ (Right .(t₂ ⊳ s₂) s₁) t₂ (Left .(t₁ ⊳ s₁) s₂) <S-Right-Left = refl
    related t₁ (Right x₁ s₁) t₂ (Right .x₁ s₂) (<S-Right-Step p) = cong (λ x → Node x₁ x) (related t₁ s₁ t₂ s₂ p)

    mutual
      accR : ∀ (t : Tree) (t₁ : Tree) (s₁ : Stack)→ Acc _<S_ (t , s₁) → (∀ y  → y <S (t , Right t₁ s₁) → Acc (_<S_) y)
      accR t t₁ s₁ (acc rs) .(_ , Right t₁ _) (<S-Right-Step p) = acc (accR _ t₁ _ (rs _ p))

      accT : ∀ (t : Tree) → (∀ y → y <S (t , Top) → Acc (_<S_) y)
      accT t (y , Left t₁ s) ()
      accT .(Node t₁ (y ⊳ s)) (y , Right t₁ s) <S-Right-Base = acc (accR {!!} {!!} {!!} {!<S-WF!}) -- acc (accR y t₁ s (<S-WF (y , s)))
      accT t (y , Top) ()

      aux : (x y : Tree × Stack) → y <S x → Acc (_<S_) y
      aux (t , Left t₁ stk) (y , Left t₂ s) p  = {!!}
      aux (t , Left t₁ stk) (y , Right t₂ s) p = {!!}
      aux (t , Left t₁ stk) (.(Node (t ⊳ stk) t₁) , Top) <S-Left-Base = acc (accT (Node (t ⊳ stk) t₁))
      aux (t , Right t₁ stk) .(_ , Right t₁ _) (<S-Right-Step p) = acc (accR _ t₁ _ (aux (t , stk) _ p))
      aux (t , Top) (t′ , Left t₁ stk) ()
      aux (.(Node t₁ (t′ ⊳ stk)) , Top) (t′ , Right t₁ stk) <S-Right-Base = acc (accR {!!} {!!} {!!} {!<S-WF!})
      aux (t , Top) (t′ , Top) ()

      <S-WF : Well-founded (_<S_)
      <S-WF x = acc (aux x)

  -- module Tree+BoundStack where

  --   data BTree : ℕ → Set where
  --     BTip  : BTree 1
  --     BNode : ∀ {n} → BTree n → BTree n → BTree (1 + n)

  --   data Stack : ℕ → Set where
  --     Left  : ∀ {n} (t : Tree) → Stack n → Stack (1 + n)
  --     Right : ∀ {n} (t : Tree) → Stack n → Stack (1 + n)
  --     Top   : ∀ {n}                      → Stack (1 + n)

  --   _⊳_ : ∀ {n : ℕ} → Tree → Stack n → Tree
  --   t ⊳ Top       = t
  --   t ⊳ Left x s  = Node (t ⊳ s) x
  --   t ⊳ Right x s = Node x (t ⊳ s)

  --   data [_]_<S_ : (n : ℕ) → (l₁ : Tree × Stack n) → (l₂ : Tree × Stack n) → Set where
  --     <S-Right-Step : ∀ {n} {t t₁ t₂ s₁ s₂} → [ n ] (t₁ , s₁) <S (t₂ , s₂) → [ 1 + n ] (t₁ , Right t s₁) <S  (t₂ , Right t s₂)

  --     <S-Left-Step  : ∀ {n} {t t₁ t₂ s₁ s₂} → [ n ] (t₁ , s₁) <S (t₂ , s₂) → [ 1 + n ] (t₁ , Left t s₁) <S (t₂ , Left t s₂)

  --     <S-Right-Left : ∀ {n} {t₁ t₂ s₁ s₂} → [ 1 + n ] (t₁ , Right (t₂ ⊳ s₂) s₁) <S (t₂ , Left (t₁ ⊳ s₁) s₂)

  --     <S-Right-Base : ∀ {n} {t t₁ s₁}       → [ 1 + n ] (t , Right t₁ s₁) <S (Node t₁ (t ⊳ s₁) , Top)

  --     <S-Left-Base  : ∀ {n} {t t₁ s₁}       → [ 1 + n ] (Node (t ⊳ s₁) t₁ , Top)    <S (t , Left t₁ s₁)

  --   mutual
  --     accR : ∀ (n : ℕ) (t₁ : Tree) (t : Tree) (s₁ : Stack n) → Acc [ n ]_<S_ (t , s₁) → (∀ y  → [ 1 + n ] y <S (t , Right t₁ s₁) → Acc ([ 1 + n ]_<S_) y)
  --     accR n t₁ t s (acc x) (y , .(Right t₁ _)) (<S-Right-Step p) = acc (accR n t₁ y _ (x _ p))

  --     accL : ∀ (n : ℕ) (t₁ : Tree) (t : Tree) (s₁ : Stack n) → Acc [ n ]_<S_ (t , s₁) → (∀ y → [ suc n ] y <S (t , Left t₁ s₁) → Acc ([_]_<S_ (suc n)) y)
  --     accL n t₁ t s₁ (acc rs) (y , Left .t₁ s) (<S-Left-Step p)            = acc (accL n t₁ y s (rs (y , s) p))
  --     accL n .(y ⊳ s) t s₁ (acc rs) (y , Right .(t ⊳ s₁) s) <S-Right-Left = acc (accR n (t ⊳ s₁) y s (<S-WF n (y , s)))
  --     accL n t₁ t s₁ (acc rs) (.(Node (t ⊳ s₁) t₁) , Top) <S-Left-Base    = acc (accT n (Node (t ⊳ s₁) t₁))

  --     accT : ∀ (n : ℕ) (t : Tree) → (∀ y  → [ 1 + n ] y <S (t , Top) → Acc ([ 1 + n ]_<S_) y)
  --     accT n t (y , Left t₁ s) ()
  --     accT n t (y , Top)       ()
  --     accT n .(Node t₁ (y ⊳ s)) (y , Right t₁ s) <S-Right-Base = acc (accR n t₁ y s (<S-WF n (y , s)))

  --     <S-WF : ∀ n → Well-founded ([ n ]_<S_)
  --     <S-WF n x = acc (aux n x)
  --       where
  --         aux : (n : ℕ) (x y : Tree × Stack n) → [ n ] y <S x → Acc ([_]_<S_ n) y
  --         aux zero x y ()
  --         aux (suc n) (x , Left t s) (y , Left .t s₁) (<S-Left-Step p)              = acc (accL n t y s₁ (aux n (x , s) (y , s₁) p))
  --         aux (suc n) (x , Left .(y ⊳ s₁) s) (y , Right .(x ⊳ s) s₁) <S-Right-Left = acc (accR n (x ⊳ s) y s₁ (<S-WF n (y , s₁)))
  --         aux (suc n) (x , Left t s) (.(Node (x ⊳ s) t) , Top) <S-Left-Base         = acc (accT n (Node (x ⊳ s) t))
  --         aux (suc n) (x , Right t s) (y , .(Right t _)) (<S-Right-Step p) = acc (accR n t y _ (aux n (x , s) (y , _) p))
  --         aux (suc n) (x , Top) (y , Left t s₁) ()
  --         aux (suc n) (.(Node t (y ⊳ s₁)) , Top) (y , Right t s₁) <S-Right-Base = acc (accR n t y s₁ (<S-WF n (y , s₁)))
  --         aux (suc n) (x , Top) (y , Top) ()

  --   related : ∀ {n} t₁ s₁ t₂ s₂ → [ n ] (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊳ s₁ ) ≡ (t₂ ⊳ s₂)
  --   related t₁ Top t₂ Top ()
  --   related .(Node (t₂ ⊳ s₂) x₁) Top t₂ (Left x₁ s₂) <S-Left-Base = refl
  --   related t₁ Top t₂ (Right x₁ s₂) ()
  --   related t₁ (Left x₁ s₁) t₂ Top ()
  --   related t₁ (Left x₁ s₁) t₂ (Left .x₁ s₂) (<S-Left-Step x) = cong (λ x → Node x x₁) (related t₁ s₁ t₂ s₂ x)
  --   related t₁ (Left x₁ s₁) t₂ (Right x₂ s₂) ()
  --   related t₁ (Right x₁ s₁) .(Node x₁ (t₁ ⊳ s₁)) Top <S-Right-Base = refl
  --   related t₁ (Right .(t₂ ⊳ s₂) s₁) t₂ (Left .(t₁ ⊳ s₁) s₂) <S-Right-Left = refl
  --   related t₁ (Right x₁ s₁) t₂ (Right .x₁ s₂) (<S-Right-Step p) = cong (λ x → Node x₁ x) (related t₁ s₁ t₂ s₂ p)

  -- module FStack+Tree where

  --   -- Perfect binary trees of depth n
  --   data PTree : ℕ → Set where
  --     Tip  : PTree 0
  --     Node : ∀ {n} → PTree n → PTree n → PTree (1 + n)

  --   -- Stacks of at most size n
  --   data FStack : ℕ → Set where
  --     Top   : ∀ {n} →           FStack n
  --     Left  : ∀ {n} → PTree n → FStack n → FStack (1 + n)
  --     Right : ∀ {n} → PTree n → FStack n → FStack (1 + n)

  --   diffFS : ∀ {n} → FStack n → ℕ
  --   diffFS {n} Top           = n
  --   diffFS {n} (Left x stk)  = diffFS stk
  --   diffFS {n} (Right x stk) = diffFS stk

  --   -- a stack of at most size n and a tree with the rest make a tree of size n
  --   FStack+PTree : ℕ → Set
  --   FStack+PTree n = Σ (FStack n) λ fv → PTree (diffFS fv)

  --   plug : ∀ {n} → FStack+PTree n → PTree n
  --   plug (Top , t)         = t
  --   plug (Left x stk , t)  = Node (plug (stk , t)) x
  --   plug (Right x stk , t) = Node x (plug (stk , t))

  --   _⊳_ : ∀ {n} → (fs : FStack n) → PTree (diffFS fs) → PTree n
  --   fs ⊳ t = plug (fs , t)

  --   -- order relation between FStack+PTree of size n (the tree doesn't play an important role)
  --   data [_]_<S_ : (n : ℕ) → FStack+PTree n → FStack+PTree n → Set where
  --     <S-Right-Step : ∀ {n} {s₁ s₂ : FStack n} {t t₁ t₂}  → [ n ] (s₁ , t₁) <S (s₂ , t₂) → [ 1 + n ] (Right t s₁ , t₁) <S  (Right t s₂ , t₂)

  --     <S-Left-Step  : ∀ {n} {s₁ s₂ : FStack n} {t t₁ t₂}  → [ n ] (s₁ , t₁) <S (s₂ , t₂) → [ 1 + n ] (Left t s₁ , t₁) <S (Left t s₂ , t₂)

  --     <S-Right-Left : ∀ {n} {s₁ s₂ : FStack n} {t₁ t₂}  → [ 1 + n ] (Right (s₂ ⊳ t₂) s₁ , t₁) <S (Left (s₁ ⊳ t₁) s₂ , t₂)

  --     <S-Right-Base : ∀ {n} {s : FStack n} {t t₁}       → [ 1 + n ] (Right t₁ s , t) <S (Top , Node t₁ (s ⊳ t) )

  --     <S-Left-Base  : ∀ {n} {s : FStack n} {t t₁}       → [ 1 + n ] (Top , Node (s ⊳ t) t₁)    <S (Left t₁ s , t)

  --   related : ∀ {n} (d₁ d₂ : FStack+PTree n) → [ n ] d₁ <S d₂ → plug d₁ ≡ plug d₂
  --   related (Top , t₁) (Top , t₂) ()
  --   related (Top , .(Node (plug (s₂ , t₂)) x₁)) (Left x₁ s₂ , t₂) <S-Left-Base = {!!}
  --   related (Top , t₁) (Right x₁ s₂ , t₂) x = {!!}
  --   related (Left x₁ s₁ , t₁) (s₂ , t₂) x = {!!}
  --   related (Right x₁ s₁ , t₁) (s₂ , t₂) x = {!!}

  --   -- and the relation is well founded
  --   mutual
  --     accR : ∀ (n : ℕ) (t₁ : PTree n) (s : FStack n) (t : PTree (diffFS s)) → Acc [ n ]_<S_ (s , t)
  --                                                                         → (∀ y  → [ 1 + n ] y <S (Right t₁ s , t) → Acc ([ 1 + n ]_<S_) y)
  --     accR n t₁ s t (acc rs) (.(Right t₁ _) , y) (<S-Right-Step p) = acc (accR n t₁ _ y (rs _ p))

  --     accL : ∀ (n : ℕ) (t₁ : PTree n) (s : FStack n) (t : PTree (diffFS s)) → Acc [ n ]_<S_ (s , t) → (∀ y → [ suc n ] y <S (Left t₁ s , t) → Acc ([_]_<S_ (suc n)) y)
  --     accL n t₁ s t (acc rs) (Top , .(Node (plug (s , t)) t₁)) <S-Left-Base = acc (accT n (Node (plug (s , t)) t₁))
  --     accL n t₁ s t (acc rs) (Left .t₁ stk , y) (<S-Left-Step p) = acc (accL n t₁ stk y (rs (stk , y) p))
  --     accL n .(plug (stk , y)) s t (acc rs) (Right .(plug (s , t)) stk , y) <S-Right-Left = acc (accR n (plug (s , t)) stk y (<S-WF n (stk , y)))

  --     accT : ∀ (n : ℕ) (t : PTree (1 + n)) → (∀ y  → [ 1 + n ] y <S (Top , t) → Acc ([ 1 + n ]_<S_) y)
  --     accT n t (Top , y) ()
  --     accT n t (Left x₁ stk , y) ()
  --     accT n .(Node x₁ (plug (stk , y))) (Right x₁ stk , y) <S-Right-Base = acc (accR n x₁ stk y (<S-WF n (stk , y)))

  --     <S-WF : ∀ n → Well-founded ([ n ]_<S_)
  --     <S-WF n x = acc (aux n x)
  --       where
  --         aux : (n : ℕ) (x y : FStack+PTree n) → [ n ] y <S x → Acc ([_]_<S_ n) y
  --         aux zero x y ()
  --         aux (suc n) (Top , t) (Top , t′) ()
  --         aux (suc n) (Top , t) (Left x₁ stk , t′) ()
  --         aux (suc n) (Top , .(Node x₁ (plug (stk , t′)))) (Right x₁ stk , t′) <S-Right-Base = acc (accR n x₁ stk t′ (<S-WF n (stk , t′)))

  --         aux (suc n) (Left x₁ s , t) (Top , .(Node (plug (s , t)) x₁)) <S-Left-Base                 = acc (accT n (Node (plug (s , t)) x₁))
  --         aux (suc n) (Left x₁ s , t) (Left .x₁ stk , t′) (<S-Left-Step p)                           = acc (accL n x₁ stk t′ (aux n (s , t) (stk , t′) p))
  --         aux (suc n) (Left .(plug (stk , t′)) s , t) (Right .(plug (s , t)) stk , t′) <S-Right-Left = acc (accR n (plug (s , t)) stk t′ (<S-WF n (stk , t′)))

  --         aux (suc n) (Right x₁ s , t) (_ , _) (<S-Right-Step p) = acc (accR n x₁ _ _ (aux n (s , t) _ p))

  --   -- we can separate later the proof from the function
  --   leftmost : ∀ {n} → (p : PTree n) → Σ (FStack+PTree n) λ d → plug d ≡ p
  --   leftmost Tip          = (Top , Tip) , refl
  --   leftmost (Node t₁ t₂) with leftmost t₁
  --   leftmost (Node .(plug (stk , t′)) t₂) | (stk , t′) , refl = (Left t₂ stk , t′) , refl

  --   next : ∀ {n} → FStack+PTree n → Maybe (FStack+PTree n)
  --   next (Top , Tip)         = nothing
  --   next (Top , Node t₁ t₂)  with leftmost t₂
  --   ... | ((stk , t′) , _)   = just (Right t₁ stk , t′)
  --   next (Left x Top , t)            = just (Top , Node t x)
  --   next (Left x (Left x₁ stk) , t)  with next ((Left x₁ stk) , t)
  --   next (Left x (Left x₁ stk) , t) | just x₂ = {!!}
  --   next (Left x (Left x₁ stk) , t) | nothing = nothing
  --   next (Left x (Right x₁ stk) , t)  = {!!}
  --   next (Right x Top , t)            = {!!}
  --   next (Right x (Left x₁ stk) , t)  = {!!}
  --   next (Right x (Right x₁ stk) , t) = {!!}

  --   theorem : ∀ {n} → (d : FStack+PTree n) → (x : FStack+PTree n) → next d ≡ just x → [ n ] x <S d
  --   theorem (Top , Tip) x ()
  --   theorem (Top , Node t₁ t₂) x p with leftmost t₂
  --   theorem (Top , Node t₁ .(plug (stk , t))) .(Right t₁ stk , t) refl | (stk , t) , refl = <S-Right-Base
  --   theorem (Left x stk  , t) d p = {!!}
  --   theorem (Right x stk , t) d p = {!!}

  --   fixpoint : ∀ {A : Set} → (_<_ : A → A → Set) → Well-founded _<_ → (f : A → Maybe A) → (∀ a x → f a ≡ just x → x < a) → A → A
  --   fixpoint {A} _<_ x f pr a = aux a (x a)
  --     where
  --       aux : (x : A) → Acc _<_ x → A
  --       aux x (acc rs) with f x | inspect f x
  --       aux x (acc rs) | just b | Reveal_·_is_.[ eq ]  with pr x b eq
  --       ... | z  = aux b (rs b z)
  --       aux x (acc rs) | nothing | _ = x
\end{code}
