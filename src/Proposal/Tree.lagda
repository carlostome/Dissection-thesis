\begin{code}
module Proposal.Tree where

  open import Data.Maybe
  open import Data.Unit
  open import Data.Empty

  open import Data.Sum
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Induction.WellFounded
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

  module Bound where

    data Stack : ℕ → Set where
      Left  : ∀ {n} (t : Tree) → Stack n → Stack (1 + n)
      Right : ∀ {n} (t : Tree) → Stack n → Stack (1 + n)
      Top   : ∀ {n} → Stack (1 + n)

    data [_]_<S_ : (n : ℕ) → Stack n → Stack n → Set where
      <S-Right-Step : ∀ {n} {t s₁ s₂} → [ n ] s₁ <S s₂ → [ 1 + n ] Right t s₁ <S  Right t s₂

      <S-Left-Step  : ∀ {n} {t s₁ s₂} → [ n ] s₁ <S  s₂ →
                                        [ 1 + n ] Left t s₁ <S Left t s₂

      <S-Right-Left : ∀ {n} {t₁ t₂ s₁ s₂} → [ 1 + n ] Right t₁ s₁ <S Left t₂ s₂

      <S-Right-Base : ∀ {n} {t₁ s₁}       → [ 1 + n ] Right t₁ s₁ <S Top

      <S-Left-Base  : ∀ {n} {x₁ s₁}       → [ 1 + n ] Top         <S Left x₁ s₁

    mutual
      accR : ∀ (n : ℕ) (t₁ : Tree) (s₁ : Stack n)→ Acc [ n ]_<S_ s₁ → (∀ y  → [ 1 + n ] y <S Right t₁ s₁ → Acc ([ 1 + n ]_<S_) y)
      accR n t s (acc x) .(Right t _) (<S-Right-Step {s₁ = s₁} p) = acc (accR n t s₁ (x s₁ p))

      accL : ∀ (n : ℕ) (t : Tree) (s₁ : Stack n) → Acc [ n ]_<S_ s₁ → (∀ y → [ suc n ] y <S Left t s₁ → Acc ([_]_<S_ (suc n)) y)
      accL n t s₁ (acc x) .(Left t _) (<S-Left-Step p) = acc (accL n _ _ (x _ p))
      accL n t s₁ (acc x) .(Right _ _) <S-Right-Left   = acc (accR n _ _ (<S-WF n _))
      accL n t s₁ (acc x) .Top <S-Left-Base            = acc (accT n)

      accT : ∀ n → (∀ y  → [ 1 + n ] y <S Top → Acc ([ 1 + n ]_<S_) y)
      accT n .(Right t₁ s₁) (<S-Right-Base {t₁ = t₁} {s₁ = s₁}) = acc (accR n t₁ s₁ (<S-WF n s₁))

      <S-WF : ∀ n → Well-founded ([ n ]_<S_)
      <S-WF n x = acc (aux n x)
        where
          aux : (n : ℕ) (x y : Stack n) → [ n ] y <S x → Acc ([_]_<S_ n) y
          aux zero x y ()
          aux (suc n) (Left t s)  .(Left t _) (<S-Left-Step p) = acc (accL n t _ (aux n _ _ p))
          aux (suc n) (Left t s)  .(Right t₁ s₁) (<S-Right-Left {t₁ = t₁} {s₁ = s₁})   = acc (accR n t₁ s₁ (<S-WF n _))
          aux (suc n) (Left t s)  .Top <S-Left-Base                                    = acc (accT n)
          aux (suc n) (Right t s) .(Right t s₁) (<S-Right-Step {s₁ = s₁} p)  = acc (accR n t s₁ (aux n s s₁ p))
          aux (suc n) Top .(Right t₁ s₁) (<S-Right-Base {t₁ = t₁} {s₁ = s₁}) = acc (accR n t₁ s₁ (<S-WF n s₁))

  module UnBound where

    data Stack : Set where
      Left  : ∀ (t : Tree) → Stack → Stack
      Right : ∀ (t : Tree) → Stack → Stack
      Top   : Stack

    data _<S_ : Stack → Stack → Set where
      <S-Right-Step : ∀ {t s₁ s₂} → s₁ <S s₂  → Right t s₁ <S  Right t s₂

      <S-Left-Step  : ∀ {t s₁ s₂} → s₁ <S  s₂ → Left t s₁ <S Left t s₂

      <S-Right-Left : ∀ {t₁ t₂ s₁ s₂} → Right t₁ s₁ <S Left t₂ s₂

      <S-Right-Base : ∀ {t₁ s₁}       → Right t₁ s₁ <S Top

      <S-Left-Base  : ∀ {x₁ s₁}       → Top         <S Left x₁ s₁

    mutual
      accR : ∀ (t₁ : Tree) (s₁ : Stack)→ Acc _<S_ s₁ → (∀ y  → y <S Right t₁ s₁ → Acc (_<S_) y)
      accR t s (acc x) .(Right t _) (<S-Right-Step {s₁ = s₁} p) = acc (accR t s₁ (x s₁ p))

      accL : ∀ (t : Tree) (s₁ : Stack) → Acc _<S_ s₁ → (∀ y → y <S Left t s₁ → Acc (_<S_) y)
      accL t s₁ (acc x) .(Left t _) (<S-Left-Step p) = acc (accL _ _ (x _ p))
      accL t s₁ (acc x) .(Right _ s) (<S-Right-Left {s₁ = s})  = acc (accR _ _ ({!<S-WF!}))
      accL t s₁ (acc x) .Top <S-Left-Base            = acc (accT)

      -- non termination highlighting is non deterministic!
      accT : (∀ y  → y <S Top → Acc (_<S_) y)
      accT .(Right t₁ s₁) (<S-Right-Base {t₁ = t₁} {s₁ = s₁}) = acc (accR t₁ s₁ (<S-WF s₁))

      <S-WF : Well-founded (_<S_)
      <S-WF x = acc (aux x)
        where
          aux : (x y : Stack) → y <S x → Acc (_<S_) y
          aux (Left t s)  .(Left t _) (<S-Left-Step p) = acc (accL t _ (aux _ _ p))
          aux (Left t s)  .(Right t₁ s₁) (<S-Right-Left {t₁ = t₁} {s₁ = s₁})   = acc (accR t₁ s₁ (<S-WF _))
          aux (Left t s)  .Top <S-Left-Base                                    = acc (accT)
          aux (Right t s) .(Right t s₁) (<S-Right-Step {s₁ = s₁} p)  = acc (accR t s₁ (aux s s₁ p))
          aux Top .(Right t₁ s₁) (<S-Right-Base {t₁ = t₁} {s₁ = s₁}) = acc (accR t₁ s₁ (<S-WF s₁))

  module Tree+BoundStack where

    data BTree : ℕ → Set where
      BTip  : BTree 1
      BNode : ∀ {n} → BTree n → BTree n → BTree (1 + n)

    data Stack : ℕ → Set where
      Left  : ∀ {n} (t : Tree) → Stack n → Stack (1 + n)
      Right : ∀ {n} (t : Tree) → Stack n → Stack (1 + n)
      Top   : ∀ {n}                      → Stack (1 + n)

    _⊳_ : ∀ {n : ℕ} → Tree → Stack n → Tree
    t ⊳ Top       = t
    t ⊳ Left x s  = Node (t ⊳ s) x
    t ⊳ Right x s = Node x (t ⊳ s)

    data [_]_<S_ : (n : ℕ) → (l₁ : Tree × Stack n) → (l₂ : Tree × Stack n) → Set where
      <S-Right-Step : ∀ {n} {t t₁ t₂ s₁ s₂} → [ n ] (t₁ , s₁) <S (t₂ , s₂) → [ 1 + n ] (t₁ , Right t s₁) <S  (t₂ , Right t s₂)

      <S-Left-Step  : ∀ {n} {t t₁ t₂ s₁ s₂} → [ n ] (t₁ , s₁) <S (t₂ , s₂) → [ 1 + n ] (t₁ , Left t s₁) <S (t₂ , Left t s₂)

      <S-Right-Left : ∀ {n} {t₁ t₂ s₁ s₂} → [ 1 + n ] (t₁ , Right (t₂ ⊳ s₂) s₁) <S (t₂ , Left (t₁ ⊳ s₁) s₂)

      <S-Right-Base : ∀ {n} {t t₁ s₁}       → [ 1 + n ] (t , Right t₁ s₁) <S (Node t₁ (t ⊳ s₁) , Top)

      <S-Left-Base  : ∀ {n} {t t₁ s₁}       → [ 1 + n ] (Node (t ⊳ s₁) t₁ , Top)    <S (t , Left t₁ s₁)

    mutual
      accR : ∀ (n : ℕ) (t₁ : Tree) (t : Tree) (s₁ : Stack n) → Acc [ n ]_<S_ (t , s₁) → (∀ y  → [ 1 + n ] y <S (t , Right t₁ s₁) → Acc ([ 1 + n ]_<S_) y)
      accR n t₁ t s (acc x) (y , .(Right t₁ _)) (<S-Right-Step p) = acc (accR n t₁ y _ (x _ p))

      accL : ∀ (n : ℕ) (t₁ : Tree) (t : Tree) (s₁ : Stack n) → Acc [ n ]_<S_ (t , s₁) → (∀ y → [ suc n ] y <S (t , Left t₁ s₁) → Acc ([_]_<S_ (suc n)) y)
      accL n t₁ t s₁ (acc rs) (y , Left .t₁ s) (<S-Left-Step p)            = acc (accL n t₁ y s (rs (y , s) p))
      accL n .(y ⊳ s) t s₁ (acc rs) (y , Right .(t ⊳ s₁) s) <S-Right-Left = acc (accR n (t ⊳ s₁) y s (<S-WF n (y , s)))
      accL n t₁ t s₁ (acc rs) (.(Node (t ⊳ s₁) t₁) , Top) <S-Left-Base    = acc (accT n (Node (t ⊳ s₁) t₁))

      accT : ∀ (n : ℕ) (t : Tree) → (∀ y  → [ 1 + n ] y <S (t , Top) → Acc ([ 1 + n ]_<S_) y)
      accT n t (y , Left t₁ s) ()
      accT n t (y , Top)       ()
      accT n .(Node t₁ (y ⊳ s)) (y , Right t₁ s) <S-Right-Base = acc (accR n t₁ y s (<S-WF n (y , s)))

      <S-WF : ∀ n → Well-founded ([ n ]_<S_)
      <S-WF n x = acc (aux n x)
        where
          aux : (n : ℕ) (x y : Tree × Stack n) → [ n ] y <S x → Acc ([_]_<S_ n) y
          aux zero x y ()
          aux (suc n) (x , Left t s) (y , Left .t s₁) (<S-Left-Step p)              = acc (accL n t y s₁ (aux n (x , s) (y , s₁) p))
          aux (suc n) (x , Left .(y ⊳ s₁) s) (y , Right .(x ⊳ s) s₁) <S-Right-Left = acc (accR n (x ⊳ s) y s₁ (<S-WF n (y , s₁)))
          aux (suc n) (x , Left t s) (.(Node (x ⊳ s) t) , Top) <S-Left-Base         = acc (accT n (Node (x ⊳ s) t))
          aux (suc n) (x , Right t s) (y , .(Right t _)) (<S-Right-Step p) = acc (accR n t y _ (aux n (x , s) (y , _) p))
          aux (suc n) (x , Top) (y , Left t s₁) ()
          aux (suc n) (.(Node t (y ⊳ s₁)) , Top) (y , Right t s₁) <S-Right-Base = acc (accR n t y s₁ (<S-WF n (y , s₁)))
          aux (suc n) (x , Top) (y , Top) ()

    related : ∀ {n} t₁ s₁ t₂ s₂ → [ n ] (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊳ s₁ ) ≡ (t₂ ⊳ s₂)
    related t₁ Top t₂ Top ()
    related .(Node (t₂ ⊳ s₂) x₁) Top t₂ (Left x₁ s₂) <S-Left-Base = refl
    related t₁ Top t₂ (Right x₁ s₂) ()
    related t₁ (Left x₁ s₁) t₂ Top ()
    related t₁ (Left x₁ s₁) t₂ (Left .x₁ s₂) (<S-Left-Step x) = cong (λ x → Node x x₁) (related t₁ s₁ t₂ s₂ x)
    related t₁ (Left x₁ s₁) t₂ (Right x₂ s₂) ()
    related t₁ (Right x₁ s₁) .(Node x₁ (t₁ ⊳ s₁)) Top <S-Right-Base = refl
    related t₁ (Right .(t₂ ⊳ s₂) s₁) t₂ (Left .(t₁ ⊳ s₁) s₂) <S-Right-Left = refl
    related t₁ (Right x₁ s₁) t₂ (Right .x₁ s₂) (<S-Right-Step p) = cong (λ x → Node x₁ x) (related t₁ s₁ t₂ s₂ p)

  module FStack+Tree where

    -- Perfect binary trees of depth n
    data PTree : ℕ → Set where
      Tip  : PTree 0
      Node : ∀ {n} → PTree n → PTree n → PTree (1 + n)

    -- Stacks of at most size n
    data FStack : ℕ → Set where
      Top   : ∀ {n} →           FStack n
      Left  : ∀ {n} → PTree n → FStack n → FStack (1 + n)
      Right : ∀ {n} → PTree n → FStack n → FStack (1 + n)

    diffFS : ∀ {n} → FStack n → ℕ
    diffFS {n} Top           = n
    diffFS {n} (Left x stk)  = diffFS stk
    diffFS {n} (Right x stk) = diffFS stk

    -- a stack of at most size n and a tree with the rest make a tree of size n
    FStack+PTree : ℕ → Set
    FStack+PTree n = Σ (FStack n) λ fv → PTree (diffFS fv)

    plug : ∀ {n} → FStack+PTree n → PTree n
    plug {zero} (Top , t) = t
    plug {suc zero} (Top , t) = t
    plug {suc zero} (Left x Top , t)  = Node t x
    plug {suc zero} (Right x Top , t) = Node x t
    plug {suc (suc n)} (Top , t) = t
    plug {suc (suc n)} (Left x fstk , t)  = Node (plug (fstk , t)) x
    plug {suc (suc n)} (Right x fstk , t) = Node x (plug (fstk , t))

    _⊳_ : ∀ {n} → (fs : FStack n) → PTree (diffFS fs) → PTree n
    fs ⊳ t = plug (fs , t)

    -- order relation between FStack+PTree of size n (the tree doesn't play an important role)
    data [_]_<S_ : (n : ℕ) → FStack+PTree n → FStack+PTree n → Set where
      <S-Right-Step : ∀ {n} {s₁ s₂ : FStack n} {t t₁ t₂}  → [ n ] (s₁ , t₁) <S (s₂ , t₂) → [ 1 + n ] (Right t s₁ , t₁) <S  (Right t s₂ , t₂)

      <S-Left-Step  : ∀ {n} {s₁ s₂ : FStack n} {t t₁ t₂}  → [ n ] (s₁ , t₁) <S (s₂ , t₂) → [ 1 + n ] (Left t s₁ , t₁) <S (Left t s₂ , t₂)

      <S-Right-Left : ∀ {n} {s₁ s₂ : FStack n} {t₁ t₂}  → [ 1 + n ] (Right (s₂ ⊳ t₂) s₁ , t₁) <S (Left (s₁ ⊳ t₁) s₂ , t₂)

      <S-Right-Base : ∀ {n} {s : FStack n} {t t₁}       → [ 1 + n ] (Right t₁ s , t) <S (Top , Node t₁ (s ⊳ t) )

      <S-Left-Base  : ∀ {n} {s : FStack n} {t t₁}       → [ 1 + n ] (Top , Node (s ⊳ t) t₁)    <S (Left t₁ s , t)

    -- and the relation is well founded
    mutual
      accR : ∀ (n : ℕ) (t₁ : PTree n) (s : FStack n) (t : PTree (diffFS s)) → Acc [ n ]_<S_ (s , t)
                                                                          → (∀ y  → [ 1 + n ] y <S (Right t₁ s , t) → Acc ([ 1 + n ]_<S_) y)
      accR n t₁ s t (acc rs) (.(Right t₁ _) , y) (<S-Right-Step p) = acc (accR n t₁ _ y (rs _ p))

      accL : ∀ (n : ℕ) (t₁ : PTree n) (s : FStack n) (t : PTree (diffFS s)) → Acc [ n ]_<S_ (s , t) → (∀ y → [ suc n ] y <S (Left t₁ s , t) → Acc ([_]_<S_ (suc n)) y)
      accL n t₁ s t (acc rs) (Top , .(Node (plug (s , t)) t₁)) <S-Left-Base = acc (accT n (Node (plug (s , t)) t₁))
      accL n t₁ s t (acc rs) (Left .t₁ stk , y) (<S-Left-Step p) = acc (accL n t₁ stk y (rs (stk , y) p))
      accL n .(plug (stk , y)) s t (acc rs) (Right .(plug (s , t)) stk , y) <S-Right-Left = acc (accR n (plug (s , t)) stk y (<S-WF n (stk , y)))

      accT : ∀ (n : ℕ) (t : PTree (1 + n)) → (∀ y  → [ 1 + n ] y <S (Top , t) → Acc ([ 1 + n ]_<S_) y)
      accT n t (Top , y) ()
      accT n t (Left x₁ stk , y) ()
      accT n .(Node x₁ (plug (stk , y))) (Right x₁ stk , y) <S-Right-Base = acc (accR n x₁ stk y (<S-WF n (stk , y)))

      <S-WF : ∀ n → Well-founded ([ n ]_<S_)
      <S-WF n x = acc (aux n x)
        where
          aux : (n : ℕ) (x y : FStack+PTree n) → [ n ] y <S x → Acc ([_]_<S_ n) y
          aux zero x y ()
          aux (suc n) (Top , .(Node _ (plug (_ , y)))) (.(Right _ _) , y) <S-Right-Base = acc (accR n _ _ y (<S-WF n (_ , y)))
          aux (suc n) (Left x₁ s , t) (_ , _) (<S-Left-Step p)            = acc (accL n x₁ _ _ (aux n (s , t) _ p))
          aux (suc n) (Left .(plug (_ , _)) s , t) (_ , _) <S-Right-Left = acc (accR n (plug (s , t)) _ _ (<S-WF n (_ , _)))
          aux (suc n) (Left x₁ s , t) (_ , _) <S-Left-Base                = acc (accT n (Node (plug (s , t)) x₁))
          aux (suc n) (Right x₁ s , t) (_ , _) (<S-Right-Step p) = acc (accR n x₁ _ _ (aux n (s , t) _ p))
\end{code}
