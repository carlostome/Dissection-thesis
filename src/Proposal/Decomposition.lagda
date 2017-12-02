\begin{code}
module Proposal.Decomposition where

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

  Node≡-r : ∀ {t t₁ t₂} → t₁ ≡ t₂ → Node t t₁ ≡ Node t t₂
  Node≡-r refl = refl

  Node≡-l : ∀ {t t₁ t₂} → t₁ ≡ t₂ → Node t₁ t ≡ Node t₂ t
  Node≡-l refl = refl

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

  data Dec : (t : Tree) → Set where
    _,_ : ∀ (t : Tree) → (s : Stack) → Dec (t ⊳ s)

  [_]_<D_ : (t : Tree) → Dec t → Dec t → Set
  [ .(Node (Node (t ⊳ s) t₂) t₁) ] t , Left t₁ (Left t₂ s) <D d₂ = {!d₂!}
  [ .(Node (Node t₂ (t ⊳ s)) t₁) ] t , Left t₁ (Right t₂ s) <D d₂ = {!!}
  [ .(Node t t₁) ] t , Left t₁ Top <D d₂ = {!!}
  [ .(Node t₁ (t ⊳ s)) ] t , Right t₁ s <D d₂ = {!!}
  [ .t ] t , Top <D d₂ = {!!}
  -- data [_]_<D_ : (t : Tree) → Dec t → Dec t → Set where
  --   <S-Right-Step : ∀ {t t₁ t₂ s₁ s₂ t′} → (eq1 : t₁ ⊳ s₁ ≡ t′) (eq2 : t₂ ⊳ s₂ ≡ t′)
  --                 → [ (t₁ ⊳ s₁) ] (t₁ , s₁) <D (t₂ , s₂)
  --                 → [ Node t t′ ] (t₁ , Right t s₁ ) <D  (t₂ , Right t s₂)

  --   <S-Left-Step  : ∀ {t t₁ t₂ s₁ s₂ t′} → (eq1 : t₁ ⊳ s₁ ≡ t′) (eq2 : t₂ ⊳ s₂ ≡ t′)
  --                 → [ t′ ] (t₁ , s₁ =| eq1) <D (t₂ , s₂ =| eq2) → [ Node t′ t ] (t₁ , Left t s₁ =| Node≡-l eq1) <D (t₂ , Left t s₂ =| Node≡-l eq2)

  --   <S-Right-Left : ∀ {t₁ t₂ s₁ s₂} → (eq : Node (t₂ ⊳ s₂) (t₁ ⊳ s₁) ≡ Node (t₂ ⊳ s₂) (t₁ ⊳ s₁))
  --                 → [ Node (t₂ ⊳ s₂) (t₁ ⊳ s₁) ] (t₁ , Right (t₂ ⊳ s₂) s₁ =| eq) <D (t₂ , Left (t₁ ⊳ s₁) s₂ =| eq)

  --   <S-Right-Base : ∀ {t t₁ s₁} → (eq : Node t₁ (t ⊳ s₁) ≡ Node t₁ (t ⊳ s₁))
  --                 → [ Node t₁ (t ⊳ s₁) ](t , Right t₁ s₁ =| eq) <D (Node t₁ (t ⊳ s₁) , Top =| eq)

  --   <S-Left-Base  : ∀ {t t₁ s₁} → (eq : Node (t ⊳ s₁) t₁ ≡ Node (t ⊳ s₁) t₁)
  --                 → [ Node (t ⊳ s₁) t₁ ] (Node (t ⊳ s₁) t₁ , Top =| eq) <D (t , Left t₁ s₁ =| eq)

  -- <S-WF : ∀ t → Well-founded ([ t ]_<D_)
  -- <S-WF t x = acc (aux t x)
  --   where
  --     aux : (t : Tree) → (x : Dec t) → WfRec ([ t ]_<D_) (Acc ([ t ]_<D_)) x
  --     aux t (t′ , Left t₁ s  =| eq) y p = {!!}
  --     aux t (t′ , Right t₁ s =| eq) y p = {!!}
  --     aux .(Node (t′ ⊳ s) t) (.(Node (t′ ⊳ s) t) , Top =| refl) (t′ , Left t s =| refl) p  = {!!}
  --     aux .(Node t (t′ ⊳ s)) (.(Node t (t′ ⊳ s)) , Top =| refl) (t′ , Right t s =| refl) p = {!!}
  --     aux .t′ (.t′ , Top =| refl) (t′ , Top =| refl) ()
    -- where
    --   aux : (x y : Tree × Stack) → y <S x → Acc (_<S_) y
    --   aux (t , Left t₁ stk) (y , Left t₂ s) p  = {!!}
    --   aux (t , Left t₁ stk) (y , Right t₂ s) p = {!!}
    --   aux (t , Left t₁ stk) (.(Node (t ⊳ stk) t₁) , Top) <S-Left-Base = {!!}
    --   aux (t , Right t₁ stk) .(_ , Right t₁ _) (<S-Right-Step p) = acc (accR _ t₁ _ (aux (t , stk) _ p))
    --   aux (t , Top) (t′ , Left t₁ stk) ()
    --   aux (.(Node t₁ (t′ ⊳ stk)) , Top) (t′ , Right t₁ stk) <S-Right-Base = acc (accR {!!} {!!} {!!} {!<S-WF!})
    --   aux (t , Top) (t′ , Top) ()
    -- related : ∀ t₁ s₁ t₂ s₂ →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊳ s₁ ) ≡ (t₂ ⊳ s₂)
    -- related t₁ Top t₂ Top ()
    -- related .(Node (t₂ ⊳ s₂) x₁) Top t₂ (Left x₁ s₂) <S-Left-Base = refl
    -- related t₁ Top t₂ (Right x₁ s₂) ()
    -- related t₁ (Left x₁ s₁) t₂ Top ()
    -- related t₁ (Left x₁ s₁) t₂ (Left .x₁ s₂) (<S-Left-Step x) = cong (λ x → Node x x₁) (related t₁ s₁ t₂ s₂ x)
    -- related t₁ (Left x₁ s₁) t₂ (Right x₂ s₂) ()
    -- related t₁ (Right x₁ s₁) .(Node x₁ (t₁ ⊳ s₁)) Top <S-Right-Base = refl
    -- related t₁ (Right .(t₂ ⊳ s₂) s₁) t₂ (Left .(t₁ ⊳ s₁) s₂) <S-Right-Left = refl
    -- related t₁ (Right x₁ s₁) t₂ (Right .x₁ s₂) (<S-Right-Step p) = cong (λ x → Node x₁ x) (related t₁ s₁ t₂ s₂ p)

    -- accO : ∀ {t s t′ s′} → Acc _<S_ (t , s) → (t ⊳ s) ≡ (t′ ⊳ s′) → Acc _<S_ (t′ , s′)
    -- accO {s = Left t s} {s′ = Left t₁ s′} x eq  with Node-inj eq
    -- accO {_} {Left t s} {_} {Left .t s′} (acc rs) eq | proj₃ , refl =
    --   acc λ { (y , Left t ss) x → {!!}
    --         ; (y , Right t ss) x → {!!}
    --         ; (y , Top) x → {!!}}
    -- accO {s = Left t s} {s′ = Right t₁ s′} x x₁ = {!!}
    -- accO {s = Left t s} {s′ = Top} x x₁ = {!!}
    -- accO {s = Right t s} {s′ = s′} x x₁ = {!!}
    -- accO {s = Top} {s′ = s′} x x₁ = {!!}

    -- mutual
    --   accR : ∀ (t : Tree) (t₁ : Tree) (s₁ : Stack)→ Acc _<S_ (t , s₁) → (∀ y  → y <S (t , Right t₁ s₁) → Acc (_<S_) y)
    --   accR t t₁ s₁ (acc rs) .(_ , Right t₁ _) (<S-Right-Step p) = acc (accR _ t₁ _ (rs _ p))

    --   accL : ∀ (t₁ : Tree) (t′ : Tree) (s′ : Stack) → t₁ ≡ t′ ⊳ s′ → Acc _<S_ (t′ , s′)
    --        → (t : Tree) (s₁ : Stack) → Acc _<S_ (t , s₁) → (∀ y → y <S (t , Left t₁ s₁) → Acc (_<S_) y)
    --   accL t₁ t′ s′ eq acc1 t s₁ (acc rs) (y , Left .t₁ s) (<S-Left-Step p)        = acc (accL t₁ t′ s′ eq acc1 y s (rs (y , s) p))
    --   accL .(y ⊳ s) t′ s′ eq acc1 t s₁ acc2 (y , Right .(t ⊳ s₁) s) <S-Right-Left = {!!}
    --   accL .(t′ ⊳ s′) t′ s′ refl (acc rs) t s₁ acc2 (.(Node (t ⊳ s₁) (t′ ⊳ s′)) , Top) <S-Left-Base = {!!}

    --   accT : ∀ t′ s′ → Acc _<S_ (t′ , s′) → (t : Tree) → (∀ y → y <S (Node t (t′ ⊳ s′) , Top) → Acc (_<S_) y)
    --   accT t′ s′ x t (y , Left t₁ s) ()
    --   accT t′ s′ ac t (y , Right t₁ s) p with Node-inj (related _ _ _ _ p)
    --   accT t′ s′ ac t (y , Right .t s) p | refl , z = acc (accR {!!} {!!} {!!} {!!})
    --   accT t′ s′ x t (y , Top) ()


\end{code}
