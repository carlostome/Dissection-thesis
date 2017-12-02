\begin{code}
module Proposal.Subtree where

  open import Induction.WellFounded
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Function
  open import Relation.Unary
  open import Relation.Binary

  data Tree : Set where
    Tip  : Tree
    Node : Tree → Tree → Tree

  data Subtree : Tree → Tree → Set where
    Base-l : ∀ {t₁ t₂}     → Subtree t₁ (Node t₁ t₂)
    Base-r : ∀ {t₁ t₂}     → Subtree t₂ (Node t₁ t₂)
    Step-l   : ∀ {t t₁ t₂} → Subtree t t₁ → Subtree t (Node t₁ t₂)
    Step-r   : ∀ {t t₁ t₂} → Subtree t t₂ → Subtree t (Node t₁ t₂)

  Subtree-WF : Well-founded Subtree
  Subtree-WF x = acc (aux x)
    where
      aux : ∀ (x : Tree) → (∀ y → Subtree y x → Acc Subtree y)
      aux Tip y ()
      aux (Node t₁ t₂) .t₁ Base-l = Subtree-WF t₁
      aux (Node t₁ t₂) .t₂ Base-r = Subtree-WF t₂
      aux (Node t₁ t₂) y (Step-l p) = aux t₁ y p
      aux (Node t₁ t₂) y (Step-r p) = aux t₂ y p

  lemma : ∀ {t₁ t₂ t} → t₁ ≡ t₂ → Subtree t₁ t → Subtree t₂ t
  lemma refl x₁ = x₁

  lem : ∀ {x y t} → x ≡ y → Acc Subtree (Node x t) → Acc Subtree (Node y t)
  lem refl x = x

  data Stack : Set where
    Left  : ∀ (t : Tree) → Stack → Stack
    Right : ∀ (t : Tree) → Stack → Stack
    Top   : Stack

  _⊳_ : Tree → Stack → Tree
  t ⊳ Top       = t
  t ⊳ Left x s  = Node (t ⊳ s) x
  t ⊳ Right x s = Node x (t ⊳ s)

  plug : Tree × Stack → Tree
  plug (t , stk) = t ⊳ stk

  data _<S_ : Tree × Stack → Tree × Stack → Set where
    <S-Right-Step : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Right t s₁) <S  (t₂ , Right t s₂)

    <S-Left-Step  : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Left t s₁) <S (t₂ , Left t s₂)

    -- <S-Right-Left : ∀ {t₁ t₂ s₁ s₂}   → (t₁ , Right (t₂ ⊳ s₂) s₁) <S (t₂ , Left (t₁ ⊳ s₁) s₂)

    <S-Right-Base : ∀ {t t₁ s₁}       → (t , Right t₁ s₁) <S (Node t₁ (t ⊳ s₁) , Top)

    <S-Left-Base  : ∀ {t t₁ s₁}       → (Node (t ⊳ s₁) t₁ , Top)    <S (t , Left t₁ s₁)

  related : ∀ {t₁ s₁ t₂ s₂} → (t₁ , s₁) <S (t₂ , s₂) → plug (t₁ , s₁ ) ≡ plug (t₂ , s₂)
  related (<S-Right-Step x) = cong (λ t → Node _ t) (related x)
  related (<S-Left-Step x)  = cong ((λ t → Node t _)) (related x)
  related <S-Right-Base     = refl
  related <S-Left-Base      = refl

  open Deprecated-inspect renaming (inspect to inspect′)

  mutual
    accR : ∀ (t : Tree) (t₁ : Tree) (s₁ : Stack)→ Acc _<S_ (t , s₁) → (∀ y  → y <S (t , Right t₁ s₁) → Acc (_<S_) y)
    accR t t₁ s₁ (acc rs) .(_ , Right t₁ _) (<S-Right-Step p) = acc (accR _ t₁ _ (rs _ p))

    accL : ∀ (t₁ : Tree) (t : Tree) (s₁ : Stack) → Acc Subtree (Node (t ⊳ s₁) t₁) → Acc _<S_ (t , s₁) → (∀ y → y <S (t , Left t₁ s₁) → Acc (_<S_) y)
    accL t₁ t s₁ r (acc rs) (y , .(Left t₁ s₂)) (<S-Left-Step {s₁ = s₂} p) with related p
    ... | rp with inspect′ (y ⊳ s₂) | inspect′ (t ⊳ s₁)
    accL t₁ t s₁ r (acc rs) (y , .(Left t₁ s)) (<S-Left-Step {s₁ = s} p) | eq | y₁ with-≡ eq₁ | y₂ with-≡ eq₂ with trans (trans (sym eq₁) eq) eq₂
    accL t₁ t s₁ r (acc rs) (y , .(Left t₁ s)) (<S-Left-Step {s₁ = s} p) | eq | .(y ⊳ s) with-≡ refl | .(y ⊳ s) with-≡ eq₂ | refl
      = acc (accL {!!} {!!} {!!} {!r!} (rs (y , s) p)) -- acc (accL {!!} {!!} {!!} {!r!} (rs (y , s) p)) -- acc (accL {!!} {!!} {!!} {!r!} (rs (y , s₂) p))
    accL t₁ t s₁ (acc r) (acc rs) (.(Node (t ⊳ s₁) t₁) , .Top) <S-Left-Base =
      acc λ { (x , Left t s) ()
            ; (x , Right .(t ⊳ s₁) s) <S-Right-Base → acc (accR x (t ⊳ s₁) s (<S-WF (x , s) (r (x ⊳ s) Base-r)))
            ; (x , Top) ()}

    accT : ∀ t → Acc Subtree t → (∀ y → y <S (t , Top) → Acc (_<S_) y)
    accT t ac (t′ , Left t₁ s) ()
    accT .(Node t₁ (t′ ⊳ s)) (acc rs) (t′ , Right t₁ s) <S-Right-Base = acc (accR t′ t₁ s (<S-WF (t′ , s) (rs (t′ ⊳ s) Base-r)))
    accT t ac (t′ , Top) ()

    aux : (x : Tree × Stack) → Acc Subtree (plug x) → (y : Tree × Stack) → y <S x → Acc (_<S_) y
    aux (t , Left t₁ s) (acc rs) (y , Left .t₁ s′) (<S-Left-Step p) = acc (accL t₁ y s′ {!!}  (aux (t , s) (rs (t ⊳ s) Base-l) (y , s′) p))
    aux (t , Left t₁ s) (acc rs) (y , Right t₂ s′) ()
    aux (t , Left t₁ s) (acc rs) (.(Node (t ⊳ s) t₁) , Top) <S-Left-Base =
      acc λ { (y , Left t s′) ()
            ; (y , Right .(t ⊳ s) s′) <S-Right-Base → acc (accR y (t ⊳ s) s′ (<S-WF (y , s′) (rs (y ⊳ s′) Base-r)))
            ; (y , Top) ()}
    aux (t , Right t₁ s) (acc rs) (y , .(Right t₁ _)) (<S-Right-Step p)   = acc (accR y t₁ _ (aux (t , s) (rs (t ⊳ s) Base-r) (y , _) p))
    aux (t , Top) rs (y , Left t₁ s′) ()
    aux (.(Node t₁ (y ⊳ s′)) , Top) (acc rs) (y , Right t₁ s′) <S-Right-Base = acc (accR y t₁ s′ (<S-WF (y , s′) (rs (y ⊳ s′) Base-r)))
    aux (t , Top) rs (y , Top) ()

    <S-WF : ∀ x → Acc Subtree (plug x) → Acc (_<S_) x
    <S-WF x ac = acc (aux x ac)

\end{code}

