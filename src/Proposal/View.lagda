\begin{code}
module Proposal.View where

  open import Data.Nat
  open import Data.Product
  open import Relation.Binary
  open import Relation.Nullary
  open import Induction.WellFounded

  data Tree : Set where
    Leaf  : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  -- structural view biased to the right relation on trees
  data _≣_ : Tree → Tree → Set where
    ≣-Leaf : ∀ {a b}                   → Leaf a     ≣ Leaf b
    ≣-Node : ∀ {t₁ t₂ s₁ s₂} → t₂ ≣ s₂ → Node t₁ t₂ ≣ Node s₁ s₂

  ≣-Node-Inj : ∀ {t₁ t₂ s₁ s₂} → Node t₁ t₂ ≣ Node s₁ s₂ → t₂ ≣ s₂
  ≣-Node-Inj (≣-Node x) = x

  infixl 15 _≣_

  ≣-reflexive : Reflexive _≣_
  ≣-reflexive {Leaf x}    = ≣-Leaf
  ≣-reflexive {Node _ x}  = ≣-Node  ≣-reflexive

  ≣-transitive : Transitive _≣_
  ≣-transitive ≣-Leaf ≣-Leaf         = ≣-Leaf
  ≣-transitive (≣-Node a) (≣-Node x) = ≣-Node (≣-transitive a x)

  ≣-symmetric : Symmetric _≣_
  ≣-symmetric ≣-Leaf     = ≣-Leaf
  ≣-symmetric (≣-Node a) = ≣-Node (≣-symmetric a)

  ≣-decidable : Decidable _≣_
  ≣-decidable (Leaf x) (Leaf x₁)    = yes ≣-Leaf
  ≣-decidable (Leaf x) (Node y y₁)  = no (λ ())
  ≣-decidable (Node x x₁) (Leaf x₂) = no (λ ())
  ≣-decidable (Node _ x) (Node _ y) with ≣-decidable x y
  ≣-decidable (Node _ x) (Node _ y) | yes p = yes (≣-Node p)
  ≣-decidable (Node _ x) (Node _ y) | no ¬p = no λ x → ¬p (≣-Node-Inj x)

  data Stack : Set where
    Left  : ∀ (t : Tree) → Stack → Stack
    Right : ∀ (n : ℕ)    → Stack → Stack
    Top   : Stack

  _⊲_  : Tree → Stack → Tree
  t ⊲ Left  t₁ s = Node (t ⊲ s) t₁
  t ⊲ Right n  s = Node (Leaf n) (t ⊲ s)
  t ⊲ Top        = t

  data _<S_ : Tree × Stack → Tree × Stack → Set where

    <S-Right-Step : ∀ {n t₁ t₂ s₁ s₂}      →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Right n s₁) <S  (t₂ , Right n s₂)

    <S-Left-Step  : ∀ {t t₁ t₂ s₁ s₂}      →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Left t s₁)  <S (t₂ , Left t s₂)

    <S-Right-Left : ∀ {t₁ t₂ s₁ s₂} {a b}  → b ≣ t₁ ⊲ s₁ → (t₁ , Right a s₁) <S (t₂ , Left b s₂)

    <S-Right-Base : ∀ {t t₁ s₁} {t₂ n}     → t₂ ≣ (t ⊲ s₁) → (t , Right n s₁) <S (Node t₁ t₂ , Top)

    <S-Left-Base  : ∀ {t t₁ s₁} {t₂}       → t₂ ≣ (t ⊲ s₁) → (Node t₂ t₁ , Top) <S (t , Left t₁ s₁)

  related : ∀ t₁ s₁ t₂ s₂ →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊲ s₁ ) ≣ (t₂ ⊲ s₂)
  related t₁ (Left t s₁) t₂ .(Left t _) (<S-Left-Step x) = ≣-Node ≣-reflexive
  related t₁ (Right n s₁) t₂ .(Right n _) (<S-Right-Step x) = ?
  related t₁ (Right n s₁) t₂ .(Left _ _) (<S-Right-Left x) = ?
  related t₁ (Right n s₁) .(Node _ _) .Top (<S-Right-Base x) = ?
  related t₁ Top t₂ s₂ x = {!!}
\end{code}
