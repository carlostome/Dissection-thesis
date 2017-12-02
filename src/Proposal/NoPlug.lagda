\begin{code}
module Proposal.NoPlug where

  open import Data.Nat
  open import Data.Product
  open import Relation.Binary
  open import Relation.Nullary
  open import Induction.WellFounded
  open import Relation.Binary.PropositionalEquality

  data Tree : Set where
    Leaf  : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  -- structural equality relation on trees
  data _≣_ : Tree → Tree → Set where
    ≣-Leaf : ∀ {a b}         → Leaf a ≣ Leaf b
    ≣-Node : ∀ {t₁ t₂ s₁ s₂} → t₁ ≣ s₁ → t₂ ≣ s₂ → Node t₁ t₂ ≣ Node s₁ s₂

  ≣-Node-Inj : ∀ {t₁ t₂ s₁ s₂} → Node t₁ t₂ ≣ Node s₁ s₂ → t₁ ≣ s₁ × t₂ ≣ s₂
  ≣-Node-Inj (≣-Node a b) = a , b

  infixl 15 _≣_

  ≣-reflexive : Reflexive _≣_
  ≣-reflexive {Leaf x}    = ≣-Leaf
  ≣-reflexive {Node x x₁} = ≣-Node ≣-reflexive ≣-reflexive

  ≣-transitive : Transitive _≣_
  ≣-transitive ≣-Leaf ≣-Leaf             = ≣-Leaf
  ≣-transitive (≣-Node a b) (≣-Node x y) = ≣-Node (≣-transitive a x) (≣-transitive b y)

  ≣-symmetric : Symmetric _≣_
  ≣-symmetric ≣-Leaf       = ≣-Leaf
  ≣-symmetric (≣-Node a b) = ≣-Node (≣-symmetric a) (≣-symmetric b)

  ≣-decidable : Decidable _≣_
  ≣-decidable (Leaf x) (Leaf x₁)    = yes ≣-Leaf
  ≣-decidable (Leaf x) (Node y y₁)  = no (λ ())
  ≣-decidable (Node x x₁) (Leaf x₂) = no (λ ())
  ≣-decidable (Node x x₁) (Node y y₁) with ≣-decidable x y | ≣-decidable x₁ y₁
  ≣-decidable (Node x x₁) (Node y y₁) | yes p | yes p₁ = yes (≣-Node p p₁)
  ≣-decidable (Node x x₁) (Node y y₁) | yes p | no ¬p  = no λ x → ¬p (proj₂ (≣-Node-Inj x))
  ≣-decidable (Node x x₁) (Node y y₁) | no ¬p | yes p  = no λ x → ¬p (proj₁ (≣-Node-Inj x))
  ≣-decidable (Node x x₁) (Node y y₁) | no ¬p | no ¬p₁ = no λ x → ¬p (proj₁ (≣-Node-Inj x))

  data Stack : Set where
    Left  : ∀ (t : Tree) → Stack → Stack
    Right : ∀ (t : Tree) → Stack → Stack
    Top   : Stack

  _⊲_  : Tree → Stack → Tree
  t ⊲ Left  t₁ s = Node (t ⊲ s) t₁
  t ⊲ Right t₁ s = Node t₁ (t ⊲ s)
  t ⊲ Top        = t

  plug-⊲ : Tree × Stack → Tree
  plug-⊲ (t , s) = t ⊲ s

  data _<S_ : Tree × Stack → Tree × Stack → Set where

    <S-Right-Step : ∀ {x y t₁ t₂ s₁ s₂}      → (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Right x s₁) <S  (t₂ , Right y s₂)

    <S-Left-Step  : ∀ {x y t₁ t₂ s₁ s₂}      → (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Left x s₁)  <S (t₂ , Left y s₂)

    <S-Right-Left : ∀ {t₁ t₂ s₁ s₂} {a b}    → (t₁ , Right a s₁) <S (t₂ , Left b s₂)

    <S-Right-Base : ∀ {t x y s₁} {t₂}        → (t , Right x s₁)  <S (Node y t₂ , Top)

    <S-Left-Base  : ∀ {t x y s₁} {t₂}        → (Node t₂ x , Top) <S (t , Left y s₁)


  data _<'_ : Tree × Stack → Tree × Stack → Set where
    lt :  ∀ t×s t×s′ → plug-⊲ t×s ≣ plug-⊲ t×s′ → t×s <S t×s′ → t×s <' t×s′

  mutual
    accR : ∀ t₁ x s₁ → t₁ ≣ s₁ → Acc (_<'_) x → WfRec (_<'_ ) (Acc (_<'_ )) (proj₁ x , Right t₁ (proj₂ x))
    accR t₁ (x , s) s₁ st (acc rs) .(_ , Right _ _) (lt .(_ , Right _ _) .(x , Right t₁ s) (≣-Node x₁ x₂) (<S-Right-Step p))
      = acc (accR _ (_ , _) s₁ (≣-transitive x₁ st) (rs (_ , _) (lt (_ , _) (x , s) x₂ p)))

  --   accL : ∀ t t₁ y s₁ → t₁ ≣ s₁ → Acc ([ t ]ₛ_<_) y → WfRec ([_]ₛ_<_ (Node t s₁)) (Acc ([_]ₛ_<_ (Node t s₁))) (proj₁ y , Left t₁ (proj₂ y))
  --   accL t t₁ y s₁ x x₁ z x₂ = {!!}
  --   -- accL t t₁ (y , s) s₁ x (acc rs) .(t₂ , Left t₁ s₂) (lt .(Node t s₁) .(t₂ , Left t₁ s₂) .(y , Left t₁ s) eq₁ eq₂ (<S-Left-Step {t₁ = t₂} {s₁ = s₂} p))
  --   --   = acc (accL t t₁ (t₂ , s₂) s₁ x (rs (t₂ , s₂) (lt t (t₂ , s₂) (y , s) (proj₁ (≣-Node-Inj eq₁)) (proj₁ (≣-Node-Inj eq₂)) p)))
  --   -- accL t t₁ (y , s) s₁ x (acc rs) .(_ , Right _ _) (lt .(Node t s₁) .(_ , Right _ _) .(y , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Right-Left x₂ x₃)) = acc (accR s₁ _ (_ , _) t eq₁ (<S-WF s₁ (_ , _)))
  --   -- accL t t₁ (y , s) s₁ x (acc rs) .(Node _ t₁ , Top) (lt .(Node t s₁) .(Node _ t₁ , Top) .(y , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Left-Base x₂)) = acc (accH t s₁ _ t₁ eq₁ eq₃)

  --   accH : ∀ s₁ s₂ t₁ t₂ → t₁ ≣ s₁ → t₂ ≣ s₂ → WfRec ([_]ₛ_<_ (Node s₁ s₂)) (Acc ([_]ₛ_<_ (Node s₁ s₂))) (Node t₁ t₂ , Top)
  --   accH s₁ s₂ t₁ t₂ x x₁ .(_ , Right _ _) (lt .(Node s₁ s₂) .(_ , Right _ _) .(Node t₁ t₂ , Top) (≣-Node eq₁ eq₃) eq₂ <S-Right-Base) = acc (accR s₂ _ _ s₁ eq₁ (<S-WF s₂ _))

    <S-WF : ∀ x t → (t ≣ plug-⊲ x) → Acc (_<'_) x
    <S-WF x t p = acc (aux t x p)
      where aux : ∀ (t : Tree) → (x : Tree × Stack) → (t ≣ plug-⊲ x) → WfRec (_<'_) (Acc (_<'_)) x
            aux .(Node _ _) (x , Left t₁ s) (≣-Node eq eq₁) .(_ , Left _ _) (lt .(_ , Left _ _) .(x , Left t₁ s) (≣-Node st st₁) (<S-Left-Step p)) = {!!}
            aux .(Node _ _) (x , Left t₁ s) (≣-Node eq eq₁) .(t₂ , Right a s₂) (lt .(t₂ , Right a s₂) .(x , Left t₁ s) (≣-Node st st₁) (<S-Right-Left {t₁ = t₂} {s₁ = s₂} {a = a}))
              = acc (accR _ _ (x ⊲ s) st (<S-WF (t₂ , s₂) t₁ ({!≣-symmetric st₁!})))
            aux .(Node _ _) (x , Left t₁ s) (≣-Node eq eq₁) .(Node _ _ , Top) (lt .(Node _ _ , Top) .(x , Left t₁ s) st <S-Left-Base) = {!!}
            aux t (x , Right t₁ s) eq y p = {!!}
            aux t (x , Top) eq y p = {!!}
  --           aux .(Node _ _) (x , Left t₁ s) .(_ , Left _ _) (lt .(Node _ _) .(_ , Left _ _) .(x , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Left-Step p)) = acc (accL _ _ (.t₁ , .s₁) .s₃ eq₃ (<S-WF .s₂ (.t₁ , .s₁)))
  --           aux .(Node _ _) (x , Left t₁ s) .(_ , Right _ _) (lt .(Node _ _) .(_ , Right _ _) .(x , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ <S-Right-Left) = acc (accR _ _ _ _ eq₁ (<S-WF _ _))
  --           aux .(Node _ _) (x , Left t₁ s) .(Node _ _ , Top) (lt .(Node _ _) .(Node _ _ , Top) .(x , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ <S-Left-Base) = acc (accH _ _ _ _ eq₁ eq₃)
  --           aux .(Node _ _) (x , Right t₁ s) .(_ , Right _ _) (lt .(Node _ _) .(_ , Right _ _) .(x , Right t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Right-Step p)) = acc (accR _ _ _ _ eq₁ (<S-WF _ _))
  --           aux .(Node _ _) (.(Node _ _) , Top) .(_ , Right _ _) (lt .(Node _ _) .(_ , Right _ _) .(Node _ _ , Top) (≣-Node eq₁ eq₃) eq₂ <S-Right-Base) = acc (accR _ _ _ _ eq₁ (<S-WF _ (_ , _)))

\end{code}
