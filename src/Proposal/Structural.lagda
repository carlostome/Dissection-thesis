\begin{code}
module Proposal.Structural where

  open import Data.Nat
  open import Data.Product
  open import Relation.Binary
  open import Relation.Nullary
  open import Induction.WellFounded

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

    <S-Right-Step : ∀ {t t₁ t₂ s₁ s₂}      → (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Right t s₁) <S  (t₂ , Right t s₂)

    <S-Left-Step  : ∀ {t t₁ t₂ s₁ s₂}      → (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Left t s₁)  <S (t₂ , Left t s₂)

    <S-Right-Left : ∀ {t₁ t₂ s₁ s₂} {a b}  → a ≣ t₂ ⊲ s₂   → b ≣ t₁ ⊲ s₁ → (t₁ , Right a s₁) <S (t₂ , Left b s₂)

    <S-Right-Base : ∀ {t t₁ s₁} {t₂}       → t₂ ≣ (t ⊲ s₁)                → (t , Right t₁ s₁) <S (Node t₁ t₂ , Top)

    <S-Left-Base  : ∀ {t t₁ s₁} {t₂}       → t₂ ≣ (t ⊲ s₁) → (Node t₂ t₁ , Top) <S (t , Left t₁ s₁)

  related : ∀ t₁ s₁ t₂ s₂ →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊲ s₁ ) ≣ (t₂ ⊲ s₂)
  related t₁ (Left t s₁) t₂ .(Left t _) (<S-Left-Step x)      = ≣-Node (related t₁ s₁ t₂ _ x) ≣-reflexive
  related t₁ (Right t s₁) t₂ .(Right t _) (<S-Right-Step x)   = ≣-Node ≣-reflexive (related t₁ s₁ t₂ _ x)
  related t₁ (Right t s₁) t₂ .(Left _ _) (<S-Right-Left x x₁) = ≣-Node x (≣-symmetric x₁)
  related t₁ (Right t s₁) .(Node t _) .Top (<S-Right-Base x)  = ≣-Node ≣-reflexive (≣-symmetric x)
  related .(Node _ _) Top t₂ .(Left _ _) (<S-Left-Base x)     = ≣-Node x ≣-reflexive

  data [_]ₛ_<_ : Tree → Tree × Stack → Tree × Stack → Set where
    lt :  ∀ t t×s t×s′ → (eq₁ : plug-⊲ t×s ≣ t) → (eq₂ : plug-⊲ t×s′ ≣ t) → (p : t×s <S t×s′) → [ t ]ₛ t×s < t×s′

  mutual
    accR : ∀ t t₁ y s₁ → t₁ ≣ s₁ → Acc ([ t ]ₛ_<_) y → WfRec ([ Node s₁ t ]ₛ_<_ ) (Acc ([ Node s₁ t ]ₛ_<_ )) (proj₁ y , Right t₁ (proj₂ y))
    accR t t₁ (y , s) s₁ x (acc rs) .(t₂ , Right t₁ s₂) (lt .(Node s₁ t) .(t₂ , Right t₁ s₂) .(y , Right t₁ s) eq₁ eq₂ (<S-Right-Step {t₁ = t₂} {s₁ = s₂} p))
      = acc (accR t t₁ (t₂ , s₂) s₁ x (rs (t₂ , s₂) (lt t (t₂ , s₂) (y , s) (proj₂ (≣-Node-Inj eq₁)) (proj₂ (≣-Node-Inj eq₂)) p)))

    accL : ∀ t t₁ y s₁ → t₁ ≣ s₁ → Acc ([ t ]ₛ_<_) y → WfRec ([_]ₛ_<_ (Node t s₁)) (Acc ([_]ₛ_<_ (Node t s₁))) (proj₁ y , Left t₁ (proj₂ y))
    accL t t₁ (y , s) s₁ x (acc rs) .(t₂ , Left t₁ s₂) (lt .(Node t s₁) .(t₂ , Left t₁ s₂) .(y , Left t₁ s) eq₁ eq₂ (<S-Left-Step {t₁ = t₂} {s₁ = s₂} p))
      = acc (accL t t₁ (t₂ , s₂) s₁ x (rs (t₂ , s₂) (lt t (t₂ , s₂) (y , s) (proj₁ (≣-Node-Inj eq₁)) (proj₁ (≣-Node-Inj eq₂)) p)))
    accL t t₁ (y , s) s₁ x (acc rs) .(_ , Right _ _) (lt .(Node t s₁) .(_ , Right _ _) .(y , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Right-Left x₂ x₃)) = acc (accR s₁ _ (_ , _) t eq₁ (<S-WF s₁ (_ , _)))
    accL t t₁ (y , s) s₁ x (acc rs) .(Node _ t₁ , Top) (lt .(Node t s₁) .(Node _ t₁ , Top) .(y , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Left-Base x₂)) = acc (accH t s₁ _ t₁ eq₁ eq₃)

    accH : ∀ s₁ s₂ t₁ t₂ → t₁ ≣ s₁ → t₂ ≣ s₂ → WfRec ([_]ₛ_<_ (Node s₁ s₂)) (Acc ([_]ₛ_<_ (Node s₁ s₂))) (Node t₁ t₂ , Top)
    accH s₁ s₂ t₁ t₂ x x₁ .(_ , Right t₁ _) (lt .(Node s₁ s₂) .(_ , Right t₁ _) .(Node t₁ t₂ , Top) (≣-Node eq₁ eq₃) eq₂ (<S-Right-Base x₂)) = acc (accR s₂ t₁ _ s₁ eq₁ (<S-WF s₂ (_ , _)))

    <S-WF : ∀ t → Well-founded ([ t ]ₛ_<_)
    <S-WF t x = acc (aux t x)
      where aux : ∀ t x → WfRec ([_]ₛ_<_ t) (Acc ([_]ₛ_<_ t)) x
            aux .(Node _ _) (x , Left t₁ s) .(t₂ , Left t₁ s₂) (lt .(Node _ _) .(t₂ , Left t₁ s₂) .(x , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Left-Step {t₁ = t₂} {s₁ = s₂} p)) = acc (accL _ t₁ (t₂ , s₂) _ eq₃ (<S-WF _ (t₂ , s₂)))
            aux .(Node _ _) (x , Left t₁ s) .(_ , Right _ _) (lt .(Node _ _) .(_ , Right _ _) .(x , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Right-Left x₂ x₃)) = acc (accR _ _ _ _ eq₁ (<S-WF _ (_ , _)))
            aux .(Node _ _) (x , Left t₁ s) .(Node _ t₁ , Top) (lt .(Node _ _) .(Node _ t₁ , Top) .(x , Left t₁ s) (≣-Node eq₁ eq₃) eq₂ (<S-Left-Base x₂)) = acc (accH _ _ _ t₁ (eq₁) (eq₃))
            aux .(Node _ _) (x , Right t₁ s) .(t₂ , Right t₁ s₁) (lt .(Node _ _) .(t₂ , Right t₁ s₁) .(x , Right t₁ s) (≣-Node eq₁ eq₄) (≣-Node eq₂ eq₃) (<S-Right-Step {t₁ = t₂} {s₁ = s₁} p)) = acc (accR _ t₁ (t₂ , s₁) _ eq₂ (<S-WF _ (t₂ , s₁)))
            aux .(Node _ _) (.(Node _ _) , Top) .(_ , Right _ _) (lt .(Node _ _) .(_ , Right _ _) .(Node _ _ , Top) (≣-Node eq₁ eq₃) eq₂ (<S-Right-Base x₁)) = acc (accR _ _ _ _ eq₁ (<S-WF _ _))
\end{code}
