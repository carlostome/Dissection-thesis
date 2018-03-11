\begin{code}
module Thesis.FoldIx where

  open import Data.Nat
  open import Data.List
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Induction.WellFounded

  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  Node-injᵣ : ∀ {l r₁ r₂} → r₁ ≡ r₂ → Node l r₁ ≡ Node l r₂
  Node-injᵣ refl = refl

  Node-injₗ : ∀ {l₁ l₂ r} → l₁ ≡ l₂ → Node l₁ r ≡ Node l₂ r
  Node-injₗ refl = refl

  record TreeAlg (A : Set) : Set where
    field
      TipA  : ℕ → A
      NodeA : A → A → A

  open TreeAlg
  
  treeCata : {A : Set} → TreeAlg A → Tree → A
  treeCata tAlg (Tip n)      = TipA  tAlg n
  treeCata tAlg (Node t₁ t₂) = NodeA tAlg (treeCata tAlg t₁) (treeCata tAlg t₂)

  -- the Stack is parametrized not only by the type of result A
  -- but with the algebra used to compute the result for the trees already
  -- processed
  Stack : (A : Set) → TreeAlg A → Set
  Stack A tAlg = List (Tree ⊎ Σ A λ a → Σ Tree λ t → treeCata tAlg t ≡ a)

  pattern Left t       = inj₁ t
  pattern Right r t p  = inj₂ (r , t , p)

  -- An untyped version of the Zipper
  UZipper : (A : Set) → TreeAlg A → Set
  UZipper A tAlg = ℕ × Stack A tAlg

  plug⇑  : {A : Set} {tAlg : TreeAlg A} → Tree → Stack A tAlg → Tree
  plug⇑ t (Left   t₁ ∷ s)     = plug⇑ (Node t t₁) s
  plug⇑ t (Right  r t₁ p ∷ s) = plug⇑ (Node t₁ t) s
  plug⇑ t []                  = t

  plug⇓ : {A : Set} {tAlg : TreeAlg A} → Tree → Stack A tAlg → Tree
  plug⇓ t []                  = t
  plug⇓ t (Left t₁ ∷ s)       = Node (plug⇓ t s) t₁
  plug⇓ t (Right _ t₁ _ ∷ s)  = Node t₁ (plug⇓ t s)

  -- Zipper is indexed by the tree that is supposed to plug to
  data Zipper (A : Set) (tAlg : TreeAlg A) (t : Tree) : Set where
    _,,_,,_ : (n : ℕ) → (s : Stack A tAlg) → plug⇓ (Tip n) s ≡ t → Zipper A tAlg t

  -- A relation over indexed Zippers
  data [[_]]_<_ {A : Set} {tAlg : TreeAlg A} : (t : Tree)  → Zipper A tAlg t → Zipper A tAlg t → Set where
      <-Right-Step  : ∀ {a} {l r} {t₁ t₂} {s₁ s₂} {eq}
                    → (eq₁ : plug⇓ (Tip t₁) s₁ ≡ r) → (eq₂ : plug⇓ (Tip t₂) s₂ ≡ r)
                    → [[ r ]]        (t₁ ,, s₁                ,, eq₁)           < (t₂ ,, s₂                ,, eq₂)
                    → [[ Node l r ]] (t₁ ,, Right a l eq ∷ s₁ ,, Node-injᵣ eq₁) < (t₂ ,, Right a l eq ∷ s₂ ,, Node-injᵣ eq₂)
                    
  --     <-Left-Step   : ∀ {r} {t₁ t₂ s₁ s₂}                         → (t₁ , s₁) < (t₂ , s₂)   →  (t₁ , Left r ∷ s₁)       < (t₂ , Left r ∷ s₂)
  --     <-Right-Left  : ∀ {n} {t₁ t₂ s₁ s₂} {t₁′ t₂′}  {eq : eval t₁′ ≡ n} → (t₁′ ≡ plug⇓ (Tip t₂) s₂)
  --                                                                        → (t₂′ ≡ plug⇓ (Tip t₁) s₁) → (t₁ , Right t₁′ n eq ∷ s₁) < (t₂ , Left t₂′ ∷ s₂)

  mutual
    accR : ∀ {A} {tAlg : TreeAlg A} {l r : Tree} (t₁ : ℕ) (s₁ : Stack A tAlg) (eq₁ : plug⇓ (Tip t₁) s₁ ≡ r)
           {a : A} {eq : treeCata tAlg l ≡ a} →
           Acc ([[_]]_<_ r) (t₁ ,, s₁ ,, eq₁) → 
           (y : Zipper A tAlg (Node l r)) → [[ Node l r ]] y < (t₁ ,, inj₂ (a , l , eq) ∷ s₁ ,, Node-injᵣ eq₁) → Acc ([[_]]_<_ (Node l r)) y
    accR t₁ s₁ eq₁ (acc rs) (n ,, [] ,, x) ()
    accR t₁ s₁ eq₁ (acc rs) (n ,, inj₁ x₁ ∷ s ,, x) ()
    accR t₁ s₁ eq₁ (acc rs) (n ,, inj₂ (a′ , t′ , eq′) ∷ s ,, x) p = {!!}
    
    <-WF : {A : Set} → {tAlg : TreeAlg A} → (t : Tree) → Well-founded ([[_]]_<_ {A} {tAlg} t)
    <-WF t x = acc (aux t x)
      where
        aux : ∀ {A} {tAlg : TreeAlg A} (t : Tree) (x : Zipper A tAlg t)
            (y : Zipper A tAlg t) → [[ t ]] y < x → Acc ([[_]]_<_ t) y
        aux .(Node l (plug⇓ (Tip t₁) s₁)) .(t₂ ,, inj₂ (a , l , eq) ∷ s₂ ,, Node-injᵣ eq₂) .(t₁ ,, inj₂ (a , l , eq) ∷ s₁ ,, refl)
             (<-Right-Step {a} {l} {.(plug⇓ (Tip t₁) s₁)} {t₁} {t₂} {s₁} {s₂} {eq} refl eq₂ p)
         = acc (accR t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) (t₁ ,, s₁ ,, refl)))
\end{code}
