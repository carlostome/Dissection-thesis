\begin{code}
module Thesis.FoldIx where

  open import Data.Nat
  open import Data.List
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Induction.WellFounded
  open import Function
  open import Data.List.Reverse
  open import Data.List.Properties

  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  Node-injᵣ : ∀ {l r₁ r₂} → Node l r₁ ≡ Node l r₂ → r₁ ≡ r₂
  Node-injᵣ refl = refl

  Node-injₗ : ∀ {l₁ l₂ r} →  Node l₁ r ≡ Node l₂ r → l₁ ≡ l₂
  Node-injₗ refl = refl

  record TreeAlg : Set₁ where
    field
      A : Set
      TipA  : ℕ → A
      NodeA : A → A → A

  treeCata : (tAlg : TreeAlg) → Tree → (TreeAlg.A tAlg)
  treeCata tAlg (Tip n)      = TreeAlg.TipA  tAlg n
  treeCata tAlg (Node t₁ t₂) = TreeAlg.NodeA tAlg (treeCata tAlg t₁) (treeCata tAlg t₂)

  module _ (tAlg : TreeAlg) where
    open TreeAlg tAlg
    
    -- the Stack is parametrized not only by the type of result A
    -- but with the algebra used to compute the result for the trees already
    -- processed
    Stack : Set
    Stack = List (Tree ⊎ Σ A λ a → Σ Tree λ t → treeCata tAlg t ≡ a)

    pattern Left t       = inj₁ t
    pattern Right r t p  = inj₂ (r , t , p)

    plug⇑  : Tree → Stack → Tree
    plug⇑ t (Left   t₁ ∷ s)     = plug⇑ (Node t t₁) s
    plug⇑ t (Right  r t₁ p ∷ s) = plug⇑ (Node t₁ t) s
    plug⇑ t []                  = t

    plug⇓ : Tree → Stack → Tree
    plug⇓ t []                  = t
    plug⇓ t (Left t₁ ∷ s)       = Node (plug⇓ t s) t₁
    plug⇓ t (Right _ t₁ _ ∷ s)  = Node t₁ (plug⇓ t s)

    UZipper = ℕ × Stack
    
    -- Zipper is indexed by the tree that is supposed to plug to
    data Zipper⇓ (t : Tree) : Set where
      _,,_,,_ : (n : ℕ) → (s : Stack) → plug⇓ (Tip n) s ≡ t → Zipper⇓ t

    lift⇓ : (n : ℕ) → (s : Stack) → Zipper⇓ (plug⇓ (Tip n) s)
    lift⇓ n s = n ,, s ,, refl

    -- A relation over indexed Zipper⇓s
    data [[_]]_<_ : (t : Tree) → Zipper⇓ t → Zipper⇓ t → Set where
         <-Right-Step  : ∀ {a} {l r} {t₁ t₂} {s₁ s₂} {eq}
                       → (eq₁ : Node l (plug⇓ (Tip t₁) s₁) ≡ Node l r) → (eq₂ : Node l (plug⇓ (Tip t₂) s₂) ≡ Node l r)
                       → [[ r ]]        (t₁ ,, s₁                ,, Node-injᵣ eq₁)           < (t₂ ,, s₂                ,, Node-injᵣ eq₂)
                       → [[ Node l r ]] (t₁ ,, Right a l eq ∷ s₁ ,, eq₁) < (t₂ ,, Right a l eq ∷ s₂ ,, eq₂)

         <-Left-Step  : ∀ {l r} {t₁ t₂} {s₁ s₂}
                       → (eq₁ : Node (plug⇓ (Tip t₁) s₁) r ≡ Node l r) → (eq₂ : Node (plug⇓ (Tip t₂) s₂) r ≡ Node l r)
                       → [[ l ]]        (t₁ ,, s₁                ,, Node-injₗ eq₁)           < (t₂ ,, s₂                ,, Node-injₗ eq₂)
                       → [[ Node l r ]] (t₁ ,, Left r  ∷ s₁ ,, eq₁) < (t₂ ,, Left r ∷ s₂ ,, eq₂)
                    
         <-Right-Left  : ∀ {a} {l r} {t₁ t₂ s₁ s₂} {eq} {eq₁ eq₂} →
                       [[ Node l r ]] (t₁ ,, Right a l eq ∷ s₁ ,, eq₁) < (t₂ ,, Left r ∷ s₂ ,, eq₂)

    mutual
      accR : ∀ {l r : Tree} (t : ℕ) (s : Stack) eq₁
               {a : A} {eq : treeCata tAlg l ≡ a} →
               Acc ([[_]]_<_ r) (t ,, s ,, Node-injᵣ eq₁) → 
             (y : Zipper⇓ (Node l r)) → [[ Node l r ]] y < (t ,, inj₂ (a , l , eq) ∷ s ,, eq₁) → Acc ([[_]]_<_ (Node l r)) y
      accR t s eq₁ {a} {eq} (acc rs) .(t₁ ,, inj₂ (a , _ , eq) ∷ s₁ ,, refl) (<-Right-Step {t₁ = t₁} {s₁ = s₁} refl .eq₁ p)
          = acc (accR t₁ s₁ refl (rs (t₁ ,, s₁ ,, refl) p))

      accL : ∀ {l r : Tree} (t : ℕ) (s : Stack) eq₂ →
               Acc ([[_]]_<_ l) (t ,, s ,, Node-injₗ eq₂) → 
               (y : Zipper⇓ (Node l r)) → [[ Node l r ]] y < (t ,, inj₁ r ∷ s ,, eq₂) → Acc ([[_]]_<_ (Node l r)) y
      accL {r = r} t s eq₂ (acc rs) .(t₁ ,, inj₁ r ∷ s₁ ,, refl) (<-Left-Step {t₁ = t₁} {s₁ = s₁} refl .eq₂ p)
        = acc (accL t₁ s₁ refl (rs (t₁ ,, s₁ ,, refl) p))
      accL {l} t s eq₂ (acc rs) .(t₁ ,, inj₂ (a , l , eq) ∷ s₁ ,, refl) (<-Right-Left {a} {t₁ = t₁} {s₁ = s₁} {eq = eq} {refl})
        = acc (accR t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) (t₁ ,, s₁ ,, refl)))

      <-WF : ∀ (t : Tree) → Well-founded ([[ t ]]_<_)
      <-WF t x = acc (aux t x)
          where
            aux : ∀ (t : Tree) (x : Zipper⇓ t)
                (y : Zipper⇓ t) → [[ t ]] y < x → Acc ([[_]]_<_ t) y
            aux .(Node l (plug⇓ (Tip t₁) s₁)) .(t₂ ,, inj₂ (a , l , eq) ∷ s₂ ,, eq₂) .(t₁ ,, inj₂ (a , l , eq) ∷ s₁ ,, refl)
                (<-Right-Step {a} {l} {t₁ = t₁} {t₂} {s₁} {s₂} {eq} refl eq₂ p)
              = acc (accR t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) (t₁ ,, s₁ ,, refl)))
            aux .(Node (plug⇓ (Tip t₁) s₁) r) .(t₂ ,, inj₁ r ∷ s₂ ,, eq₂) .(t₁ ,, inj₁ r ∷ s₁ ,, refl)
                (<-Left-Step {r = r} {t₁} {t₂} {s₁} {s₂} refl eq₂ p)
              = acc (accL t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) (t₁ ,, s₁ ,, refl)))
            aux .(Node l (plug⇓ (Tip t₁) s₁)) .(t₂ ,, inj₁ (plug⇓ (Tip t₁) s₁) ∷ s₂ ,, eq₂) .(t₁ ,, inj₂ (a , l , eq) ∷ s₁ ,, refl)
                (<-Right-Left {a} {l} {.(plug⇓ (Tip t₁) s₁)} {t₁} {t₂} {s₁} {s₂} {eq} {refl} {eq₂})
              = acc (accR t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) (t₁ ,, s₁ ,, refl)))

      plug⇑-++-Right : ∀ x a t (p : treeCata tAlg t ≡ a) s → plug⇑ x (s ++ Right a t p ∷ []) ≡ Node t (plug⇑ x s)
      plug⇑-++-Right x a t p (Left t′ ∷ s)       = plug⇑-++-Right (Node x t′) a t p s
      plug⇑-++-Right x a t p (Right a′ t′ p′ ∷ s)   = plug⇑-++-Right (Node t′ x) a t p s
      plug⇑-++-Right _ _ _ _ []                   = refl

      plug⇑-++-Left : ∀ x t s → plug⇑ x (s ++  inj₁ t ∷ []) ≡ Node (plug⇑ x s) t
      plug⇑-++-Left x t′ (Left t ∷ s)       = plug⇑-++-Left (Node x t) t′ s
      plug⇑-++-Left x t′ (Right a t p ∷ s)  = plug⇑-++-Left (Node t x) t′ s
      plug⇑-++-Left _ _ []                 = refl

      plug⇓-++-Left : ∀ {x} {t} s → plug⇓ x (s ++ Left t ∷ []) ≡ plug⇓ (Node x t) s
      plug⇓-++-Left (Left t ∷ s)       = cong (flip Node t) (plug⇓-++-Left s)
      plug⇓-++-Left (Right a t p ∷ s)  = cong (Node t)      (plug⇓-++-Left s)
      plug⇓-++-Left []                 = refl

      plug⇓-++-Right : ∀ {x} {a} {t} {p : treeCata tAlg t ≡ a} s → plug⇓ x (s ++ Right a t p ∷ []) ≡ plug⇓ (Node t x) s
      plug⇓-++-Right (Left t ∷ s)       = cong (flip Node t) (plug⇓-++-Right s)
      plug⇓-++-Right (Right a t p ∷ s)  = cong (Node t) (plug⇓-++-Right s)
      plug⇓-++-Right []                 = refl

      plug⇑-to-plug⇓ : ∀ t s → plug⇑ t s ≡ plug⇓ t (reverse s)
      plug⇑-to-plug⇓  t  s = aux t s (reverseView s)
        where aux : ∀ t s → Reverse s → plug⇑ t s ≡ plug⇓ t (reverse s)
              aux t .[] [] = refl
              aux t .(s ++ Left t₁ ∷ []) (s ∶ x ∶ʳ Left t₁)
                rewrite reverse-++-commute s (Left t₁ ∷ [])
                        | plug⇑-++-Left t t₁ s                   = cong (flip Node t₁) (aux t s x)
              aux t .(s ++ Right a t₁ eq ∷ []) (s ∶ x ∶ʳ Right a t₁ eq)
                rewrite reverse-++-commute s (Right a t₁ eq ∷ [])
                        | plug⇑-++-Right t a t₁ eq s         = cong (Node t₁) (aux t s x)

      plug⇓-to-plug⇑ : ∀ t s → plug⇓ t s ≡ plug⇑ t (reverse s)
      plug⇓-to-plug⇑ t  s = aux t s (reverseView s)
        where aux : ∀ t s → Reverse s → plug⇓ t s ≡ plug⇑ t (reverse s)
              aux t .[] [] = refl
              aux t .(s ++ Right a t₁ eq ∷ []) (s ∶ x ∶ʳ Right a t₁ eq)
                rewrite reverse-++-commute s (Right a t₁ eq ∷ [])
                        | plug⇓-++-Right {t} {a} {t₁} {eq} s      = aux (Node t₁ t) s x
              aux t .(s ++ Left t₁ ∷ []) (s ∶ x ∶ʳ Left t₁)
                rewrite reverse-++-commute s (Left t₁ ∷ [])
                        | plug⇓-++-Left {t} {t₁} s                = aux (Node t t₁) s x

      data Zipper⇑ (t : Tree) : Set where
        _,,_,,_ : (n : ℕ) → (s : Stack) → plug⇑ (Tip n) s ≡ t → Zipper⇑ t

      forget⇑ : (t : Tree) → Zipper⇑ t → UZipper
      forget⇑ t (n ,, s ,, x) = n , s
    
      Zipper⇓-to-Zipper⇑ : (t : Tree) → Zipper⇓ t → Zipper⇑ t
      Zipper⇓-to-Zipper⇑ .(plug⇓ (Tip n) s) (n ,, s ,, refl)
        = n ,, reverse s ,, sym (plug⇓-to-plug⇑ (Tip n) s)

      Zipper⇑-to-Zipper⇓ : (t : Tree) → Zipper⇑ t → Zipper⇓ t
      Zipper⇑-to-Zipper⇓ .(plug⇑ (Tip n) s) (n ,, s ,, refl)
        = n ,, (reverse s) ,, sym (plug⇑-to-plug⇓ (Tip n) s)

      data [[_]]⇑_<_ (t : Tree) : Zipper⇑ t → Zipper⇑ t → Set where
        lt : ∀ z₁ z₂ → [[ t ]] Zipper⇑-to-Zipper⇓ t z₁ < Zipper⇑-to-Zipper⇓ t z₂ → [[ t ]]⇑ z₁ < z₂

      <⇑-WF : ∀ (t : Tree) → Well-founded ([[ t ]]⇑_<_)
      <⇑-WF t x = acc (aux t x (<-WF t (Zipper⇑-to-Zipper⇓ t x)))
        where
          aux : (t : Tree) → (z : Zipper⇑ t) → Acc [[ t ]]_<_ (Zipper⇑-to-Zipper⇓ t z)
              →  WfRec ([[ t ]]⇑_<_) (Acc ([[ t ]]⇑_<_)) z
          aux t x (acc rs) y (lt .y .x p) = acc (aux t y (rs (Zipper⇑-to-Zipper⇓ t y) p))
 
      -- A result of a load/unload is either a value of type A or
      -- a Zipper that corresponds to the next leaf
      UResult : Set
      UResult = UZipper ⊎ A

      load : Tree → Stack → UResult
      load (Tip x) s      = inj₁ (x , s)
      load (Node t₁ t₂) s = load t₁ (Left t₂ ∷ s)

      unload : (t : Tree) → (r : A) → treeCata tAlg t ≡ r → Stack → UResult
      unload t a eq []                    = inj₂ a
      unload t a eq (Left t′ ∷ s)         = load t′ (Right a t eq ∷ s)
      unload t a eq (Right a′ t′ eq′ ∷ s) = unload  (Node t′ t) ((NodeA) a′ a) (cong₂ (NodeA) eq′ eq) s

      step : UZipper → UResult
      step (n , s)  = unload (Tip n) (TipA n) refl s

      load-preserves-plug⇑ : (t : Tree) (s : Stack) (t′ : ℕ) (s′ : Stack)
                           → {!!} {- load t s ≡ inj₁ (t′ , s′) -} → plug⇑ (Tip t′) s′ ≡ plug⇑ t s -- plug⇑ t s ≡ plug⇑ (Tip t′) s′
      load-preserves-plug⇑ = {!!}

      loadIx : (t : Tree) → (s : Stack) → Zipper⇑ (plug⇑ t s)
      loadIx t s with load t s | inspect (load t) s
      ... | inj₁ (t′ , s′) | [ eq ] = t′ ,, s′ ,, (load-preserves-plug⇑ t s t′ s′ eq)
  --     load-preserves-plug⇑ (Tip n) s .n .s refl   = refl
 --     load-preserves-plug⇑ (Node t₁ t₂) s t′ s′ x = load-preserves-plug⇑ t₁ (inj₁ t₂ ∷ s) t′ s′ x

      -- unload-preserves-plug⇑ : (t : Tree) (a : A) (eq : treeCata tAlg t ≡ a) (s : Stack) (t′ : ℕ) (s′ : Stack)
      --                        → unload t a eq s ≡ inj₁ (t′ , s′) → plug⇑ t s ≡ plug⇑ (Tip t′) s′
      -- unload-preserves-plug⇑ t a eq [] t′ s′ ()
      -- unload-preserves-plug⇑ t a eq (Left x ∷ s) t′ s′ p         = load-preserves-plug⇑ x (Right a t eq ∷ s) t′ s′ p
      -- unload-preserves-plug⇑ t a eq (Right a′ x eq′ ∷ s) t′ s′ p = unload-preserves-plug⇑ (Node x t) (NodeA a′ a) (cong₂ (NodeA) eq′ eq) s t′ s′ p

      -- step-preserves-plug⇑ : (z z′ : UZipper) → step z ≡ inj₁ z′ → plug⇑ z ≡ plug⇑ z′
      -- step-preserves-plug⇑ (t , s) (t′ , s′) x = unload-preserves-plug⇑ (Tip t) (TipA t) refl s t′ s′ x



      convert : UZipper → UZipper
      convert (n , s) = (n , reverse s)

      Result : (t : Tree) → Set
      Result t = Zipper⇑ t ⊎ A 

      stepIx : (t : Tree) → Zipper⇑ t → Zipper⇑ t ⊎ A
      stepIx t x with step (forget⇑ t x) | inspect step (forget⇑ t x)
      stepIx t x | inj₁ (t′ , s′) | [ eq ] = inj₁ (t′ ,, s′ ,, {!!})
      stepIx t x | inj₂ y         | _      = inj₁ x


      stepIx-< : (t : Tree) → (z z′ : Zipper⇑ t) → stepIx t z ≡ inj₁ z′ → [[ t ]]⇑ z′ < z
      stepIx-< t z z′ x = lt z′ z {!!}


      rec : (t : Tree) → (z : Zipper⇑ t) → Acc ([[ t ]]⇑_<_) z → A
      rec t z (acc rs) with stepIx t z | inspect (stepIx t) z
      rec t z (acc rs) | inj₁ x | [ eq ] = rec t x (rs x (stepIx-< t z x eq))
      rec t z (acc rs) | inj₂ y | _      = y

      foldTree : Tree → A
      foldTree t with loadIx t []
      ... | z = rec t z (<⇑-WF t z)
      
      -- rec t  s (acc rs) with step (t , s) | inspect step (t , s)
      -- rec t  s (acc rs) | inj₁ (t′ , s′) | [ eq ]
      --   with plug⇑ (Tip t) s | step-preserves-plug⇑ (t , s) (t′ , s′) eq
      -- rec t s (acc rs) | inj₁ (t′ , s′) | Reveal_·_is_.[ eq ] | .(plug⇑ (Tip t′) s′) | refl
      --   = rec t′ s′ (rs (t′ , (reverse s′))
      --               (lt (t′ , (reverse s′)) (t , reverse s)
      --                         (sym (plug⇑-to-plug⇓ (Tip t′) s′)) (trans (sym (plug⇑-to-plug⇓ (Tip t) s))
      --                         (step-preserves-plug⇑ (t , s) (t′ , s′) eq))
      --                         (step-< (t , s) (t′ , s′) eq)))
      -- rec t  s (acc rs) | inj₂ n  | eq = n


      
\end{code}
