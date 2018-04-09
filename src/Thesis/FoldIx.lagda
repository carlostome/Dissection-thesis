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
  open import Data.List.All
  open import Data.List.All.Properties
  open import Thesis.Data.Sum.Inj
  open import Data.Empty
  
  private
    ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs = refl
    ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

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

  -- Catamorphism over a Tree given an algebra
  treeCata : (tAlg : TreeAlg) → Tree → (TreeAlg.A tAlg)
  treeCata tAlg (Tip n)      = TreeAlg.TipA  tAlg n
  treeCata tAlg (Node t₁ t₂) = TreeAlg.NodeA tAlg (treeCata tAlg t₁) (treeCata tAlg t₂)

  evalTreeAlg : TreeAlg
  evalTreeAlg = record { A = ℕ ; TipA = id ; NodeA = _+_ }


  -- The tail-recursive construction is parametrized over the algebra used.
  module _ (tAlg : TreeAlg) where

    open TreeAlg tAlg
    
    Stack : Set
    Stack = List (Tree ⊎ Σ A λ a → Σ Tree λ t → treeCata tAlg t ≡ a)

    pattern Left t       = inj₁ t
    pattern Right r t p  = inj₂ (r , t , p)

    -- plug bottom-up
    plug⇑  : Tree → Stack → Tree
    plug⇑ t (Left   t₁ ∷ s)     = plug⇑ (Node t t₁) s
    plug⇑ t (Right  r t₁ p ∷ s) = plug⇑ (Node t₁ t) s
    plug⇑ t []                  = t

    -- plug top-down
    plug⇓ : Tree → Stack → Tree
    plug⇓ t []                  = t
    plug⇓ t (Left t₁ ∷ s)       = Node (plug⇓ t s) t₁
    plug⇓ t (Right _ t₁ _ ∷ s)  = Node t₁ (plug⇓ t s)


    ----------------------------------------------------------------------------------
    --                         Properties of plug                                   --


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


    --------------------------------------------------------------------------------
    --                        Zipper                                              --                                                            


    UZipper = ℕ × Stack

    plugZ⇑ : UZipper → Tree
    plugZ⇑ (t , s) = plug⇑ (Tip t) s
    
    plugZ⇓ : UZipper → Tree
    plugZ⇓ (t , s) = plug⇓ (Tip t) s


    --------------------------------------------------------------------------------
    --                        Top-down Indexed  Zipper                            --                                                            


    data Zipper⇓ (t : Tree) : Set where
      _,,_ : (z : UZipper) → plugZ⇓ z ≡ t → Zipper⇓ t

    -- the extra structure of the Zipper⇓ can be forgotten
    forget⇓ : ∀ {t : Tree} → (z : Zipper⇓ t) → UZipper
    forget⇓ (z ,, _) = z
    
    -- A relation over indexed Zipper⇓
    data [[_]]⇓_<_ : (t : Tree) → Zipper⇓ t → Zipper⇓ t → Set where
         <-Right-Step  : ∀ {a} {l r} {t₁ t₂} {s₁ s₂} {eq}
                       → (eq₁ : Node l (plug⇓ (Tip t₁) s₁) ≡ Node l r) → (eq₂ : Node l (plug⇓ (Tip t₂) s₂) ≡ Node l r)
                       → [[ r ]]⇓        ((t₁ , s₁)                 ,, Node-injᵣ eq₁)  < ((t₂ , s₂)                ,, Node-injᵣ eq₂)
                       → [[ Node l r ]]⇓ ((t₁ , Right a l eq ∷ s₁ ) ,, eq₁)            < ((t₂ , Right a l eq ∷ s₂) ,, eq₂)

         <-Left-Step  : ∀ {l r} {t₁ t₂} {s₁ s₂}
                       → (eq₁ : Node (plug⇓ (Tip t₁) s₁) r ≡ Node l r) → (eq₂ : Node (plug⇓ (Tip t₂) s₂) r ≡ Node l r)
                       → [[ l ]]⇓        ((t₁ , s₁)           ,, Node-injₗ eq₁) < ((t₂ , s₂ )               ,, Node-injₗ eq₂)
                       → [[ Node l r ]]⇓ ((t₁ , Left r  ∷ s₁) ,, eq₁)           < ((t₂ , Left r ∷ s₂ ) ,, eq₂)
                    
         <-Right-Left  : ∀ {a} {l r} {t₁ t₂ s₁ s₂} {eq} {eq₁ eq₂} → [[ Node l r ]]⇓ ((t₁ , Right a l eq ∷ s₁) ,, eq₁) < ((t₂ , Left r ∷ s₂) ,, eq₂)


    ----------------------------------------------------------------------------------
    --                  Well-foundedness proof of [[_]]⇓_<_                         --



    accR : ∀ {l r : Tree} (t : ℕ) (s : Stack) eq₁
             {a : A} {eq : treeCata tAlg l ≡ a} →
             Acc ([[_]]⇓_<_ r) ((t , s) ,, Node-injᵣ eq₁) →
             (y : Zipper⇓ (Node l r)) → [[ Node l r ]]⇓ y < ((t , inj₂ (a , l , eq) ∷ s) ,, eq₁) → Acc ([[_]]⇓_<_ (Node l r)) y
    accR t s eq₁ {a} {eq} (acc rs) .((t₁ , inj₂ (a , _ , eq) ∷ s₁) ,, refl) (<-Right-Step {t₁ = t₁} {s₁ = s₁} refl .eq₁ p)
        = acc (accR t₁ s₁ refl (rs ((t₁ , s₁) ,, refl) p))
    
    accL : ∀ {l r : Tree} (t : ℕ) (s : Stack) eq₂ →
             (wrf : Well-founded [[ r ]]⇓_<_) →
             Acc ([[_]]⇓_<_ l) ((t , s ) ,, Node-injₗ eq₂) → 
             (y : Zipper⇓ (Node l r)) → [[ Node l r ]]⇓ y < ((t , inj₁ r ∷ s) ,, eq₂) → Acc ([[_]]⇓_<_ (Node l r)) y
    accL {r = r} t s eq₂ wfr (acc rs) .((t₁ , inj₁ r ∷ s₁) ,, refl) (<-Left-Step {t₁ = t₁} {s₁ = s₁} refl .eq₂ p)
      = acc (accL t₁ s₁ refl wfr (rs ((t₁ , s₁) ,, refl) p))
    accL {l} t s eq₂ wrf (acc rs) .((t₁ , inj₂ (a , l , eq) ∷ s₁) ,, refl) (<-Right-Left {a} {t₁ = t₁} {s₁ = s₁} {eq = eq} {refl})
      = acc (accR t₁ s₁ refl (wrf ((t₁ , s₁) ,, refl)))

    <-WF : ∀ (t : Tree) → Well-founded ([[ t ]]⇓_<_)
    <-WF t x = acc (aux t x)
          where
            aux : ∀ (t : Tree) (x : Zipper⇓ t)
                (y : Zipper⇓ t) → [[ t ]]⇓ y < x → Acc ([[_]]⇓_<_ t) y
            aux .(Node l (plug⇓ (Tip t₁) s₁)) .((t₂ , inj₂ (a , l , eq) ∷ s₂) ,, eq₂) .((t₁ , inj₂ (a , l , eq) ∷ s₁) ,, refl)
                (<-Right-Step {a} {l} {t₁ = t₁} {t₂} {s₁} {s₂} {eq} refl eq₂ p)
              = acc (accR t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) ((t₁ , s₁) ,, refl)))
            aux .(Node (plug⇓ (Tip t₁) s₁) r) .((t₂ , inj₁ r ∷ s₂) ,, eq₂) .((t₁ , inj₁ r ∷ s₁) ,, refl)
                (<-Left-Step {r = r} {t₁} {t₂} {s₁} {s₂} refl eq₂ p)
              = acc (accL t₁ s₁ refl (<-WF r) (<-WF (plug⇓ (Tip t₁) s₁) ((t₁ , s₁) ,, refl)))
            aux .(Node l (plug⇓ (Tip t₁) s₁)) .((t₂ , inj₁ (plug⇓ (Tip t₁) s₁) ∷ s₂) ,, eq₂) .((t₁ , inj₂ (a , l , eq) ∷ s₁) ,, refl)
                (<-Right-Left {a} {l} {.(plug⇓ (Tip t₁) s₁)} {t₁} {t₂} {s₁} {s₂} {eq} {refl} {eq₂})
              = acc (accR t₁ s₁ refl (<-WF (plug⇓ (Tip t₁) s₁) ((t₁ , s₁) ,, refl)))


   ----------------------------------------------------------------------------------
   --                  Relation over UZipper                                       --


    data _<ᵤ_ : UZipper → UZipper → Set where
      <ᵤ-Right-Step  : ∀ {a} {l} {t₁ t₂} {s₁ s₂} {eq : treeCata tAlg l ≡ a}
                      → (t₁ , s₁) <ᵤ (t₂ , s₂)
                      →  (t₁ , Right a l eq ∷ s₁) <ᵤ (t₂ , Right a l eq ∷ s₂)
      <ᵤ-Left-Step   : ∀ {r} {t₁ t₂ s₁ s₂}
                      → (t₁ , s₁) <ᵤ (t₂ , s₂)
                      →  (t₁ , Left r ∷ s₁)       <ᵤ (t₂ , Left r ∷ s₂)
      <ᵤ-Right-Left  : ∀ {a} {t₁ t₂ s₁ s₂} {t₁′ t₂′}  {eq : treeCata tAlg t₁′ ≡ a} → (t₁′ ≡ plug⇓ (Tip t₂) s₂)
                      → (t₂′ ≡ plug⇓ (Tip t₁) s₁)
                      → (t₁ , Right a t₁′ eq ∷ s₁) <ᵤ (t₂ , Left t₂′ ∷ s₂)

    -- from the relation over UZipper and equality proofs we can recover the
    -- indexed relation
    to : ∀ (t : Tree) (z₁ z₂ : UZipper) (eq₁ : plugZ⇓ z₁ ≡ t) (eq₂ : plugZ⇓ z₂ ≡ t) → z₁ <ᵤ z₂ → [[ t ]]⇓ (z₁ ,, eq₁) < (z₂ ,, eq₂)
    to .(Node l (plug⇓ (Tip t₁) s₁)) .(t₁ , inj₂ (a , l , eq) ∷ s₁) .(t₂ , inj₂ (a , l , eq) ∷ s₂) refl eq₂ (<ᵤ-Right-Step {a} {l} {t₁} {t₂} {s₁} {s₂} {eq} x)
      = <-Right-Step refl eq₂ (to (plug⇓ (Tip t₁) s₁) (t₁ , s₁) (t₂ , s₂) refl (Node-injᵣ eq₂) x)
    to .(Node (plug⇓ (Tip t₁) s₁) r) .(t₁ , inj₁ r ∷ s₁) .(t₂ , inj₁ r ∷ s₂) refl eq₂ (<ᵤ-Left-Step {r} {t₁} {t₂} {s₁} {s₂} x)
      = <-Left-Step refl eq₂ (to (plug⇓ (Tip t₁) s₁) (t₁ , s₁) (t₂ , s₂) refl (Node-injₗ eq₂) x)
    to .(Node (plug⇓ (Tip t₂) s₂) (plug⇓ (Tip t₁) s₁)) .(t₁ , inj₂ (a , plug⇓ (Tip t₂) s₂ , eq) ∷ s₁)
                                                       .(t₂ , inj₁ (plug⇓ (Tip t₁) s₁) ∷ s₂) refl eq₂
                                                       (<ᵤ-Right-Left {a} {t₁} {t₂} {s₁} {s₂} {.(plug⇓ (Tip t₂) s₂)} {eq = eq} refl refl)
      = <-Right-Left


    --------------------------------------------------------------------------------
    --                        Bottom-up Indexed  Zipper                           --                                                            


    data Zipper⇑ (t : Tree) : Set where
      _,,_ : (z : UZipper) → plugZ⇑ z ≡ t → Zipper⇑ t

    -- forget the extra structure
    forget⇑ : ∀ {t : Tree} → Zipper⇑ t → UZipper
    forget⇑ ( z ,, _) = z
    
    forget⇑-prop : (t : Tree) → (z : Zipper⇑ t) → plugZ⇑ (forget⇑ z) ≡ t
    forget⇑-prop t (z ,, x) = x
    
    Zipper⇓-to-Zipper⇑ : (t : Tree) → Zipper⇓ t → Zipper⇑ t
    Zipper⇓-to-Zipper⇑ .(plug⇓ (Tip n) s) ((n , s) ,, refl)
      = (n , reverse s) ,, sym (plug⇓-to-plug⇑ (Tip n) s)

    Zipper⇑-to-Zipper⇓ : (t : Tree) → Zipper⇑ t → Zipper⇓ t
    Zipper⇑-to-Zipper⇓ t ((n , s) ,, x) = (n , reverse s) ,, (trans (sym (plug⇑-to-plug⇓ (Tip n) s)) x)

    data [[_]]⇑_<_ (t : Tree) : Zipper⇑ t → Zipper⇑ t → Set where
      lt : ∀ z₁ z₂ → [[ t ]]⇓ Zipper⇑-to-Zipper⇓ t z₁ < Zipper⇑-to-Zipper⇓ t z₂ → [[ t ]]⇑ z₁ < z₂

    <⇑-WF : ∀ (t : Tree) → Well-founded ([[ t ]]⇑_<_)
    <⇑-WF t x = acc (aux t x (<-WF t (Zipper⇑-to-Zipper⇓ t x)))
      where
        aux : (t : Tree) → (z : Zipper⇑ t) → Acc [[ t ]]⇓_<_ (Zipper⇑-to-Zipper⇓ t z)
            →  WfRec ([[ t ]]⇑_<_) (Acc ([[ t ]]⇑_<_)) z
        aux t x (acc rs) y (lt .y .x p) = acc (aux t y (rs (Zipper⇑-to-Zipper⇓ t y) p))


    --------------------------------------------------------------------------------
    --                        Folding functions                                   --                                                            


    load : Tree → Stack → UZipper ⊎ A
    load (Tip x) s      = inj₁ (x , s)
    load (Node t₁ t₂) s = load t₁ (Left t₂ ∷ s)

    unload : (t : Tree) → (r : A) → treeCata tAlg t ≡ r → Stack → UZipper ⊎ A
    unload t a eq []                    = inj₂ a
    unload t a eq (Left t′ ∷ s)         = load t′ (Right a t eq ∷ s)
    unload t a eq (Right a′ t′ eq′ ∷ s) = unload  (Node t′ t) ((NodeA) a′ a) (cong₂ (NodeA) eq′ eq) s

    -- one step of the fold
    step : UZipper → UZipper ⊎ A
    step (n , s)  = unload (Tip n) (TipA n) refl s


    --------------------------------------------------------------------------------
    --               Properties of Folding functions                              --                                                            


    -- load never delivers some inj₂
    load-not-inj₂ : (t : Tree) (s : Stack) → ∀ a → load t s ≡ inj₂ a → ⊥
    load-not-inj₂ (Tip x₁) s a ()
    load-not-inj₂ (Node t t₁) s a x = load-not-inj₂ t (inj₁ t₁ ∷ s) a x
    
    load-preserves-plug⇑ : (t : Tree) (s : Stack) (t′ : ℕ) (s′ : Stack)
                         → load t s ≡ inj₁ (t′ , s′) → plug⇑ (Tip t′) s′ ≡ plug⇑ t s
    load-preserves-plug⇑ (Tip x₁) s .x₁ .s refl = refl
    load-preserves-plug⇑ (Node t t₁) s t′ s′ x  = load-preserves-plug⇑ t (inj₁ t₁ ∷ s) t′ s′ x

    unload-preserves-plug⇑ : (t : Tree) (a : A) (eq : treeCata tAlg t ≡ a) (s : Stack) (t′ : ℕ) (s′ : Stack)
                           → unload t a eq s ≡ inj₁ (t′ , s′) → plug⇑ (Tip t′) s′ ≡ plug⇑ t s
    unload-preserves-plug⇑ t a eq [] t′ s′ ()
    unload-preserves-plug⇑ t a eq (Left x ∷ s) t′ s′ p         = load-preserves-plug⇑ x (Right a t eq ∷ s) t′ s′ p
    unload-preserves-plug⇑ t a eq (Right a′ x eq′ ∷ s) t′ s′ p = unload-preserves-plug⇑ (Node x t) (NodeA a′ a) (cong₂ (NodeA) eq′ eq) s t′ s′ p

    step-preserves-plug⇑ : (z z′ : UZipper) → step z ≡ inj₁ z′ → plugZ⇑ z′ ≡ plugZ⇑ z
    step-preserves-plug⇑ (t , s) (t′ , s′) x = unload-preserves-plug⇑ (Tip t) (TipA t) refl s t′ s′ x


    --------------------------------------------------------------------------------
    --                        Folding functions over Indexed Zippers              --                                                            

    loadIx : (t : Tree) → (s : Stack) → Zipper⇑ (plug⇑ t s) ⊎ A
    loadIx t s with load t s | inspect (load t) s
    ... | inj₁ (t′ , s′) | [ eq ] = inj₁ ((t′ , s′) ,, load-preserves-plug⇑ t s t′ s′ eq)
    ... | inj₂ y | [ eq ]         = inj₂ y


    loadIx-not-inj₂ : (t : Tree) → (s : Stack) → ∀ a → loadIx t s ≡ inj₂ a → ⊥
    loadIx-not-inj₂ t s a x with load t s | inspect (load t) s
    loadIx-not-inj₂ t s a () | inj₁ x₁ | zz
    loadIx-not-inj₂ t s .y refl | inj₂ y | Reveal_·_is_.[ eq ] = load-not-inj₂ t s y eq
    
    stepIx : (t : Tree) → Zipper⇑ t → Zipper⇑ t ⊎ A
    stepIx t (z ,, p) with step z | inspect step z
    stepIx .(plug⇑ (Tip (proj₁ z)) (proj₂ z)) (z ,, refl)
      | inj₁ x | Reveal_·_is_.[ eq ]                 = inj₁ (x ,, (step-preserves-plug⇑ z x eq))
    stepIx t (z ,, p) | inj₂ y | Reveal_·_is_.[ eq ] = inj₂ y

    stepU : ∀ (t : Tree) z₁ z₂
          → stepIx t z₁ ≡ inj₁ z₂ → step (forget⇑ z₁) ≡ inj₁ (forget⇑ z₂)
    stepU t (z₁ ,, p₁) (z₂ ,, p₂) x with step z₁ | inspect step z₁
    stepU .(plug⇑ (Tip (proj₁ z₁)) (proj₂ z₁)) (z₁ ,, refl)
          (.x₁ ,, .(unload-preserves-plug⇑ (Tip (proj₁ z₁)) (TipA (proj₁ z₁)) refl (proj₂ z₁) (proj₁ x₁) (proj₂ x₁) eq)) refl
          | inj₁ x₁ | Reveal_·_is_.[ eq ] = refl
    stepU t (z₁ ,, p₁) (z₂ ,, p₂) () | inj₂ y | ee
    
    prepend : ∀ {t₁ t₂ s₁ s₂} → (t₁ , s₁) <ᵤ (t₂ , s₂) → ∀ s → (t₁ , s ++ s₁) <ᵤ (t₂ , s ++ s₂)
    prepend x (Left t ∷ s)       = <ᵤ-Left-Step  (prepend x s)
    prepend x (Right t n eq ∷ s) = <ᵤ-Right-Step (prepend x s)
    prepend x [] = x

    load-stack-lemma : ∀ t t′ s s′ → load t s ≡ inj₁ (t′ , s′)
                     → ∃ λ s′′
                     → s′ ≡ s′′ ++ s × All Is-inj₁ s′′ × plug⇑ (Tip t′) s′′ ≡ t
    load-stack-lemma (Tip x) .x s .s refl = [] , refl , [] , refl
    load-stack-lemma (Node t₁ t₂) t′ s s′ x with load-stack-lemma t₁ t′ (inj₁ t₂ ∷ s) s′ x
    load-stack-lemma (Node .(Tip t′) t₂) t′ s .(inj₁ t₂ ∷ s) refl | .[] , refl , [] , refl = Left t₂ ∷ [] , (refl , (is-inj₁ ∷ [] , refl))
    load-stack-lemma (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) t′ s .(inj₁ x ∷ xs ++ inj₁ t₂ ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl
      = Left x ∷ xs ++ (Left t₂ ∷ [])
        , cong (Left x ∷_) (sym (++-assoc xs (inj₁ t₂ ∷ []) s))
        , ++⁺ {xs = Left x ∷ xs} {ys = Left t₂ ∷ []} (is-inj₁ ∷ all) (is-inj₁ ∷ [])
        , plug⇑-++-Left (Node (Tip t′) x) t₂ xs


    reverse-++ : ∀ {A : Set} (s : List A) (x : A) → reverse (x ∷ s) ≡ reverse s ++ (x ∷ [])
    reverse-++ xs x = unfold-reverse x xs

    load-< : ∀ n eq t s t′ s′
            → load t (Right (TipA n) (Tip n) eq ∷ s) ≡ inj₁ (t′ , s′)
            → (t′ , reverse s′) <ᵤ (n , reverse (Left t ∷ s)) 
    load-< n eq (Tip x) s .x .(Right (TipA n) (Tip n) eq ∷ s) refl with reverse (Right (TipA n) (Tip n ) eq ∷ s) | reverse-++ s (Right (TipA n) (Tip n) eq)
    load-< n eq (Tip x) s .x .(Right (TipA n) (Tip n) eq ∷ s) refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      with reverse (Left (Tip x) ∷ s) | reverse-++ s (Left (Tip x))
    load-< n eq (Tip x) s .x .(Right (TipA n) (Tip n) eq ∷ s) refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₁ (Tip x) ∷ []) | refl
      = prepend (<ᵤ-Right-Left refl refl) (reverse s)
    load-< n eq (Node t₁ t₂) s t′ s′ p with load-stack-lemma t₁ t′ (inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) s′ p
    load-< n eq (Node .(Tip t′) t₂) s t′ .(inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) refl | .[] , refl , [] , refl
      with reverse (Left (Node (Tip t′) t₂) ∷ s) | reverse-++ s (Left (Node (Tip t′) t₂))
    load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) refl | .[] , refl , [] , refl
      | .(foldl (λ rev x → x ∷ rev) [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
      with reverse (Left t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) | reverse-++ (Right (TipA n) (Tip n) eq ∷ s) (Left t₂)
    load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) refl
      | .[] , refl , [] , refl | .(foldl _ [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
      | .(foldl (λ rev x → x ∷ rev) (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      with reverse (Right (TipA n) (Tip n ) eq ∷ s) | reverse-++ s (Right (TipA n) (Tip n) eq)
    load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) refl | .[] , refl , [] , refl
      | .(foldl _ [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      | .(foldl (λ rev x → x ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      with (reverse s ++ Right (TipA n) (Tip n) eq ∷ []) ++ Left t₂ ∷ [] | ++-assoc (reverse s) (Right (TipA n) (Tip n) eq ∷ []) (Left t₂ ∷ [])
    load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) refl | .[] , refl , [] , refl
      | .(foldl _ [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      | .(foldl (λ rev x → x ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) | refl = prepend (<ᵤ-Right-Left refl refl) (reverse s)
    load-< n eq (Node t₁ t₂) s t′ .(inj₁ x ∷ xs ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
      with reverse (Left (Node t₁ t₂) ∷ s) | reverse-++ s (Left (Node t₁ t₂))
    load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl
      with reverse (Left x ∷ (xs ++ Left t₂ ∷ Right (TipA n) (Tip n) eq ∷ s)) | reverse-++-commute  (Left x ∷ xs) (Left t₂ ∷ Right (TipA n) (Tip n) eq ∷ s)
    load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
      | .(foldl _ [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) (Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) s ++ foldl (λ rev x₁ → x₁ ∷ rev) (inj₁ x ∷ []) xs) | refl
      with reverse (Left t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) | reverse-++ (Right (TipA n) (Tip n) eq ∷ s) (Left t₂)
    load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
      | .(foldl _ [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      with reverse (Right (TipA n) (Tip n) eq ∷ s) | reverse-++ s (Right (TipA n) (Tip n) eq)
    load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
      | .(foldl _ [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl | .(foldl _ (Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      with reverse (Left x ∷ xs) | reverse-++ xs (Left x)
    load-< n eq (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl
      | .(foldl _ [] s ++ inj₁ (Node (plug⇑ (Node (Tip t′) x) xs) t₂) ∷ []) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] xs ++ inj₁ x ∷ []) | refl
      with ((reverse s ++ (Right (TipA n) (Tip n) eq ∷ [])) ++ (Left t₂ ∷ [])) | ++-assoc (reverse s) (Right (TipA n) (Tip n) eq ∷ []) (Left t₂ ∷ [])
    load-< n eq (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl | .(foldl _ [] s ++ inj₁ (Node (plug⇑ (Node (Tip t′) x) xs) t₂) ∷ []) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      | .(foldl _ [] xs ++ inj₁ x ∷ []) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) | refl
      with (reverse s ++ (Right (TipA n) (Tip n) eq ∷ Left t₂ ∷ [])) ++ (reverse xs ++ Left x ∷ [])
           | ++-assoc (reverse s) (Right (TipA n) (Tip n) eq ∷ Left t₂ ∷ []) (reverse xs ++ Left x ∷ [])
    load-< n eq (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ Right (TipA n) (Tip n) eq ∷ s) p
      | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl
      | .(foldl _ [] s ++ inj₁ (Node (plug⇑ (Node (Tip t′) x) xs) t₂) ∷ []) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
      | .(foldl _ (Right (TipA n) (Tip n) eq ∷ []) s ++ inj₁ t₂ ∷ []) | refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl | .(foldl _ [] xs ++ inj₁ x ∷ []) | refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ foldl (λ rev x₁ → x₁ ∷ rev) [] xs ++ inj₁ x ∷ []) | refl
      = prepend (<ᵤ-Right-Left refl (cong₂ Node (sym (trans (plug⇓-++-Left (reverse xs)) (sym (plug⇑-to-plug⇓ (Node (Tip t′) x) xs)))) refl)) (reverse s)

    unload-stack-lemma : ∀ pre x post t n eq t′ s′ → All Is-inj₂ pre → unload t n eq (pre ++ Left x ∷ post) ≡ inj₁ (t′ , s′)
                       → ∃ λ s
                         → s′ ≡ s ++ Right (treeCata tAlg (plug⇑ t pre)) (plug⇑ t pre) refl ∷ post
                         × All Is-inj₁ s 
                         × plug⇑ (Tip t′) s ≡ x
    unload-stack-lemma [] x post t .(treeCata tAlg t) refl t′ s′ [] p = load-stack-lemma x t′ (Right (treeCata tAlg t) t refl ∷ post) s′ p
    unload-stack-lemma (Left x₂ ∷ pre) x post t n eq t′ s′ (() ∷ x₁) p
    unload-stack-lemma (Right .(treeCata tAlg y) y refl ∷ pre) x post t .(treeCata tAlg t) refl t′ s′ (is-inj₂ ∷ all) p
      with unload-stack-lemma pre x post (Node y t) (NodeA (treeCata tAlg y) (treeCata tAlg t)) refl t′ s′ all p
    unload-stack-lemma (Right .(treeCata tAlg y) y refl ∷ pre) .(plug⇑ (Tip t′) ss) post t .(treeCata tAlg t) refl t′
      .(ss ++ Right (treeCata tAlg (plug⇑ (Node y t) pre)) (plug⇑ (Node y t) pre) refl ∷ post) (is-inj₂ ∷ all) p | ss , refl , al , refl = ss , refl , al , refl

    data View : Stack → Set where
      AllOf  : ∀ xs       → All Is-inj₂ xs → View xs
      Prefix : ∀ pre y ys → All Is-inj₂ pre → View (pre ++ (Left y ∷ ys))

    toView : ∀ s → View s
    toView [] = AllOf [] []
    toView (inj₁ x ∷ s) = Prefix [] x s []
    toView (inj₂ y ∷ s) with toView s
    toView (inj₂ y ∷ s) | AllOf .s x                             = AllOf (inj₂ y ∷ s) (is-inj₂ ∷ x)
    toView (inj₂ y ∷ .(pre ++ inj₁ x ∷ xs)) | Prefix pre x xs x₁ = Prefix (inj₂ y ∷ pre) x xs (is-inj₂ ∷ x₁)

    other-lemma : ∀ s → All Is-inj₂ s → ∀ t n eq  t′ s′ → unload t n eq s ≡ inj₁ (t′ , s′) → ⊥
    other-lemma .[] [] t n eq t′ s′ ()
    other-lemma .(Right n′ t′′ eq′ ∷ _) (is-inj₂ {(n′ , t′′ , eq′)} ∷ x) t n eq t′ s′ p
      = other-lemma _ x (Node t′′ t) (NodeA n′ n) (cong₂ (NodeA) eq′ eq) t′ s′ p

    unload-< : ∀ n eq s t′ s′ → unload (Tip n) (TipA n) eq s ≡ inj₁ (t′ , s′) → (t′ , reverse s′) <ᵤ (n , reverse s)
    unload-< n eq [] t′ s′ ()
    unload-< n eq (Left x₁ ∷ s) t′ s′ x                 = load-< n eq x₁ s t′ s′ x
    unload-< n eq (inj₂ (val , node , eq′) ∷ s) t′ s′ p with toView s
    unload-< n eq (inj₂ (val , node , eq′) ∷ s) t′ s′ p | AllOf .s x = ⊥-elim (other-lemma s x (Node node (Tip n)) (NodeA val (TipA n)) (cong₂ NodeA eq′ eq) t′ s′ p)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ x ∷ xs)) t′ s′ p | Prefix pre x xs all
      with unload-stack-lemma pre x xs (Node node (Tip n)) (NodeA val (TipA n)) (cong₂ (NodeA) eq′ eq) t′ s′ all p
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .(inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre  , refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      with reverse (inj₂ (val , node , eq′) ∷ (pre ++ inj₁ (Tip t′) ∷ xs))
        | reverse-++ (pre ++ inj₁ (Tip t′) ∷ xs) (inj₂ (val , node , eq′))
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .([] ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre  , refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      | .(foldl (λ rev x → x ∷ rev) [] (pre ++ inj₁ (Tip t′) ∷ xs) ++ inj₂ (val , node , eq′) ∷ []) | refl
      with reverse (pre ++ inj₁ (Tip t′) ∷ xs)
        | reverse-++-commute pre (inj₁ (Tip t′) ∷ xs)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .([] ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre  , refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      | .(foldl _ [] (pre ++ inj₁ (Tip t′) ∷ xs) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl (λ rev x → x ∷ rev) (inj₁ (Tip t′) ∷ []) xs ++ foldl (λ rev x → x ∷ rev) [] pre) | refl
      with reverse (inj₁ (Tip t′) ∷ xs)
        | reverse-++ xs (inj₁ (Tip t′))
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .([] ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre ,  refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      | .(foldl _ [] (pre ++ inj₁ (Tip t′) ∷ xs) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (Tip t′) ∷ []) xs ++ foldl _ [] pre) | refl
      | .(foldl (λ rev x → x ∷ rev) [] xs ++ inj₁ (Tip t′) ∷ []) | refl
      with ((reverse xs ++ inj₁ (Tip t′) ∷ []) ++ reverse pre)
        | ++-assoc (reverse xs) (inj₁ (Tip t′) ∷ []) (reverse pre)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .([] ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      | .(foldl _ [] (pre ++ inj₁ (Tip t′) ∷ xs) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (Tip t′) ∷ []) xs ++ foldl _ [] pre) | refl
      | .(foldl _ [] xs ++ inj₁ (Tip t′) ∷ []) | refl
      | .(foldl (λ rev x → x ∷ rev) [] xs ++ inj₁ (Tip t′) ∷ foldl (λ rev x → x ∷ rev) [] pre) | refl
      with (reverse xs ++ inj₁ (Tip t′) ∷ reverse pre) ++ (inj₂ (val , node , eq′) ∷ [])
        | ++-assoc (reverse xs) (inj₁ (Tip t′) ∷ reverse pre) (inj₂ (val , node , eq′) ∷ [])
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .([] ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      | .(foldl _ [] (pre ++ inj₁ (Tip t′) ∷ xs) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (Tip t′) ∷ []) xs ++ foldl _ [] pre) | refl
      | .(foldl _ [] xs ++ inj₁ (Tip t′) ∷ []) | refl
      | .(foldl _ [] xs ++ inj₁ (Tip t′) ∷ foldl _ [] pre) | refl
      | .(foldl (λ rev x → x ∷ rev) [] xs ++ inj₁ (Tip t′) ∷ foldl (λ rev x → x ∷ rev) [] pre ++ inj₂ (val , node , eq′) ∷ []) | refl
      with reverse (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ xs)
        | reverse-++ xs (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl))
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′
      .([] ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ xs) p
      | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl
      | .(foldl _ [] (pre ++ inj₁ (Tip t′) ∷ xs) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (Tip t′) ∷ []) xs ++ foldl _ [] pre) | refl
      | .(foldl _ [] xs ++ inj₁ (Tip t′) ∷ []) | refl
      | .(foldl _ [] xs ++ inj₁ (Tip t′) ∷ foldl _ [] pre) | refl
      | .(foldl _ [] xs ++ inj₁ (Tip t′) ∷ foldl _ [] pre ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl (λ rev x → x ∷ rev) [] xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      = prepend (<ᵤ-Right-Left (sym (trans (plug⇓-++-Right (reverse pre)) (sym (plug⇑-to-plug⇓ (Node node (Tip n)) pre)))) refl) (reverse xs)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .(inj₁ x ∷ xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {(inj₁ x)} {xs} is-inj₁ al , refl
      with reverse (inj₁ x ∷ (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys))
           | reverse-++ ((xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys)) (inj₁ x)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      with reverse (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys)
        | reverse-++-commute xs (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl (λ rev x₁ → x₁ ∷ rev) [] xs) | refl
      with reverse (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys)
        | reverse-++ ys (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl))
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      with reverse (inj₂ (val , node , eq′) ∷ (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys))
        | reverse-++ ((pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) (inj₂ (val , node , eq′))
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      with reverse (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)
        | reverse-++-commute pre (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl _ [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ys ++ foldl (λ rev x₁ → x₁ ∷ rev) [] pre) | refl
      with reverse (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)
        | reverse-++ ys (inj₁ (plug⇑ (Node (Tip t′) x) xs))
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl _ [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ys ++ foldl _ [] pre) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) | refl
      with ((reverse ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl)  ∷ []) ++ reverse xs)
        | ++-assoc (reverse ys) (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl)  ∷ []) (reverse xs)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl _ [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ys ++ foldl _ [] pre) | refl
      | .(foldl _ [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl)
                ∷ foldl (λ rev x₁ → x₁ ∷ rev) [] xs) | refl
      with (reverse ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ reverse xs) ++ inj₁ x ∷ []
        | ++-assoc (reverse ys) (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ reverse xs) (inj₁ x ∷ [])
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl _ [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ys ++ foldl _ [] pre) | refl
      | .(foldl _ [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ foldl _ [] xs) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ foldl (λ rev x₁ → x₁ ∷ rev) [] xs
                ++ inj₁ x ∷ []) | refl
      with (reverse ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ++ reverse pre
        | ++-assoc (reverse ys) (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) (reverse pre)
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl _ [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ys ++ foldl _ [] pre) | refl | .(foldl _ [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ foldl _ [] xs ++ inj₁ x ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ foldl (λ rev x₁ → x₁ ∷ rev) [] pre) | refl
      with (reverse ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ reverse pre) ++ inj₂ (val , node , eq′) ∷ []
        | ++-assoc (reverse ys) (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ reverse pre) (inj₂ (val , node , eq′) ∷ [])
    unload-< n eq (inj₂ (val , node , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys)) t′
      .((inj₁ x ∷ xs) ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) p
      | Prefix pre .(plug⇑ (Node (Tip t′) x) xs) ys all | .(inj₁ x ∷ xs) , refl , _∷_ {inj₁ x} {xs} is-inj₁ al , refl
      | .(foldl _ [] (xs ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ ys) ++ inj₁ x ∷ []) | refl
      | .(foldl _ (inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) ys ++ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ []) | refl
      | .(foldl _ [] (pre ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ ys) ++ inj₂ (val , node , eq′) ∷ []) | refl
      | .(foldl _ (inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) ys ++ foldl _ [] pre) | refl
      | .(foldl _ [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ []) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ foldl _ [] xs) | refl
      | .(foldl _ [] ys ++ inj₂ (treeCata tAlg (plug⇑ (Node node (Tip n)) pre) , plug⇑ (Node node (Tip n)) pre , refl) ∷ foldl _ [] xs ++ inj₁ x ∷ []) | refl
      | .(foldl _ [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ foldl _ [] pre) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] ys ++ inj₁ (plug⇑ (Node (Tip t′) x) xs) ∷ foldl (λ rev x₁ → x₁ ∷ rev) [] pre ++ inj₂ (val , node , eq′) ∷ []) | refl
      = prepend (<ᵤ-Right-Left (sym (trans (plug⇓-++-Right (reverse pre)) (sym (plug⇑-to-plug⇓ (Node node (Tip n)) pre))))
                                          (sym (trans (plug⇓-++-Left (reverse xs)) (sym (plug⇑-to-plug⇓ (Node (Tip t′) x) xs)) ))) (reverse ys)

    stepIx-< : (t : Tree) → (z z′ : Zipper⇑ t) → stepIx t z ≡ inj₁ z′ → [[ t ]]⇑ z′ < z
    stepIx-< t ((n , s) ,, eq₁) ((n₁ , s₁) ,, eq₂) x
      = lt ((n₁ , s₁) ,, eq₂) ((n , s) ,, eq₁)
           (to t (n₁ , reverse s₁) (n , reverse s) (trans (sym (plug⇑-to-plug⇓ (Tip n₁) s₁)) eq₂)
                                                   (trans (sym (plug⇑-to-plug⇓ (Tip n ) s )) eq₁)
                                                   (unload-< n refl s n₁ s₁ (stepU t ((n , s) ,, eq₁) ((n₁ , s₁) ,, eq₂) x)))

    rec : (t : Tree) → (z : Zipper⇑ t) → Acc ([[ t ]]⇑_<_) z → A
    rec t z (acc rs) with stepIx t z | inspect (stepIx t) z
    rec t z (acc rs) | inj₁ x | [ eq ] = rec t x (rs x (stepIx-< t z x eq))
    rec t z (acc rs) | inj₂ y | _      = y

    foldTree : Tree → A
    foldTree t with loadIx t []
    foldTree t | inj₁ z = rec t z (<⇑-WF t z)
    foldTree t | inj₂ n = n


    --------------------------------------------------------------------------------
    --                        Correctness properties                              --                                                            


    unload-correct : ∀ t n eq s a → unload t n eq s ≡ inj₂ a → a ≡ treeCata tAlg (plug⇑ t s)
    unload-correct t n eq [] .n refl = sym eq
    unload-correct t n eq (Left x ∷ s) a p           = ⊥-elim (load-not-inj₂ x (inj₂ (n , t , eq) ∷ s) a  p)
    unload-correct t n eq (Right a′ t′ eq′ ∷ s) a p  = unload-correct (Node t′ t) (NodeA a′ n) (cong₂ NodeA eq′ eq) s a p
   
    stepIx-correct : (t : Tree) → (z : Zipper⇑ t) → ∀ a → stepIx t z ≡ inj₂ a → a ≡ treeCata tAlg t
    stepIx-correct t ((t₁ , s₁) ,, p) a x with step (t₁ , s₁) | inspect step (t₁ , s₁)
    stepIx-correct .(plug⇑ (Tip t₁) s₁) ((t₁ , s₁) ,, refl) a () | inj₁ (t₂ , s₂) | Reveal_·_is_.[ eq ]
    stepIx-correct .(plug⇑ (Tip t₁) s₁) ((t₁ , s₁) ,, refl) .y refl | inj₂ y | Reveal_·_is_.[ eq ] = unload-correct (Tip t₁) (TipA t₁) refl s₁ y eq
    
    rec-correct : (t : Tree) → (z : Zipper⇑ t) → (ac : Acc ([[ t ]]⇑_<_) z) → ∀ a → rec t z ac ≡ a → a ≡ treeCata tAlg t
    rec-correct t z (acc rs) a x with stepIx t z | inspect (stepIx t) z
    rec-correct t z (acc rs) a x | inj₁ z′    | [ eq ]                  = rec-correct t z′ (rs z′ (stepIx-< t z z′ eq)) a x
    rec-correct t z (acc rs) .a refl | inj₂ a | [ eq ]                  = stepIx-correct t z a eq
    
    correctness : ∀ t → foldTree t ≡ treeCata tAlg t
    correctness t with loadIx t [] | inspect (loadIx t) []
    correctness t | inj₁ z | _ with rec t z (<⇑-WF t z) | inspect (rec t z) (<⇑-WF t z)
    correctness t | inj₁ z | _ | a | Reveal_·_is_.[ eq ] = rec-correct t z (<⇑-WF t z) a eq
    correctness t | inj₂ y | [ eq ] = ⊥-elim (loadIx-not-inj₂ t [] y eq)

