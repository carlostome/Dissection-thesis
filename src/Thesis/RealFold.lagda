\begin{code}
module Thesis.RealFold where

  open import Induction.WellFounded
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Bool
  open import Function
  open import Data.Sum
  open import Data.Sum.Properties
  open import Thesis.Data.Sum.Inj
  open import Data.Empty
  open import Data.Nat hiding (_<_)
  open import Data.Nat.Properties

  open import Data.List
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Data.List.All
  open import Data.List.All.Properties

  open import Data.Unit

  -- some utilities not avaliable in the standard lib v14 (or I can't find them)
  private
    ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs = refl
    ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

  -- An algebra for Tree
  record TreeAlg : Set₁ where
    field
      α     : Set
      TipA  : ℕ → α
      NodeA : α → α → α

  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  Node-injₗ : ∀ {a b x y} → Node a b ≡ Node x y → a ≡ x
  Node-injₗ refl = refl

  Node-injᵣ : ∀ {a b x y} → Node a b ≡ Node x y → b ≡ y
  Node-injᵣ refl = refl

  -- catamorphism over Tree given a Tree Algebra
  treeCata : (tAlg : TreeAlg) → Tree → (TreeAlg.α tAlg)
  treeCata tAlg (Tip x)     = (TreeAlg.TipA  tAlg) x
  treeCata tAlg (Node t t₁) = (TreeAlg.NodeA tAlg) (treeCata tAlg t) (treeCata tAlg t₁)

  module _ (tAlg : TreeAlg) where

    open TreeAlg tAlg

    Stack :  Set
    Stack = List (Tree ⊎ Σ α λ a → Σ Tree λ t → treeCata tAlg t ≡ a)

    pattern Left t       = inj₁ t
    pattern Right r t p  = inj₂ (r , t , p)

    Zipper : Set
    Zipper = ℕ × Stack
    
    plug⇑  : Tree → Stack → Tree
    plug⇑ t (Left   t₁     ∷ s) = plug⇑ (Node t t₁) s
    plug⇑ t (Right  _ t₁ _ ∷ s) = plug⇑ (Node t₁ t) s
    plug⇑ t []                  = t

    plugZ⇑ : Zipper → Tree
    plugZ⇑ (n , s) = plug⇑ (Tip n) s

    plug⇓ : Tree → Stack → Tree
    plug⇓ t []                  = t
    plug⇓ t (Left t₁ ∷ s)       = Node (plug⇓ t s) t₁
    plug⇓ t (Right _ t₁ _ ∷ s)  = Node t₁ (plug⇓ t s)

    plugZ⇓ : Zipper → Tree
    plugZ⇓ (n , s) = plug⇓ (Tip n) s

    data _<_ : Zipper → Zipper → Set where
      <-Right-Step  : ∀ {a} {l} {t₁ t₂} {s₁ s₂} {eq : treeCata tAlg l ≡ a}
                    → (t₁ , s₁) < (t₂ , s₂)
                    →  (t₁ , Right a l eq ∷ s₁) < (t₂ , Right a l eq ∷ s₂)
      <-Left-Step   : ∀ {r} {t₁ t₂ s₁ s₂}
                    → (t₁ , s₁) < (t₂ , s₂)
                    →  (t₁ , Left r ∷ s₁)       < (t₂ , Left r ∷ s₂)
      <-Right-Left  : ∀ {a} {t₁ t₂ s₁ s₂} {t₁′ t₂′}  {eq : treeCata tAlg t₁′ ≡ a} → (t₁′ ≡ plug⇓ (Tip t₂) s₂)
                    → (t₂′ ≡ plug⇓ (Tip t₁) s₁)
                    → (t₁ , Right a t₁′ eq ∷ s₁) < (t₂ , Left t₂′ ∷ s₂)

    data [[_]]_<_ (t : Tree) : Zipper → Zipper → Set where
      lt : ∀ z₁ z₂ → plugZ⇓ z₁ ≡ t → plugZ⇓ z₂ ≡ t → z₁ < z₂ → [[ t ]] z₁ < z₂

    -- A result of a load/unload is either a value of type A or
    -- a Zipper that corresponds to the next leaf
    Result : Set
    Result = Zipper  ⊎ α

    load : Tree → Stack → Result
    load (Tip x) s      = inj₁ (x , s)
    load (Node t₁ t₂) s = load t₁ (Left t₂ ∷ s)

    unload : (t : Tree) → (r : α) → treeCata tAlg t ≡ r → Stack → Result
    unload t a eq []                    = inj₂ a
    unload t a eq (Left t′ ∷ s)         = load t′ (Right a t eq ∷ s)
    unload t a eq (Right a′ t′ eq′ ∷ s) = unload  (Node t′ t) ((NodeA) a′ a) (cong₂ (NodeA) eq′ eq) s

    step : Zipper → Result
    step (n , s)  = unload (Tip n) (TipA n) refl s

    convert : Zipper → Zipper
    convert (n , s) = (n , reverse s)

    load-preserves-plug⇑ :(t : Tree) (s : Stack) (t′ : ℕ) (s′ : Stack)
                       → load t s ≡ inj₁ (t′ , s′) → plug⇑ t s ≡ plug⇑ (Tip t′) s′
    load-preserves-plug⇑ (Tip n) s .n .s refl   = refl
    load-preserves-plug⇑ (Node t₁ t₂) s t′ s′ x = load-preserves-plug⇑ t₁ (inj₁ t₂ ∷ s) t′ s′ x

    unload-preserves-plug⇑ : (t : Tree) (a : α) (eq : treeCata tAlg t ≡ a) (s : Stack) (t′ : ℕ) (s′ : Stack)
                           → unload t a eq s ≡ inj₁ (t′ , s′) → plug⇑ t s ≡ plug⇑ (Tip t′) s′
    unload-preserves-plug⇑ t a eq [] t′ s′ ()
    unload-preserves-plug⇑ t a eq (Left x ∷ s) t′ s′ p         = load-preserves-plug⇑ x (Right a t eq ∷ s) t′ s′ p
    unload-preserves-plug⇑ t a eq (Right a′ x eq′ ∷ s) t′ s′ p = unload-preserves-plug⇑ (Node x t) (NodeA a′ a) (cong₂ (NodeA) eq′ eq) s t′ s′ p

    step-preserves-plug⇑ : (z z′ : Zipper) → step z ≡ inj₁ z′ → plugZ⇑ z ≡ plugZ⇑ z′
    step-preserves-plug⇑ (t , s) (t′ , s′) x = unload-preserves-plug⇑ (Tip t) (TipA t) refl s t′ s′ x

    mutual
      accR : (r l : Tree) (x : ℕ) (s : Stack) (a : α) (eq : treeCata tAlg l ≡ a)
           → Acc ([[ r ]]_<_) (x , s) → WfRec ([[ Node l r ]]_<_ ) (Acc ([[ Node l r ]]_<_)) (x , Right a l eq ∷ s)
      accR .(plug⇓ (Tip t₁) s₁) l x s a eq (acc rs) .(t₁ , Right a l eq ∷ s₁)
                                         (lt .(t₁ , Right a l eq ∷ s₁) .(x , Right a l eq ∷ s) refl eq₂ (<-Right-Step {t₁ = t₁} {s₁ = s₁} p))
           = acc (accR (plug⇓ (Tip t₁) s₁) l t₁ s₁ a eq (rs (t₁ , s₁) (lt (t₁ , s₁) (x , s) refl (Node-injᵣ eq₂) p)))

      accL : (l r : Tree) (x : ℕ) (s : Stack)
           →  Acc ([[ l ]]_<_) (x , s) → WfRec ([[ Node l r ]]_<_ ) (Acc ([[ Node l r  ]]_<_ )) (x , Left r ∷ s)
      accL l r x s (acc rs) (y , .(Left r ∷ s₁)) (lt .(y , Left r ∷ s₁) .(x , Left r ∷ s) eq₁ eq₂ (<-Left-Step {s₁ = s₁} p))
        = acc (accL l r y s₁ (rs (y , s₁) (lt (y , s₁) (x , s) (Node-injₗ eq₁) (Node-injₗ eq₂) p)))
      accL .(plug⇓ (Tip x) s) .(plug⇓ (Tip y) s₁) x s (acc rs) (y , .(Right a (plug⇓ (Tip x) s) eq ∷ s₁))
           (lt .(y , Right a (plug⇓ (Tip x) s) eq ∷ s₁) .(x , Left (plug⇓ (Tip y) s₁) ∷ s) refl eq₂ (<-Right-Left {a} {s₁ = s₁} {eq = eq} refl refl))
           = acc (accR  (plug⇓ (Tip y) s₁) (plug⇓ (Tip x) s) y s₁ a eq (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
    
      <-WF : ∀ t → Well-founded ([[ t ]]_<_)
      <-WF t x = acc (aux t x)
        where aux : (t : Tree) → (x : Zipper) → WfRec ([[ t ]]_<_) (Acc ([[ t ]]_<_)) x
              aux .(Node l (plug⇓ (Tip y) s₁)) (x , .(Right a l eq ∷ s₂)) (y , .(Right a l eq ∷ s₁))
                  (lt .(y , Right a l eq ∷ s₁) .(x , Right a l eq ∷ s₂) refl eq₂ (<-Right-Step {a} {l} {s₁ = s₁} {s₂} {eq} p))
                  = acc (accR (plug⇓ (Tip y) s₁) l y s₁ a eq (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
              aux .(Node (plug⇓ (Tip y) s₁) r) (x , .(Left r ∷ s₂)) (y , .(Left r ∷ s₁))
                  (lt .(y , Left r ∷ s₁) .(x , Left r ∷ s₂) refl eq₂ (<-Left-Step {r} {s₁ = s₁} {s₂} p))
                  = acc (accL (plug⇓ (Tip y) s₁) r y s₁ (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
              aux .(Node (plug⇓ (Tip x) s₂) (plug⇓ (Tip y) s₁)) (x , .(Left (plug⇓ (Tip y) s₁) ∷ s₂)) (y , .(Right a (plug⇓ (Tip x) s₂) eq ∷ s₁))
                  (lt .(y , Right a (plug⇓ (Tip x) s₂) eq ∷ s₁) .(x , Left (plug⇓ (Tip y) s₁) ∷ s₂) refl eq₂
                      (<-Right-Left {a} {s₁ = s₁} {s₂} {.(plug⇓ (Tip x) s₂)} {.(plug⇓ (Tip y) s₁)} {eq} refl refl))
                  = acc (accR (plug⇓ (Tip y) s₁) (plug⇓ (Tip x) s₂) y s₁ a eq (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
   
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

    prepend : ∀ {t₁ t₂ s₁ s₂} → (t₁ , s₁) < (t₂ , s₂) → ∀ s → (t₁ , s ++ s₁) < (t₂ , s ++ s₂)
    prepend x (Left t ∷ s)       = <-Left-Step  (prepend x s)
    prepend x (Right t n eq ∷ s) = <-Right-Step (prepend x s)         
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
            → (t′ , reverse s′) < (n , reverse (Left t ∷ s)) 
    load-< n eq (Tip x) s .x .(Right (TipA n) (Tip n) eq ∷ s) refl with reverse (Right (TipA n) (Tip n ) eq ∷ s) | reverse-++ s (Right (TipA n) (Tip n) eq)
    load-< n eq (Tip x) s .x .(Right (TipA n) (Tip n) eq ∷ s) refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      with reverse (Left (Tip x) ∷ s) | reverse-++ s (Left (Tip x))
    load-< n eq (Tip x) s .x .(Right (TipA n) (Tip n) eq ∷ s) refl
      | .(foldl _ [] s ++ Right (TipA n) (Tip n) eq ∷ []) | refl
      | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₁ (Tip x) ∷ []) | refl
      = prepend (<-Right-Left refl refl) (reverse s)
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
      | .(foldl (λ rev x → x ∷ rev) [] s ++ Right (TipA n) (Tip n) eq ∷ inj₁ t₂ ∷ []) | refl = prepend (<-Right-Left refl refl) (reverse s)
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
      = prepend (<-Right-Left refl (cong₂ Node (sym (trans (plug⇓-++-Left (reverse xs)) (sym (plug⇑-to-plug⇓ (Node (Tip t′) x) xs)))) refl)) (reverse s)

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

    unload-< : ∀ n eq s t′ s′ → unload (Tip n) (TipA n) eq s ≡ inj₁ (t′ , s′) → (t′ , reverse s′) < (n , reverse s)
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
      = prepend (<-Right-Left (sym (trans (plug⇓-++-Right (reverse pre)) (sym (plug⇑-to-plug⇓ (Node node (Tip n)) pre)))) refl) (reverse xs)
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
      = prepend (<-Right-Left (sym (trans (plug⇓-++-Right (reverse pre)) (sym (plug⇑-to-plug⇓ (Node node (Tip n)) pre))))
                                          (sym (trans (plug⇓-++-Left (reverse xs)) (sym (plug⇑-to-plug⇓ (Node (Tip t′) x) xs)) ))) (reverse ys)

    step-< : ∀ z z′ → step z ≡ inj₁ z′ → convert z′ < convert z
    step-< (n , []) z′ ()
    step-< (n , Left t′ ∷ s) (n′ , s′) x          = load-< n refl t′ s n′ s′ x
    step-< (n , Right t′ m eq′  ∷ s) (n′ , s′) x  = unload-< n refl (inj₂ (t′ , m , eq′) ∷ s) n′ s′ x

    rec : ∀ t s → Acc ([[ plug⇑ (Tip t) s ]]_<_) (t , reverse s) → α
    rec t  s (acc rs) with step (t , s) | inspect step (t , s)
    rec t  s (acc rs) | inj₁ (t′ , s′) | [ eq ]
      with plug⇑ (Tip t) s | step-preserves-plug⇑ (t , s) (t′ , s′) eq
    rec t s (acc rs) | inj₁ (t′ , s′) | Reveal_·_is_.[ eq ] | .(plug⇑ (Tip t′) s′) | refl
      = rec t′ s′ (rs (t′ , (reverse s′))
                   (lt (t′ , (reverse s′)) (t , reverse s)
                             (sym (plug⇑-to-plug⇓ (Tip t′) s′)) (trans (sym (plug⇑-to-plug⇓ (Tip t) s))
                             (step-preserves-plug⇑ (t , s) (t′ , s′) eq))
                             (step-< (t , s) (t′ , s′) eq)))
    rec t  s (acc rs) | inj₂ n  | eq = n

    foldTree : Tree → α
    foldTree t with load t []
    foldTree t | inj₁ (t′ , s′) = rec t′ s′ (<-WF (plug⇑ (Tip t′) s′) (t′ , (reverse s′)))
    foldTree t | inj₂ n         = n

    evalZipper⇑ : (a : α) → (s : Stack) → α
    evalZipper⇑ n []                  = n
    evalZipper⇑ n (Left x ∷ s)        = evalZipper⇑ (NodeA n (treeCata tAlg x)) s
    evalZipper⇑ n (Right n′ t eq ∷ s) = evalZipper⇑ (NodeA n′ n) s

    load-preserves-evalZipper⇑ : ∀ t s t′ s′  → load t s ≡ inj₁ (t′ , s′) → evalZipper⇑ (treeCata tAlg t) s ≡ evalZipper⇑ (TipA t′) s′
    load-preserves-evalZipper⇑ (Tip x₁) s .x₁ .s refl = refl
    load-preserves-evalZipper⇑ (Node t₁ t₂) s t′ s′ x = load-preserves-evalZipper⇑ t₁ (inj₁ t₂ ∷ s) t′ s′ x

    unload-preserves-evalZipper⇑ : ∀ t n eq s t′ s′ → unload t n eq s ≡ inj₁ (t′ , s′) → evalZipper⇑ n s ≡ evalZipper⇑ (TipA t′) s′
    unload-preserves-evalZipper⇑ t n eq [] t′ s′ ()
    unload-preserves-evalZipper⇑ t .(treeCata tAlg t) refl (Left x₁ ∷ s) t′ s′ x
      = load-preserves-evalZipper⇑ x₁ (Right (treeCata tAlg t) t refl ∷ s) t′ s′ x
    unload-preserves-evalZipper⇑ t .(treeCata tAlg t) refl (Right n′ t′′ eq′ ∷ s) t′ s′ x
      = unload-preserves-evalZipper⇑ (Node t′′ t) (NodeA n′ (treeCata tAlg t)) (cong₂ (NodeA) eq′ refl) s t′ s′ x

    step-preserves-evalZipper⇑  : ∀ t s t′ s′ → step (t , s) ≡ inj₁ (t′ , s′) →  evalZipper⇑ (TipA t) s ≡ evalZipper⇑ (TipA t′) s′
    step-preserves-evalZipper⇑ t s t′ s′ x = unload-preserves-evalZipper⇑ (Tip t) (TipA t) refl s t′ s′ x

    load-not-inj₂ : ∀ t s r → load t s ≡ inj₂ r → ⊥
    load-not-inj₂ (Tip x₁) s r ()
    load-not-inj₂ (Node t t₁) s r x = load-not-inj₂ t (inj₁ t₁ ∷ s) r x

    unload-preserves-evalZipper⇑2 : ∀ t n eq s r → unload t n eq s ≡ inj₂ r → evalZipper⇑ n s ≡ r
    unload-preserves-evalZipper⇑2 t n eq [] .n refl                = refl
    unload-preserves-evalZipper⇑2 t n eq (Left y ∷ s) n′ x         = ⊥-elim (load-not-inj₂ y (Right n t eq ∷ s) n′ x)
    unload-preserves-evalZipper⇑2 t n eq (Right n′ t′ eq′ ∷ s) r x = unload-preserves-evalZipper⇑2 (Node t′ t) (NodeA n′ n) (cong₂ (NodeA) eq′ eq) s r x

    lemma : ∀ t s ac n → rec t s ac ≡ n → evalZipper⇑ (TipA t) s ≡ n
    lemma t s (acc rs) n x with step (t , s) | inspect step (t , s)
    lemma t s (acc rs) n x | inj₁ (t′ , s′) | Reveal_·_is_.[ eq ] with plug⇑ (Tip t) s | step-preserves-plug⇑ (t , s) (t′ , s′) eq 
    lemma t s (acc rs) n x | inj₁ (t′ , s′) | Reveal_·_is_.[ eq ] | .(plug⇑ (Tip t′) s′) | refl
      with step-preserves-evalZipper⇑ t s t′ s′ eq
    ... | eq′ = trans eq′ (lemma t′ s′ (rs (t′ , (reverse s′))
                (lt (t′ , reverse s′) (t , reverse s) (sym (plug⇑-to-plug⇓ ((Tip t′)) s′)) ((trans (sym (plug⇑-to-plug⇓ (Tip t) s))
                             (step-preserves-plug⇑ (t , s) (t′ , s′) eq))) (step-< (t , s) (t′ , s′) eq))) n x)
    lemma t s (acc rs) .y refl | inj₂ y | Reveal_·_is_.[ eq ]     = unload-preserves-evalZipper⇑2 (Tip t) (TipA t) refl s y eq

    correctness : ∀ t → foldTree t ≡ treeCata tAlg t
    correctness t
      with load t []
         | inspect (load t) []
    correctness t | inj₁ (t′ , s′) | [ eq ]
      with rec t′ s′ (<-WF (plug⇑ (Tip t′) s′) (t′ , (reverse s′)))
         | inspect (rec t′ s′) (<-WF (plug⇑ (Tip t′) s′) (t′ , (reverse s′)))
    ... | n | [ eq′ ] = trans (sym (lemma t′ s′ (<-WF (plug⇑ (Tip t′) s′) (t′ , (reverse s′))) n eq′))
                              (sym (load-preserves-evalZipper⇑ t [] t′ s′ eq ))
    correctness t | inj₂ y | [ eq ] = ⊥-elim (load-not-inj₂ t [] y eq)
