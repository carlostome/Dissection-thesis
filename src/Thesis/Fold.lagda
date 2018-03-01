
\begin{code}
module Thesis.Fold where

  open import Induction.WellFounded
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Bool
  open import Function
  open import Data.Sum
  open import Data.Empty
  open import Data.Nat hiding (_<_)
  open import Data.Nat.Properties
  open import Data.List
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Data.List.All
  open import Coinduction
  open import Data.Unit

  -- some utilities not avaliable in the standard lib v14 (or I can't find them)
  private
    ⊎-injective₁ : ∀ {A B : Set} {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
    ⊎-injective₁ refl = refl

    ×-injective : ∀ {A B : Set} {x y a b} → (A × B ∋ (x , y)) ≡ (a , b) → x ≡ a × y ≡ b
    ×-injective refl = refl , refl

    ++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    ++-assoc [] ys zs       = refl
    ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

    ++-right-identity : ∀ {A : Set} (s : List A) → s ≡ s ++ []
    ++-right-identity [] = refl
    ++-right-identity (x ∷ s) = cong (x ∷_) (++-right-identity s)

    reverse-++ : ∀ {A : Set} (s : List A) (x : A) → reverse (x ∷ s) ≡ reverse s ++ (x ∷ [])
    reverse-++ [] x = refl
    reverse-++ (y ∷ s) x = {!!}

    reverse-reverse : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
    reverse-reverse [] = refl
    reverse-reverse (x ∷ xs) = {!!}

    lemmam : ∀ {A : Set} (y : A) (xs ys : List A) → xs ++ (y ∷ ys) ≡ (xs ++ (y ∷ [])) ++ ys
    lemmam y [] ys = refl
    lemmam y (x ∷ xs) ys = cong (x ∷_) (lemmam y xs ys)

  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  Node-inj-inv : ∀ {a b x y} → a ≡ x → b ≡ y → Node a b ≡ Node x y
  Node-inj-inv = {!!}
  eval : Tree → ℕ
  eval (Tip x) = x
  eval (Node t t₁) = eval t + eval t₁

  Stack = List (Tree ⊎ ∃₂ λ t n → eval t ≡ n)

  pattern Left t       = inj₁ t
  pattern Right t n p  = inj₂ (t , n , p)

  Zipper = ℕ × Stack

  plug⇑  : Tree → Stack → Tree
  plug⇑ t (Left   t₁ ∷ s)     = plug⇑ (Node t t₁) s
  plug⇑ t (Right  t₁ n p ∷ s) = plug⇑ (Node t₁ t) s
  plug⇑ t []                  = t

  plugZ⇑ : Zipper → Tree
  plugZ⇑ (n , s) = plug⇑ (Tip n) s

  plug⇓ : Tree → Stack → Tree
  plug⇓ t []                  = t
  plug⇓ t (Left t₁ ∷ s)       = Node (plug⇓ t s) t₁
  plug⇓ t (Right t₁ _ _ ∷ s)  = Node t₁ (plug⇓ t s)

  plugZ⇓ : Zipper → Tree
  plugZ⇓ (n , s) = plug⇓ (Tip n) s

  Node-injᵣ : ∀ {l r₁ r₂} → r₁ ≡ r₂ → Node l r₁ ≡ Node l r₂
  Node-injᵣ refl = refl

  Node-injₗ : ∀ {l₁ l₂ r} → l₁ ≡ l₂ → Node l₁ r ≡ Node l₂ r
  Node-injₗ refl = refl

  data _<_ : Zipper → Zipper → Set where
      <-Right-Step  : ∀ {n} {l} {t₁ t₂} {s₁ s₂} {eq : eval l ≡ n} → (t₁ , s₁) < (t₂ , s₂)   →  (t₁ , Right l n eq ∷ s₁) < (t₂ , Right l n eq ∷ s₂)
      <-Left-Step   : ∀ {r} {t₁ t₂ s₁ s₂}                         → (t₁ , s₁) < (t₂ , s₂)   →  (t₁ , Left r ∷ s₁)       < (t₂ , Left r ∷ s₂)
      <-Right-Left  : ∀ {n} {t₁ t₂ s₁ s₂} {t₁′ t₂′}  {eq : eval t₁′ ≡ n} → (t₁′ ≡ plug⇓ (Tip t₂) s₂)
                                                                         → (t₂′ ≡ plug⇓ (Tip t₁) s₁) → (t₁ , Right t₁′ n eq ∷ s₁) < (t₂ , Left t₂′ ∷ s₂)

  data [[_]]_<_ ( t : Tree) : Zipper → Zipper → Set where
    lt : ∀ z₁ z₂ → plugZ⇓ z₁ ≡ t → plugZ⇓ z₂ ≡ t → z₁ < z₂ → [[ t ]] z₁ < z₂
  
  mutual
    accR : ∀ r l x s n (eq : eval l ≡ n) → Acc ([[ r ]]_<_) (x , s) → WfRec ([[ Node l r ]]_<_ ) (Acc ([[ Node l r ]]_<_)) (x , Right l n eq ∷ s)
    accR .(plug⇓ (Tip t₁) s₁) l x s n eq (acc rs) .(t₁ , inj₂ (l , n , eq) ∷ s₁)
                                         (lt .(t₁ , inj₂ (l , n , eq) ∷ s₁) .(x , inj₂ (l , n , eq) ∷ s) refl eq₂ (<-Right-Step {t₁ = t₁} {s₁ = s₁} p))
      = acc (accR (plug⇓ (Tip t₁) s₁) l t₁ s₁ n eq (rs (t₁ , s₁) (lt (t₁ , s₁) (x , s) refl {!!} p)))
    accL : ∀ l r  x s →  Acc ([[ l ]]_<_) (x , s) → WfRec ([[ Node l r ]]_<_ ) (Acc ([[ Node l r  ]]_<_ )) (x , Left r ∷ s)
    accL l r x s (acc rs) (y , .(inj₁ r ∷ s₁)) (lt .(y , inj₁ r ∷ s₁) .(x , inj₁ r ∷ s) eq₁ eq₂ (<-Left-Step {s₁ = s₁} p))
      = acc (accL l r y s₁ (rs (y , s₁) (lt (y , s₁) (x , s) {!!} {!!} p)))
    accL .(plug⇓ (Tip x) s) .(plug⇓ (Tip y) s₁) x s (acc rs) (y , .(inj₂ (plug⇓ (Tip x) s , n , eq) ∷ s₁))
         (lt .(y , inj₂ (plug⇓ (Tip x) s , n , eq) ∷ s₁) .(x , inj₁ (plug⇓ (Tip y) s₁) ∷ s) refl eq₂ (<-Right-Left {n} {s₁ = s₁} {eq = eq} refl refl))
      = acc (accR (plug⇓ (Tip y) s₁) (plug⇓ (Tip x) s) y s₁ n eq (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
    
    <-WF : ∀ t → Well-founded [[ t ]]_<_
    <-WF t x = acc (aux t x)
      where aux : ∀ t x → WfRec ([[ t ]]_<_) (Acc ([[ t ]]_<_)) x
            aux .(Node l (plug⇓ (Tip y) s₁)) (x , .(inj₂ (l , n , eq) ∷ s₂)) (y , .(inj₂ (l , n , eq) ∷ s₁))
                (lt .(y , inj₂ (l , n , eq) ∷ s₁) .(x , inj₂ (l , n , eq) ∷ s₂) refl eq₂ (<-Right-Step {n} {l} {s₁ = s₁} {s₂} {eq} p))
                = acc (accR (plug⇓ (Tip y) s₁) l y s₁ n eq (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
            aux .(Node (plug⇓ (Tip y) s₁) r) (x , .(inj₁ r ∷ s₂)) (y , .(inj₁ r ∷ s₁))
                (lt .(y , inj₁ r ∷ s₁) .(x , inj₁ r ∷ s₂) refl eq₂ (<-Left-Step {r} {s₁ = s₁} {s₂} p))
                = acc (accL (plug⇓ (Tip y) s₁) r y s₁ (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
            aux .(Node (plug⇓ (Tip x) s₂) (plug⇓ (Tip y) s₁)) (x , .(inj₁ (plug⇓ (Tip y) s₁) ∷ s₂)) (y , .(inj₂ (plug⇓ (Tip x) s₂ , n , eq) ∷ s₁))
                (lt .(y , inj₂ (plug⇓ (Tip x) s₂ , n , eq) ∷ s₁) .(x , inj₁ (plug⇓ (Tip y) s₁) ∷ s₂) refl eq₂
                    (<-Right-Left {n} {s₁ = s₁} {s₂} {.(plug⇓ (Tip x) s₂)} {.(plug⇓ (Tip y) s₁)} {eq} refl refl))
                = acc (accR (plug⇓ (Tip y) s₁) (plug⇓ (Tip x) s₂) y s₁ n eq (<-WF (plug⇓ (Tip y) s₁) (y , s₁)))
  +-lemma : ∀ {a b} {x y} → a ≡ x → b ≡ y → a + b ≡ x + y
  +-lemma refl refl = refl

  load : Tree → Stack → Zipper ⊎ ℕ
  load (Tip x) s      = inj₁ (x , s)
  load (Node t₁ t₂) s = load t₁ (Left t₂ ∷ s)

  unload : (t : Tree) → (n : ℕ) → eval t ≡ n → Stack → Zipper ⊎ ℕ
  unload t n eq []                     = inj₂ n
  unload t n eq (Left t′ ∷ s)          = load t′ (Right t n eq ∷ s)
  unload t n eq (Right t′ n′ eq′  ∷ s) = unload (Node t′ t) (n′ + n) (+-lemma eq′ eq) s
          
  step : Zipper → Zipper ⊎ ℕ
  step (n , s)  = unload (Tip n) n refl s

  convert : Zipper → Zipper
  convert (n , s) = (n , reverse s)

  data Is-inj₁ {A B : Set} : A ⊎ B → Set where
    is-inj₁ : ∀ {x} → Is-inj₁ (inj₁ x)

  plug⇑-to-plug⇓ : ∀ (z : Zipper) → plugZ⇑ z ≡ plugZ⇓ (convert z)
  plug⇑-to-plug⇓ (t , s) = aux (Tip t) s (reverseView s)
    where aux : ∀ t s → Reverse s → plug⇑ t s ≡ plug⇓ t (reverse s)
          aux = {!!}
          
  All-++ : ∀ {A : Set} {P : A → Set} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
  All-++ {xs = []} {ys} [] x₁ = x₁
  All-++ {xs = x₂ ∷ xs} {ys} x x₁ = {!!}
  All-end : ∀ {A : Set} {P : A → Set} {xs : List A} {x : A} → All P xs → P x → All P (xs ++ (x ∷ []))
  All-end [] px          = px ∷ []
  All-end (px ∷ pxs) px' = px ∷ All-end pxs px'

  load-preserves-plug⇑ : ∀ t s t′ s′ → load t s ≡ inj₁ (t′ , s′) → plug⇑ t s ≡ plug⇑ (Tip t′) s′
  load-preserves-plug⇑ (Tip n) s .n .s refl   = refl
  load-preserves-plug⇑ (Node t₁ t₂) s t′ s′ x = load-preserves-plug⇑ t₁ (inj₁ t₂ ∷ s) t′ s′ x

  unload-preserves-plug⇑ : ∀ t n eq s t′ s′ → unload t n eq s ≡ inj₁ (t′ , s′) → plug⇑ t s ≡ plug⇑ (Tip t′) s′
  unload-preserves-plug⇑ t n eq [] t′ s′ ()
  unload-preserves-plug⇑ t n eq (Left x ∷ s) t′ s′ p         = load-preserves-plug⇑ x (inj₂ (t , n , eq) ∷ s) t′ s′ p
  unload-preserves-plug⇑ t n eq (Right x n′ eq′ ∷ s) t′ s′ p = unload-preserves-plug⇑ (Node x t) (n′ + n) (+-lemma eq′ eq) s t′ s′ p

  plug⇑-++-Right : ∀ x n t (p : eval t ≡ n) s → plug⇑ x (s ++ Right t n p ∷ []) ≡ Node t (plug⇑ x s)
  plug⇑-++-Right x n t p (Left t′ ∷ s)       = plug⇑-++-Right (Node x t′) n t p s
  plug⇑-++-Right x n t p (Right t′ n′ p′ ∷ s)   = plug⇑-++-Right (Node t′ x) n t p s
  plug⇑-++-Right _ _ _ _ []                   = refl

  plug⇑-++-Left : ∀ x t s → plug⇑ x (s ++  inj₁ t ∷ []) ≡ Node (plug⇑ x s) t
  plug⇑-++-Left x t′ (Left t ∷ s)       = plug⇑-++-Left (Node x t) t′ s
  plug⇑-++-Left x t′ (Right t n p ∷ s)  = plug⇑-++-Left (Node t x) t′ s
  plug⇑-++-Left _ _ []                 = refl

  plug⇓-++-Left : ∀ {x} {t} s → plug⇓ x (s ++ Left t ∷ []) ≡ plug⇓ (Node x t) s
  plug⇓-++-Left (Left t ∷ s)       = cong (flip Node t) (plug⇓-++-Left s)
  plug⇓-++-Left (Right t n p ∷ s)  = cong (Node t)      (plug⇓-++-Left s)
  plug⇓-++-Left []                 = refl

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
      , All-++ {xs = Left x ∷ xs} {ys = Left t₂ ∷ []} (is-inj₁ ∷ all) (is-inj₁ ∷ [])
      , plug⇑-++-Left (Node (Tip t′) x) t₂ xs
 
  load-< : ∀ n eq t  s t′ s′
         → load t (Right (Tip n) n eq ∷ s) ≡ inj₁ (t′ , s′)
         → (t′ , reverse s′) < (n , reverse (Left t ∷ s)) 
  load-< n eq (Tip x) s .x .(inj₂ (Tip n , n , eq) ∷ s) refl with reverse (Right (Tip n ) n eq ∷ s) | reverse-++ s (Right (Tip n) n eq)
  load-< n eq (Tip x) s .x .(inj₂ (Tip n , n , eq) ∷ s) refl
    | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl
    with reverse (Left (Tip x) ∷ s) | reverse-++ s (Left (Tip x))
  load-< n eq (Tip x) s .x .(inj₂ (Tip n , n , eq) ∷ s) refl
    | .(foldl _ [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl
    | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₁ (Tip x) ∷ []) | refl
    = prepend (<-Right-Left refl refl) (reverse s)
  load-< n eq (Node t₁ t₂) s t′ s′ p with load-stack-lemma t₁ t′ (inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) s′ p
  load-< n eq (Node .(Tip t′) t₂) s t′ .(inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) refl | .[] , refl , [] , refl
    with reverse (Left (Node (Tip t′) t₂) ∷ s) | reverse-++ s (Left (Node (Tip t′) t₂))
  load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) refl | .[] , refl , [] , refl
    | .(foldl (λ rev x → x ∷ rev) [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
    with reverse (Left t₂ ∷ Right (Tip n) n eq ∷ s) | reverse-++ (Right (Tip n) n eq ∷ s) (Left t₂)
  load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) refl
    | .[] , refl , [] , refl | .(foldl _ [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
    | .(foldl (λ rev x → x ∷ rev) (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    with reverse (Right (Tip n ) n eq ∷ s) | reverse-++ s (Right (Tip n) n eq)
  load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) refl | .[] , refl , [] , refl
    | .(foldl _ [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    | .(foldl (λ rev x → x ∷ rev) [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl
    with (reverse s ++ Right (Tip n) n eq ∷ []) ++ Left t₂ ∷ [] | ++-assoc (reverse s) (Right (Tip n) n eq ∷ []) (Left t₂ ∷ [])
  load-< n eq (Node .(Tip t′) t₂) s t′ .([] ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) refl | .[] , refl , [] , refl
    | .(foldl _ [] s ++ inj₁ (Node (Tip t′) t₂) ∷ []) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    | .(foldl _ [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl
    | .(foldl (λ rev x → x ∷ rev) [] s ++ inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) | refl = prepend (<-Right-Left refl refl) (reverse s)
  load-< n eq (Node t₁ t₂) s t′ .(inj₁ x ∷ xs ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
    with reverse (Left (Node t₁ t₂) ∷ s) | reverse-++ s (Left (Node t₁ t₂))
  load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
    | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl
    with reverse (Left x ∷ (xs ++ Left t₂ ∷ Right (Tip n) n eq ∷ s)) | reverse-++-commute  (Left x ∷ xs) (Left t₂ ∷ Right (Tip n) n eq ∷ s)
  load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
    | .(foldl _ [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl
    | .(foldl (λ rev x₁ → x₁ ∷ rev) (inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) s ++ foldl (λ rev x₁ → x₁ ∷ rev) (inj₁ x ∷ []) xs) | refl
    with reverse (Left t₂ ∷ Right (Tip n) n eq ∷ s) | reverse-++ (Right (Tip n) n eq ∷ s) (Left t₂)
  load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
    | .(foldl _ [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
    | .(foldl (λ rev x₁ → x₁ ∷ rev) (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    with reverse (Right (Tip n) n eq ∷ s) | reverse-++ s (Right (Tip n) n eq)
  load-< n eq (Node t₁ t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , plu
    | .(foldl _ [] s ++ inj₁ (Node t₁ t₂) ∷ []) | refl | .(foldl _ (inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl
    with reverse (Left x ∷ xs) | reverse-++ xs (Left x)
  load-< n eq (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl
    | .(foldl _ [] s ++ inj₁ (Node (plug⇑ (Node (Tip t′) x) xs) t₂) ∷ []) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    | .(foldl _ [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] xs ++ inj₁ x ∷ []) | refl
    with ((reverse s ++ (Right (Tip n) n eq ∷ [])) ++ (Left t₂ ∷ [])) | ++-assoc (reverse s) (Right (Tip n) n eq ∷ []) (Left t₂ ∷ [])
  load-< n eq (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl | .(foldl _ [] s ++ inj₁ (Node (plug⇑ (Node (Tip t′) x) xs) t₂) ∷ []) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    | .(foldl _ [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl
    | .(foldl _ [] xs ++ inj₁ x ∷ []) | refl | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) | refl
    with (reverse s ++ (Right (Tip n) n eq ∷ Left t₂ ∷ [])) ++ (reverse xs ++ Left x ∷ [])
         | ++-assoc (reverse s) (Right (Tip n) n eq ∷ Left t₂ ∷ []) (reverse xs ++ Left x ∷ [])
  load-< n eq (Node .(plug⇑ (Node (Tip t′) x) xs) t₂) s t′ .((inj₁ x ∷ xs) ++ inj₁ t₂ ∷ inj₂ (Tip n , n , eq) ∷ s) p
    | .(inj₁ x ∷ xs) , refl , _∷_ {.(inj₁ x)} {xs} (is-inj₁ {x}) all , refl
    | .(foldl _ [] s ++ inj₁ (Node (plug⇑ (Node (Tip t′) x) xs) t₂) ∷ []) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) s ++ foldl _ (inj₁ x ∷ []) xs) | refl
    | .(foldl _ (inj₂ (Tip n , n , eq) ∷ []) s ++ inj₁ t₂ ∷ []) | refl
    | .(foldl _ [] s ++ inj₂ (Tip n , n , eq) ∷ []) | refl | .(foldl _ [] xs ++ inj₁ x ∷ []) | refl
    | .(foldl _ [] s ++ inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ []) | refl
    | .(foldl (λ rev x₁ → x₁ ∷ rev) [] s ++ inj₂ (Tip n , n , eq) ∷ inj₁ t₂ ∷ foldl (λ rev x₁ → x₁ ∷ rev) [] xs ++ inj₁ x ∷ []) | refl
    = prepend (<-Right-Left refl (Node-inj-inv (sym (trans (plug⇓-++-Left (reverse xs)) (sym {!!}))) refl)) (reverse s)


  data Is-inj₂ {A B : Set} : A ⊎ B → Set where
    is-inj₂ : ∀ {x} → Is-inj₂ (inj₂ x)

  unload-stack-lemma : ∀ pre x post t n eq t′ s′ → All Is-inj₂ pre → unload t n eq (pre ++ Left x ∷ post) ≡ inj₁ (t′ , s′)
                     → ∃ λ s
                       → s′ ≡ s ++ Right (plug⇑ t pre) (eval (plug⇑ t pre)) refl ∷ post
                       × All Is-inj₁ s
                       × plug⇑ (Tip t′) s ≡ x
  unload-stack-lemma [] x post t .(eval t) refl t′ s′ [] p = load-stack-lemma x t′ (inj₂ (t , eval t , refl) ∷ post) s′ p
  unload-stack-lemma (inj₁ x₂ ∷ pre) x post t n eq t′ s′ (() ∷ x₁) p
  unload-stack-lemma (inj₂ (y , .(eval y) , refl) ∷ pre) x post t .(eval t) refl t′ s′ (is-inj₂ ∷ all) p
    with unload-stack-lemma pre x post (Node y t) (eval y + eval t) refl t′ s′ all p
  unload-stack-lemma (inj₂ (y , .(eval y) , refl) ∷ pre) .(plug⇑ (Tip t′) ss) post t .(eval t) refl t′ .(ss ++ inj₂ (plug⇑ (Node y t) pre , eval (plug⇑ (Node y t) pre) , refl) ∷ post) (is-inj₂ ∷ all) p | ss , refl , al , refl = ss , refl , al , refl

  data View : Stack → Set where
    Empty : View []
    AllOf  : ∀ xs → All Is-inj₂ xs → View xs
    Prefix : ∀ pre x xs → All Is-inj₂ pre → View (pre ++ (Left x ∷ xs))

  toView : ∀ s → View s
  toView [] = Empty
  toView (inj₁ x ∷ s) = Prefix [] x s []
  toView (inj₂ y ∷ s) with toView s
  toView (inj₂ y ∷ .[]) | Empty                                = AllOf (inj₂ y ∷ []) (is-inj₂ ∷ [])
  toView (inj₂ y ∷ s) | AllOf .s x                             = AllOf (inj₂ y ∷ s) (is-inj₂ ∷ x)
  toView (inj₂ y ∷ .(pre ++ inj₁ x ∷ xs)) | Prefix pre x xs x₁ = Prefix (inj₂ y ∷ pre) x xs (is-inj₂ ∷ x₁)

  unload-< : ∀ n eq s t′ s′ → unload (Tip n) n eq s ≡ inj₁ (t′ , s′) → (t′ , reverse s′) < (n , reverse s)
  unload-< n eq [] t′ s′ ()
  unload-< n eq (Left x₁ ∷ s) t′ s′ x                 = load-< n eq x₁ s t′ s′ x
  unload-< n eq (inj₂ (node , val , eq′) ∷ s) t′ s′ p with toView s
  unload-< n eq (inj₂ (node , val , eq′) ∷ .[]) t′ s′ () | Empty
  unload-< n eq (inj₂ (node , val , eq′) ∷ s) t′ s′ p | AllOf .s x = {!!} -- contradiction
  unload-< n eq (inj₂ (node , val , eq′) ∷ .(pre ++ inj₁ x ∷ xs)) t′ s′ p | Prefix pre x xs all
    with unload-stack-lemma pre x xs (Node node (Tip n)) (val + n) (+-lemma eq′ eq) t′ s′ all p
  unload-< n eq (inj₂ (node , val , eq′) ∷ .(pre ++ inj₁ (Tip t′) ∷ xs)) t′ .(inj₂ (plug⇑ (Node node (Tip n)) pre , eval (plug⇑ (Node node (Tip n)) pre) , refl) ∷ xs) p | Prefix pre .(Tip t′) xs all | .[] , refl , [] , refl = {!!}
  unload-< n eq (inj₂ (node , val , eq′) ∷ .(pre ++ inj₁ (plug⇑ (Tip t′) (y ∷ ys)) ∷ xs)) t′.(y ∷ ys ++ inj₂ (plug⇑ (Node node (Tip n)) pre , eval (plug⇑ (Node node (Tip n)) pre) , refl) ∷ xs) p | Prefix pre .(plug⇑ (Tip t′) (y ∷ ys)) xs all | .(_ ∷ _) , refl , _∷_ {y} {ys} px al , refl = {!px!}

  -- step-< : ∀ z z′ → step z ≡ inj₁ z′ → convert z′ < convert z
  -- step-< (n , []) z′ ()
  -- step-< (n , Left t′ ∷ s) (n′ , s′) x          = load-< n refl t′ s n′ s′ x
  -- step-< (n , Right t′ m eq′  ∷ s) (n′ , s′) x  = unload-< n refl (inj₂ (t′ , m , eq′) ∷ s) n′ s′ x -- -? - unload-< n refl (inj₂ (t′ , m , eq′) ∷ s) n′ s′ x
