module Thesis.Tree.One where

  open import Data.Sum
  open import Thesis.Data.Sum
  open import Data.Product
  open import Thesis.Data.Product
  open import Data.Unit
  open import Data.Empty
  
  open import Thesis.Data.List
  
  open import Induction.WellFounded
  open import Relation.Binary.PropositionalEquality

  open import Function
  open import Data.Nat hiding (_<_)
  open import Data.Nat.Properties
  open import Data.List
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Data.List.All
  
  reverse-++ : ∀ {A : Set} (s : List A) (x : A) → reverse (x ∷ s) ≡ reverse s ++ (x ∷ [])
  reverse-++ xs x = unfold-reverse x xs

  -- binary tree with nat on the leaves
  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  Node-injᵣ : ∀ {l r₁ r₂} → Node l r₁ ≡ Node l r₂ → r₁ ≡ r₂
  Node-injᵣ refl = refl

  Node-injₗ : ∀ {l₁ l₂ r} →  Node l₁ r ≡ Node l₂ r → l₁ ≡ l₂
  Node-injₗ refl = refl

  eval : Tree → ℕ
  eval (Tip x) = x
  eval (Node t t₁) = eval t + eval t₁

  Stack = List (Tree ⊎ ∃₂ λ t n → eval t ≡ n)

  pattern Left t       = inj₁ t
  pattern Right t n p  = inj₂ (t , n , p)

  plug⇑  : Tree → Stack → Tree
  plug⇑ t (Left   t₁ ∷ s)     = plug⇑ (Node t t₁) s
  plug⇑ t (Right  t₁ n p ∷ s) = plug⇑ (Node t₁ t) s
  plug⇑ t []                  = t

  plug⇓ : Tree → Stack → Tree
  plug⇓ t []                  = t
  plug⇓ t (Left t₁ ∷ s)       = Node (plug⇓ t s) t₁
  plug⇓ t (Right t₁ _ _ ∷ s)  = Node t₁ (plug⇓ t s)

  Zipper = (Σ ℕ λ n → Σ Tree λ t → (eval t ≡ n)) × Stack

  load : Tree → Stack → Zipper ⊎ ℕ
  load (Tip x) s      = inj₁ ((x , Tip x , refl) , s)
  load (Node t₁ t₂) s = load t₁ (Left t₂ ∷ s)

  unload : (t : Tree) → (n : ℕ) → eval t ≡ n → Stack → Zipper ⊎ ℕ
  unload t n eq []                     = inj₂ n
  unload t n eq (Left t′ ∷ s)          = load t′ (Right t n eq ∷ s)
  unload t n eq (Right t′ n′ eq′  ∷ s) = inj₁ ((n′ + n , (Node t′ t) , cong₂ _+_ eq′ eq) , s)

  plugZ⇑ : Zipper → Tree
  plugZ⇑ ((_ , t , _) , s) = plug⇑ t s

  plugZ⇓ : Zipper → Tree
  plugZ⇓ ((_ , t , _) , s) = plug⇓ t s

  data Zipper⇓ (t : Tree) : Set where
    _,_ : (z : Zipper) → plugZ⇓ z ≡ t → Zipper⇓ t

  data Zipper⇑ (t : Tree) : Set where
    _,_ : (z : Zipper) → plugZ⇑ z ≡ t → Zipper⇑ t
  
  data _<_ : Zipper → Zipper → Set where
      <-Right-Step  : ∀ {n} {l} {t₁} {t₂} {s₁ s₂} {eq : eval l ≡ n} → (t₁ , Right l n eq ∷ s₁) < (t₂ , Right l n eq ∷ s₂)
      <-Right-Base  : ∀ {n} {t} {eq} {t₁ n₁ p₁} {s}                 → ((n₁ + n , Node t₁ t , cong₂ _+_ p₁ eq) , s) < ((n₁ , t₁ , p₁) , Right t n eq ∷ s)
      <-Left-Step   : ∀ {r} {t₁} {t₂} {s₁ s₂}    → (t₁ , s₁) < (t₂ , s₂) → (t₁ , Left r ∷ s₁)       < (t₂ , Left r ∷ s₂)
      <-Right-Left  : ∀ {n} {t₁ t₂ s₁ s₂} {t₁′ t₂′}  {eq : eval t₁′ ≡ n} → (t₁′ ≡ plugZ⇓ (t₂ , s₂))
                                                                         → (t₂′ ≡ plugZ⇓ (t₁ , s₁)) → (t₁ , Right t₁′ n eq ∷ s₁) < (t₂ , Left t₂′ ∷ s₂)
    -- A relation over indexed Zipper⇓
  data [[_]]⇓_<_ : (t : Tree) → Zipper⇓ t → Zipper⇓ t → Set where
      <-Right-Step  : ∀ {a} {l r} {t₁ t₂} {s₁ s₂} {eq}
                    → ∀ eq₁ eq₂
                    → [[ r ]]⇓        ((t₁ , s₁)                 , Node-injᵣ eq₁)  < ((t₂ , s₂)                , Node-injᵣ eq₂)
                    → [[ Node l r ]]⇓ ((t₁ , Right l a eq ∷ s₁ ) , eq₁)            < ((t₂ , Right l a eq ∷ s₂) , eq₂)

      <-Left-Step  : ∀ {l r} {t₁ t₂} {s₁ s₂}
                    → ∀ eq₁ eq₂
                    → [[ l ]]⇓        ((t₁ , s₁)           , Node-injₗ eq₁) < ((t₂ , s₂ )               , Node-injₗ eq₂)
                    → [[ Node l r ]]⇓ ((t₁ , Left r  ∷ s₁) , eq₁)           < ((t₂ , Left r ∷ s₂ ) , eq₂)

      <-Right-Left  : ∀ {a} {l r} {t₁ t₂ s₁ s₂} {eq} {eq₁ eq₂} → [[ Node l r ]]⇓ ((t₁ , Right l a eq ∷ s₁) , eq₁) < ((t₂ , Left r ∷ s₂) , eq₂)

      <-Right-Base  : ∀ {e} {n} {t} {eq} {t₁ n₁ p₁} {s} {eq₁}
                    → [[ e ]]⇓ (((n + n₁ , Node t t₁ , cong₂ _+_ eq p₁) , s) , {!!}) < (((n₁ , t₁ , p₁) , Right t n eq ∷ s) , eq₁)
    
  -- mutual
  --   accR : ∀ {l r : Tree} t (s : Stack) eq₁
  --            {a : ℕ} {eq : eval l ≡ a} →
  --            Acc ([[_]]⇓_<_ r) ((t , s) , Node-injᵣ eq₁) →
  --            (y : Zipper⇓ (Node l r)) → [[ Node l r ]]⇓ y < ((t , Right l a eq ∷ s) , eq₁) → Acc ([[_]]⇓_<_ (Node l r)) y
  --   accR t s eq₁ {a} {eq} (acc rs) .((t₁ , Right _ a eq ∷ s₁) , refl) (<-Right-Step {t₁ = t₁} {s₁ = s₁} refl .eq₁ p) = acc (accR t₁ s₁ refl (rs ((t₁ , s₁) , refl) p))
  --   accR {l} .(n₁ , t₁ , p₁) s refl {eq = eq} (acc rs) .(((n + n₁ , Node l t₁ , cong₂ _+_ eq p₁) , s) , eq₁) (<-Right-Base {n = n} {t₁ = t₁} {n₁} {p₁} {eq₁ = eq₁}) = {!!}
      
  --   accL : ∀ {l r : Tree} t (s : Stack) eq₂ →
  --            (wrf : Well-founded [[ r ]]⇓_<_) →
  --            Acc ([[_]]⇓_<_ l) ((t , s ) , Node-injₗ eq₂) → 
  --            (y : Zipper⇓ (Node l r)) → [[ Node l r ]]⇓ y < ((t , inj₁ r ∷ s) , eq₂) → Acc ([[_]]⇓_<_ (Node l r)) y
  --   accL {r = r} t s eq₂ wfr (acc rs) .((t₁ , inj₁ r ∷ s₁) , refl) (<-Left-Step {t₁ = t₁} {s₁ = s₁} refl .eq₂ p)
  --     = acc (accL t₁ s₁ refl wfr (rs ((t₁ , s₁) , refl) p))
  --   accL {l} t s eq₂ wrf (acc rs) .((t₁ , Right l a eq ∷ s₁) , refl) (<-Right-Left {a} {t₁ = t₁} {s₁ = s₁} {eq = eq} {refl})
  --     = acc (accR t₁ s₁ refl (wrf ((t₁ , s₁) , refl)))

  --   <-WF : ∀ (t : Tree) → Well-founded ([[ t ]]⇓_<_)
  --   <-WF t x = acc (aux t x)
  --         where
  --           aux : ∀ (t : Tree) (x : Zipper⇓ t)
  --               (y : Zipper⇓ t) → [[ t ]]⇓ y < x → Acc ([[_]]⇓_<_ t) y
  --           aux .(Node l (plug⇓ n₁ s₁)) .(((t₂ , n₂ , p₂) , inj₂ (l , a , eq) ∷ s₂) , eq₂) .(((t₁ , n₁ , p₁) , inj₂ (l , a , eq) ∷ s₁) , refl)
  --             (<-Right-Step {a} {l} {t₁ = t₁ , n₁ , p₁} {t₂ , n₂ , p₂} {s₁} {s₂} {eq} refl eq₂ p)
  --             = acc (accR (t₁ , n₁ , p₁) s₁ refl (aux (plug⇓ n₁ s₁) (((t₂ , n₂ , p₂) , s₂) , Node-injᵣ eq₂) (((t₁ , n₁ , p₁) , s₁) , refl) p))
  --           aux .(Node (plug⇓ n₁ s₁) r) .(((t₂ , n₂ , p₂) , inj₁ r ∷ s₂) , eq₂) .(((t₁ , n₁ , p₁) , inj₁ r ∷ s₁) , refl)
  --             (<-Left-Step {r = r} {t₁ , n₁ , p₁} {t₂ , n₂ , p₂} {s₁} {s₂} refl eq₂ p)
  --             = acc (accL (t₁ , n₁ , p₁) s₁ refl (<-WF r) (aux (plug⇓ n₁ s₁) (((t₂ , n₂ , p₂) , s₂) , Node-injₗ eq₂) (((t₁ , n₁ , p₁) , s₁) , refl) p))
  --           aux .(Node (plug⇓ n₂ s₂) (plug⇓ n₁ s₁)) .(((t₂ , n₂ , p₂) , inj₁ (plug⇓ n₁ s₁) ∷ s₂) , refl) .(((t₁ , n₁ , p₁) , inj₂ (plug⇓ n₂ s₂ , _ , _) ∷ s₁) , refl)
  --             (<-Right-Left {l = .(plug⇓ n₂ s₂)} {.(plug⇓ n₁ s₁)} {t₁ , n₁ , p₁} {t₂ , n₂ , p₂} {s₁} {s₂} {eq₁ = refl} {refl})
  --             = acc (accR (t₁ , n₁ , p₁) s₁ refl (<-WF (plug⇓ n₁ s₁) (((t₁ , n₁ , p₁) , s₁) , refl)))
     
  -- -- unload-< : ∀ t n eq s t′ s′ → unload t n eq s ≡ inj₁ (t′ , s′) → (t′ , reverse s′) < ((n , t , eq) , reverse s)
  -- -- unload-< t n eq [] t′ s′ ()
  -- -- unload-< t n eq (Left l ∷ s) t′ s′ x = {!!}
  -- -- unload-< t n eq (inj₂ (t′′ , n′′ , eq′′) ∷ s) .(n + n′′ , Node t t′′ , cong₂ _+_ eq eq′′) .s refl
  -- --   with reverse (inj₂ (t′′ , n′′ , eq′′) ∷ s) | unfold-reverse (inj₂ (t′′ , n′′ , eq′′)) s
  -- -- unload-< t n eq (inj₂ (t′′ , n′′ , eq′′) ∷ s) .(n + n′′ , Node t t′′ , cong₂ _+_ eq eq′′) .s refl
  -- --   | .(reverse s ++ inj₂ (t′′ , n′′ , eq′′) ∷ []) | refl = {!!} -- this should be now straightforward
