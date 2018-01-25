\begin{code}
module Thesis.Cata where

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

    ++-RI : ∀ {A : Set} (s : List A) → s ≡ s ++ []
    ++-RI [] = refl
    ++-RI (x ∷ s) = cong (x ∷_) (++-RI s)

    -- true story
    reverse-++ : ∀ {A : Set} (s : List A) (x : A) → reverse (x ∷ s) ≡ reverse s ++ (x ∷ [])
    reverse-++ [] x = refl
    reverse-++ (y ∷ s) x = {!!}

  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree

  Node-inj : ∀ {a b x y } → Node a b ≡ Node x y → a ≡ x × b ≡ y
  Node-inj refl = refl , refl

  eval : Tree → ℕ
  eval (Tip x) = x
  eval (Node t t₁) = eval t + eval t₁

  -- We not only store the natural number to which it evaluates but also the
  -- tree from which it originates for proving purposes we cannot make both the
  -- tree and the proof irrelevant because the proof depends both on the tree
  -- and the number.
  -- No more a custom stack but just a list
  Stack = List (Tree ⊎ ∃₂ λ t n → eval t ≡ n)

  pattern Left t       = inj₁ t
  pattern Right t n p  = inj₂ (t , n , p)

  Zipper = Tree × Stack

  -- plugging upwards and downwards forgets the result of evaluation
  -- and its proof.
  _⊲_  : Tree → Stack → Tree
  t ⊲ (Left  t₁ ∷ s)     = Node (t ⊲ s) t₁
  t ⊲ (Right t₁ n p ∷ s) = Node t₁ (t ⊲ s)
  t ⊲ []            = t

  plug-⊲ : Zipper → Tree
  plug-⊲ (t , s) = t ⊲ s

  _⊳_  : Tree → Stack → Tree
  t ⊳ (Left   t₁ ∷ s)     = Node t t₁ ⊳ s
  t ⊳ (Right  t₁ n p ∷ s) = Node t₁ t ⊳ s
  t ⊳ []             = t

  plug-⊳ : Zipper → Tree
  plug-⊳ (t , s) = t ⊳ s

  -- Helper functions to move right and fold

  -- go all the way down to the leftmost leaf. Combined with right is not tail-recursive but
  -- threading the type Zipper ⊎ ℕ is.
  to-left : Tree → Stack → Zipper
  to-left (Tip x) s       = (Tip x , s)
  to-left (Node t₁ t₂) s  = to-left t₁ (Left t₂ ∷ s)

  -- traverse the stack all the way up, and stop in the right subtree of the topmost node.
  to-up-right : (t : Tree) → (n : ℕ) → eval t ≡ n → Stack → Zipper ⊎ ℕ
  to-up-right t n eq (Left t₁ ∷ s)                            = inj₁ (t₁ , Right t n eq ∷ s)
  to-up-right t .(eval t) refl (Right t₁ .(eval t₁) refl ∷ s) = to-up-right (Node t₁ t) (eval t₁ + eval t) refl s
  to-up-right t n eq []                                       = inj₂ n

  right : (z : Zipper) → Zipper ⊎ ℕ
  right (Tip x , Left t ∷ s)            = inj₁ ((t , (Right (Tip x) x refl ∷ s)))
  right (Tip x , Right t n eq ∷ s)      = to-up-right (Tip x) x refl (Right t n eq ∷ s)
  right (Tip x , [])                    = inj₂ x
  right (Node t₁ t₂ , Right t n eq ∷ s) = inj₁ (to-left (Node t₁ t₂) (Right t n eq ∷ s))

  -- these two are bogus, we rule them out using the property below
  right (Node t₁ t₂ , [])               = inj₁ (Node t₁ t₂ , [])
  right (Node t₁ t₂ , Left t ∷ s)       = inj₁ (Node t₁ t₂ , Left t ∷ s)

  -- Preservation of the Tree structure
  to-left-preserves-⊳ : ∀ t t′ s s′ → to-left t s ≡ (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  to-left-preserves-⊳ (Tip x₁) .(Tip x₁) s .s refl = refl
  to-left-preserves-⊳ (Node t t₁) t′ s s′ x = to-left-preserves-⊳ t t′ (Left t₁ ∷ s) s′ x

  to-up-right-preserves-⊳ : ∀ t s t′ s′ n eq → to-up-right t n eq s ≡ inj₁ (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  to-up-right-preserves-⊳ t [] t′ s′ n eq ()
  to-up-right-preserves-⊳ t (Left t₁ ∷ s) .t₁ .(Right t  (eval t)  refl ∷ s) .(eval t) refl refl = refl
  to-up-right-preserves-⊳ t (inj₂ (t₁ , .(eval t₁) , refl) ∷ s) t′ s′ .(eval t) refl x
    = to-up-right-preserves-⊳ (Node t₁ t) s t′ s′ (eval t₁ + eval t) refl x

  right-preserves-⊳ : ∀ t s t′ s′ → right (t , s) ≡ inj₁ (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  right-preserves-⊳ (Tip x) [] t′ s′ ()
  right-preserves-⊳ (Tip x) (Left t ∷ s) .t .(Right (Tip x) x  refl ∷ s) refl = refl
  right-preserves-⊳ (Tip x) (Right t n eq ∷ s) t′ s′ p = to-up-right-preserves-⊳ (Tip x) (Right t  n  eq ∷ s) t′ s′ x refl p
  right-preserves-⊳ (Node t t₁) [] .(Node t t₁) .[] refl = refl
  right-preserves-⊳ (Node t t₁) (Left t₂ ∷ s) .(Node t t₁) .(Left t₂  ∷ s) refl = refl
  right-preserves-⊳ (Node t t₁) (inj₂ (y , a , b) ∷ s) t′ s′ x = to-left-preserves-⊳ t t′ (inj₁ t₁ ∷ inj₂ (y , a , b) ∷ s) s′ (⊎-injective₁ x)

  right-preserves-⊳' : ∀ z z′ → right z ≡ inj₁ z′ → plug-⊳ z ≡ plug-⊳ z′
  right-preserves-⊳' (x , s₁) (y , s₂) eq = right-preserves-⊳ x s₁ y s₂ eq

  -- Rule out 'bogus' Zippers
  ZipperP : Zipper → Set
  ZipperP (Tip x      , s)                   = ⊤
  ZipperP (Node t₁ t₂ ,                 [])  = ⊥
  ZipperP (Node t₁ t₂ ,         Left _ ∷ s)  = ⊥
  ZipperP (Node t₁ t₂ , Right t′ n  eq ∷ s)  = ⊤

  -- The functions taking a proper Zipper do not deliver a bogus one
  ZipperP-to-left : ∀ t s t′ s′ → to-left t s ≡ (t′ , s′) → ZipperP (t′ , s′)
  ZipperP-to-left (Tip x) s .(Tip x) .s refl = tt
  ZipperP-to-left (Node t₁ t₂) s t′ s′ p     = ZipperP-to-left t₁ (inj₁ t₂ ∷ s) t′ s′ p

  ZipperP-to-up-right : ∀ t n (eq : eval t ≡ n) s z′ → to-up-right t n eq s ≡ inj₁ z′ → ZipperP z′
  ZipperP-to-up-right t n eq [] z′ ()
  ZipperP-to-up-right t n eq (inj₁ (Tip x) ∷ s) .(Tip x , inj₂ (t , n , eq) ∷ s) refl = tt
  ZipperP-to-up-right t n eq (inj₁ (Node x₁ x₂) ∷ s) .(Node x₁ x₂ , inj₂ (t , n , eq) ∷ s) refl = tt
  ZipperP-to-up-right t .(eval t) refl (inj₂ (t′ , .(eval t′) , refl) ∷ s) z′ x = ZipperP-to-up-right (Node t′ t) (eval t′ + eval t) refl s z′ x

  ZipperP-right : ∀ z z′ → right z ≡ inj₁ z′ → ZipperP z → ZipperP z′
  ZipperP-right (Tip x , []) z′ () zP
  ZipperP-right (Tip x , inj₁ (Tip x₁) ∷ s) .(Tip x₁ , inj₂ (Tip x , x , refl) ∷ s) refl zP = tt
  ZipperP-right (Tip x , inj₁ (Node t t₁) ∷ s) .(Node t t₁ , inj₂ (Tip x , x , refl) ∷ s) refl zP = tt
  ZipperP-right (Tip x , Right t n eq ∷ s) z′ rP zP = ZipperP-to-up-right (Tip x) x refl (inj₂ (t , n , eq) ∷ s) z′ rP
  ZipperP-right (Node t₁ t₂ , []) z′ rP ()
  ZipperP-right (Node t₁ t₂ , inj₁ x ∷ s) z′ rP ()
  ZipperP-right (Node t₁ t₂ , inj₂ y ∷ s) z′ rP zP = ZipperP-to-left t₁ (inj₁ t₂ ∷ inj₂ y ∷ s) (proj₁ z′) (proj₂ z′) (⊎-injective₁ rP)

  -- the relation is adapted to hold evaluations
  data _<_ : Zipper → Zipper → Set where
    <-Right-Step  : ∀ {n t t₁ t₂ s₁ s₂} {eq : eval t ≡ n} → (t₁ , s₁) < (t₂ , s₂) →  (t₁ , Right t n eq ∷ s₁)    < (t₂ , Right t n eq ∷ s₂)
    <-Left-Step   : ∀ {t t₁ t₂ s₁ s₂}    → (t₁ , s₁) < (t₂ , s₂) → (t₁ , Left t ∷ s₁)                            < (t₂ , Left t ∷ s₂)
    <-Right-Left  : ∀ {t₁ t₂ s₁ s₂}      → (t₁ , Right (t₂ ⊲ s₂) (eval (t₂ ⊲ s₂)) refl ∷ s₁)                    < (t₂ , Left (t₁ ⊲ s₁) ∷ s₂)
    <-Right-Base  : ∀ {t t₁ s₁} {n} {eq : eval t₁ ≡ n}          → (t  , Right t₁ n eq  ∷     s₁)                  < (Node t₁ (t ⊲ s₁) , [])
    <-Left-Base   : ∀ {t t₁ s₁}          → (Node (t ⊲ s₁) t₁  , [])                                              < (t , Left t₁ ∷ s₁)

  data [[_]]_<_ ( t : Tree) : Zipper → Zipper → Set where
    lt : ∀ z₁ z₂ → plug-⊲ z₁ ≡ t → plug-⊲ z₂ ≡ t → z₁ < z₂ → [[ t ]] z₁ < z₂

  mutual
    accR : ∀ t t₁ x n (eq : eval t₁ ≡ n) → Acc ([[ t ]]_<_) x → WfRec ([[ Node t₁ t ]]_<_ ) (Acc ([[ Node t₁ t ]]_<_)) (proj₁ x , Right t₁ n eq ∷ (proj₂ x))
    accR .(y ⊲ s₁) t₁ x n eq (acc rs) (y , .(inj₂ (t₁ , n , eq) ∷ s₁)) (lt .(y , inj₂ (t₁ , n , eq) ∷ s₁)
                                       .(proj₁ x , inj₂ (t₁ , n , eq) ∷ proj₂ x) refl eq₂ (<-Right-Step {s₁ = s₁} p))
         = acc (accR (y ⊲ s₁) t₁ (y , s₁) n eq (rs (y , s₁) (lt (y , s₁) x refl (proj₂ (Node-inj eq₂)) p)))

    accL : ∀ t t₁ x →  Acc ([[ t ]]_<_) x → WfRec ([[ Node t t₁ ]]_<_ ) (Acc ([[ Node t t₁  ]]_<_ )) (proj₁ x , Left t₁ ∷ (proj₂ x))
    accL .(y ⊲ s₁) t₁ (x , s) (acc rs) (y , .(inj₁ t₁ ∷ _)) (lt .(y , inj₁ t₁ ∷ _) .(x , inj₁ t₁ ∷ s) refl eq₂ (<-Left-Step {s₁ = s₁} p))
        = acc (accL (y ⊲ s₁) t₁ (y , s₁) (rs (y , s₁) (lt (y , s₁) (x , s) refl (proj₁ (Node-inj eq₂)) p)))
    accL .(x ⊲ s) .(y ⊲ s₁) (x , s) (acc rs) (y , .(inj₂ ((x ⊲ s) , eval (x ⊲ s) , refl) ∷ s₁))
                                              (lt .(y , inj₂ ((x ⊲ s) , eval (x ⊲ s) , refl) ∷ s₁)
                                                  .(x , inj₁ (y ⊲ s₁) ∷ s) refl eq₂ (<-Right-Left {s₁ = s₁}))
        = acc (accR (y ⊲ s₁) (x ⊲ s) (y , s₁) (eval (x ⊲ s)) refl (<-WF (y ⊲ s₁) (y , s₁)))
    accL .(x ⊲ s) t₁ (x , s) (acc rs) (.(Node (x ⊲ s) t₁) , .[]) (lt .(Node (x ⊲ s) t₁ , []) .(x , inj₁ t₁ ∷ s) refl eq₂ <-Left-Base)
        = acc (accH (x ⊲ s) t₁)

    accH : ∀ t₁ t₂ → WfRec ([[ Node t₁ t₂ ]]_<_) (Acc ([[ Node t₁ t₂ ]]_<_ )) (Node t₁ t₂ , [])
    accH t₁ .(y ⊲ s₁) (y , .(inj₂ (t₁ , n , eq) ∷ s₁))
                      (lt .(y , inj₂ (t₁ , n , eq) ∷ s₁)
                          .(Node t₁ (y ⊲ s₁) , []) refl eq₂
                          (<-Right-Base {s₁ = s₁} {n = n} {eq = eq}))
         = acc (accR (y ⊲ s₁) t₁ (y , s₁) n eq (<-WF (y ⊲ s₁) (y , s₁)))

    <-WF : ∀ t → Well-founded [[ t ]]_<_
    <-WF t x = acc (aux t x)
      where aux : ∀ t x → WfRec ([[ t ]]_<_) (Acc ([[ t ]]_<_)) x
            aux .(Node t (y ⊲ s₁)) (x , .(inj₂ (t , eval t , refl) ∷ _)) (y , .(inj₂ (t , eval t , refl) ∷ s₁))
                (lt .(y , inj₂ (t , eval t , refl) ∷ s₁)
                    .(x , inj₂ (t , eval t , refl) ∷ _) refl eq₂
                    (<-Right-Step {.(eval t)} {t} {.y} {.x} {s₁} {eq = refl} p))
                = acc (accR (y ⊲ s₁) t (y , s₁) (eval t) refl (<-WF (y ⊲ s₁) (y , s₁)))
            aux .(Node (y ⊲ s₁) t) (x , .(inj₁ t ∷ s₂)) (y , .(inj₁ t ∷ s₁))
                (lt .(y , inj₁ t ∷ s₁)
                    .(x , inj₁ t ∷ s₂) refl eq₂
                    (<-Left-Step {t} {.y} {.x} {s₁} {s₂} p))
                = acc (accL (y ⊲ s₁) t (y , s₁) (<-WF (y ⊲ s₁) (y , s₁)))
            aux .(Node (x ⊲ s₂) (y ⊲ s₁)) (x , .(inj₁ (y ⊲ s₁) ∷ s₂)) (y , .(inj₂ ((x ⊲ s₂) , eval (x ⊲ s₂) , refl) ∷ s₁))
                 (lt .(y , inj₂ ((x ⊲ s₂) , eval (x ⊲ s₂) , refl) ∷ s₁)
                     .(x , inj₁ (y ⊲ s₁) ∷ s₂) refl eq₂
                     (<-Right-Left {s₁ = s₁} {s₂}))
                = acc (accR (y ⊲ s₁) (x ⊲ s₂) (y , s₁) (eval (x ⊲ s₂)) refl (<-WF (y ⊲ s₁) (y , s₁)))
            aux .(Node t₁ (y ⊲ s₁)) (.(Node t₁ (y ⊲ s₁)) , .[]) (y , .(inj₂ (t₁ , n , eq) ∷ s₁))
                 (lt .(y , inj₂ (t₁ , n , eq) ∷ s₁)
                     .(Node t₁ (y ⊲ s₁) , []) refl eq₂
                     (<-Right-Base {.y} {t₁} {s₁} {n = n} {eq = eq}))
               = acc (accR (y ⊲ s₁) t₁ (y , s₁) n eq (<-WF (y ⊲ s₁) (y , s₁)))
            aux .(Node (x ⊲ s₁) t₁) (x , .(inj₁ t₁ ∷ s₁)) (.(Node (x ⊲ s₁) t₁) , .[])
                (lt .(Node (x ⊲ s₁) t₁ , [])
                    .(x , inj₁ t₁ ∷ s₁) refl eq₂
                    (<-Left-Base {.x} {t₁} {s₁}))
              = acc (accH (x ⊲ s₁) t₁)

  ⊳-++-Right : ∀ {x} {n} {t} {p : eval t ≡ n} s → x ⊳ (s ++ Right t n p ∷ []) ≡ Node t (x ⊳ s)
  ⊳-++-Right (Left t ∷ s)       = ⊳-++-Right s
  ⊳-++-Right (Right t n p ∷ s)  = ⊳-++-Right s
  ⊳-++-Right []                 = refl

  ⊳-++-Left : ∀ {x} {t} s → x ⊳ (s ++  inj₁ t ∷ []) ≡ Node (x ⊳ s) t
  ⊳-++-Left (Left t ∷ s)       = ⊳-++-Left s
  ⊳-++-Left (Right t n p ∷ s)  = ⊳-++-Left s
  ⊳-++-Left []                 = refl

  ⊲-++-Right : ∀ {x} {n} {t} {p : eval t ≡ n} s → x ⊲ (s ++ Right t n p ∷ []) ≡ Node t x ⊲ s
  ⊲-++-Right (Left t ∷ s)       = cong (flip Node t) (⊲-++-Right s)
  ⊲-++-Right (Right t n p ∷ s)  = cong (Node t) (⊲-++-Right s)
  ⊲-++-Right []              = refl

  ⊲-++-Left : ∀ {x} {t} s → x ⊲ (s ++ Left t ∷ []) ≡ Node x t ⊲ s
  ⊲-++-Left (Left t ∷ s)       = cong (flip Node t) (⊲-++-Left s)
  ⊲-++-Left (Right t n p ∷ s)  = cong (Node t)      (⊲-++-Left s)
  ⊲-++-Left []                 = refl

  convert : Zipper → Zipper
  convert (t , s) = t , reverse s

  ⊳-to-⊲ : ∀ (z : Zipper) → plug-⊳ z ≡ plug-⊲ (convert z)
  ⊳-to-⊲ (t , s) = aux t s (reverseView s)
    where aux : ∀ t s → Reverse s → t ⊳ s ≡ t ⊲ (reverse s)
          aux t .[] [] = refl
          aux t .(s ++ Left t₁ ∷ []) (s ∶ x ∶ʳ Left t₁)
            rewrite reverse-++-commute s (Left t₁ ∷ [])
                  | ⊳-++-Left {t} {t₁} s                   = cong (flip Node t₁) (aux t s x)
          aux t .(s ++ Right t₁ n eq ∷ []) (s ∶ x ∶ʳ Right t₁ n eq)
            rewrite reverse-++-commute s (Right t₁ n eq ∷ [])
                  | ⊳-++-Right {t} {n} {t₁} {eq} s         = cong (Node t₁) (aux t s x)


  ⊲-to-⊳ : (z : Zipper) → plug-⊲ z ≡ plug-⊳ (convert z)
  ⊲-to-⊳ (t , s) = aux t s (reverseView s)
    where aux : ∀ t s → Reverse s → t ⊲ s ≡ t ⊳ (reverse s)
          aux t .[] [] = refl
          aux t .(s ++ Right t₁ n eq ∷ []) (s ∶ x ∶ʳ Right t₁ n eq)
            rewrite reverse-++-commute s (Right t₁ n eq ∷ [])
                  | ⊲-++-Right {t} {n} {t₁} {eq} s        = aux (Node t₁ t) s x
          aux t .(s ++ Left t₁ ∷ []) (s ∶ x ∶ʳ Left t₁)
            rewrite reverse-++-commute s (Left t₁ ∷ [])
                  | ⊲-++-Left {t} {t₁} s                  = aux (Node t t₁) s x

  One-Up : Zipper → Zipper
  One-Up (x , [])                   = x , []
  One-Up (t₁ , Left t₂ ∷ s)         = t₁ , Left t₂ ∷ s
  One-Up (t₂ , Right t₁ n eq ∷ s)   = Node t₁ t₂ , s

  -- prepending some stack doesn't change the ordering
  prepend : ∀ {t₁ t₂ s₁ s₂} → (t₁ , s₁) < (t₂ , s₂) → ∀ s → (t₁ , s ++ s₁) < (t₂ , s ++ s₂)
  prepend x (Left t ∷ s)       = <-Left-Step  (prepend x s)
  prepend x (Right t n eq ∷ s) = <-Right-Step (prepend x s)
  prepend x []                 = x

  lemma : ∀ z → plug-⊲ (convert (One-Up z)) ≡ plug-⊲ (convert z)
  lemma (x , []) = refl
  lemma (x , Left t ∷ s) = refl
  lemma (x , Right t n eq ∷ s) rewrite reverse-++ s (inj₂ (t , n , eq))= sym (⊲-++-Right (reverse s))


  propi : ∀ t₁ t₂ s → convert (Node t₁ t₂ , s) < convert (t₁ , inj₁ t₂ ∷ s)
  propi  t₁ t₂ s rewrite ++-RI (reverse s) | reverse-++ s (inj₁ t₂) = prepend {s₁ = []} {s₂ = inj₁ t₂ ∷ []} <-Left-Base (reverse s)

  -- this should be provable. to-right-up only returns inj₁ (t , s) when this position is on the right subtree
  -- of the node of which left subtree we are currently in.
  to-u : ∀ t t′ n (eq : eval t ≡ n) s s′ → to-up-right t n eq s ≡ inj₁ (t′ , s′) → convert (One-Up (t′ , s′)) < convert (One-Up (t , s))
  to-u t t′ n eq [] s′ ()
  to-u t t′ n eq (inj₁ .t′ ∷ s) .(inj₂ (t , n , eq) ∷ s) refl = propi t t′ s
  to-u t t′ .(eval t) refl (inj₂ (t₁ , .(eval t₁) , refl) ∷ s) [] x = {!!}
  to-u t t′ .(eval t) refl (inj₂ (t₁ , .(eval t₁) , refl) ∷ s) (inj₁ x₁ ∷ s′) x = {!!}
  to-u t t′ .(eval t) refl (inj₂ (t₁ , .(eval t₁) , refl) ∷ s) (inj₂ (t′′ , n , eq) ∷ s′) x = {!y!}

  inj₁Is : ∀ {A B : Set} → A ⊎ B → Set
  inj₁Is (inj₁ x) = ⊤
  inj₁Is (inj₂ y) = ⊥

  to-left-l : ∀ t t′ s s′ → to-left t s ≡ (t′ , s′) → ∃ λ s′′ → s′ ≡ s′′ ++ s × All inj₁Is s′′
  to-left-l (Tip x₁) .(Tip x₁) s .s refl = [] , refl , []
  to-left-l (Node t t₁) t′ s s′ x with to-left-l t _ (Left t₁ ∷ s) _ x
  to-left-l (Node t t₁) t′ s .(inj₁ t₁ ∷ s) x | .[] , refl , [] = inj₁ t₁ ∷ [] , (refl , tt ∷ [])
  to-left-l (Node t t₁) t′ s .(x ∷ inj₁ t₁ ∷ s) eq | .(x ∷ []) , refl , _∷_ {x} {.[]} px [] = {!!} , ({!!} , {!!})

  -- if we are in a node and we go all the way down to the left then
  -- we will be in a smaller position than the parent of the node we started in.
  --   B
  --  / \
  -- A  X
  --   / \
  --  C  D
  --
  -- C < B
  to-l : ∀ t₁ t₂ t n eq s t′ s′
       → to-left (Node t₁ t₂) (Right t n eq ∷ s) ≡ (t′ , s′)
       → convert (One-Up (t′ , s′)) < convert (One-Up (Node t₁ t₂ , Right t n eq ∷ s ))
  to-l (Tip x₁) t₂ t n eq s .(Tip x₁) .(inj₁ t₂ ∷ inj₂ (t , n , eq) ∷ s) refl
    rewrite ++-RI (reverse s) | reverse-++ ((inj₂ (t , n , eq) ∷ s)) (inj₁ t₂) | reverse-++ (s) (inj₂ (t , n , eq))
    | ++-assoc (reverse s) (inj₂ (t , n , eq) ∷ []) (inj₁ t₂ ∷ [])
    = prepend <-Right-Base (reverse s)
  to-l (Node t₁ t₃) t₂ t n eq s t′ s′ x with to-left-l t₁ _ _ _ x
  to-l (Node t₁ t₃) t₂ t n eq s t′ .(ss ++ inj₁ t₃ ∷ inj₁ t₂ ∷ inj₂ (t , n , eq) ∷ s) x | ss , refl , p = {!!}

  -- We use the ZipperP property to rule out bogus Zippers
  to-right-< : ∀ (z z′ : Zipper)
             → ZipperP z          -- is z valid?
             → right z ≡ inj₁ z′
             → convert (One-Up z′) < convert (One-Up z)
  to-right-< (Tip x , []) z′ zP ()
  to-right-< (Tip x , Left t ∷ s) .(t , Right (Tip x) x refl ∷ s) tt refl = propi (Tip x) t s
  to-right-< (Tip x , Right t n eq ∷ s) (t′ , s′) tt rP                   = to-u (Tip x) t′ x refl (inj₂ (t , n , eq) ∷ s) s′ rP
  to-right-< (Node t₁ t₂ , Right t n eq ∷ s) (t′ , s′) tt rP              = to-l t₁ t₂ t n eq s t′ s′ (⊎-injective₁ rP)

  -- the bogus cases we don′t wanna deal with
  to-right-< (Node t₁ t₂ , []) z′ () rP
  to-right-< (Node t₁ t₂ , Left x ∷ s) z′ () rP

  foldAll : (z : Zipper) → ZipperP z → ℕ
  foldAll (t , s) zP = aux (t , s) zP (<-WF (t ⊳ s) (convert (One-Up (t , s))))
    where aux : ∀ (z : Zipper) → ZipperP z → Acc ([[ plug-⊳ z ]]_<_) (convert (One-Up z)) → ℕ
          aux z zP (acc rs) with right z | inspect right z
          aux z zP (acc rs) | inj₁ z′ | [ eq ] with right-preserves-⊳' z z′ eq
          ... | pr rewrite pr | lemma z | sym (lemma z′) = aux z′ (ZipperP-right z z′ eq zP) (rs (convert (One-Up z′))
                                             (lt (convert (One-Up z′))
                                             (convert (One-Up z))
                                             (trans (lemma z′) (sym (⊳-to-⊲ z′)))
                                             (trans (lemma z)
                                             (trans (sym (⊳-to-⊲ z)) (right-preserves-⊳' z z′ eq))) (to-right-< z z′ zP eq)))
          aux z zP (acc rs) | inj₂ y  | eq = y

  fold-Tree : Tree → ℕ
  fold-Tree t with to-left t [] | inspect (to-left t) []
  ... | z | [ eq ] = foldAll z (ZipperP-to-left t [] (proj₁ z) (proj₂ z) eq)

  t = Node (Tip 1)
  -- good luck with that!
  correctness : ∀ t → eval t ≡ fold-Tree t
  correctness (Tip x) = {!!}
  correctness (Node t t₁) = {!!}
