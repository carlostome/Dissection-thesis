\begin{code}
module Proposal.Pos where

  open import Induction.WellFounded
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Data.List
  open import Data.Product
  open import Data.Bool
  open import Function

  data Tree : Set where
    Tip  : Tree
    Node : (t₁ t₂ : Tree) → Tree

  data Pos : Tree → Set where
    here  : ∀ {t}     → Pos t
    left  : ∀ {t₁ t₂} → Pos t₁ → Pos (Node t₁ t₂)
    right : ∀ {t₁ t₂} → Pos t₂ → Pos (Node t₁ t₂)

  toPos : (t : Tree) → List Bool → Maybe (Pos t)
  toPos Tip []         = just here
  toPos Tip (_ ∷ _)    = nothing
  toPos (Node t₁ t₂) []       = just here
  toPos (Node t₁ t₂) (false ∷ xs) with toPos t₁ xs
  toPos (Node t₁ t₂) (false ∷ xs) | just x  = just (left x)
  toPos (Node t₁ t₂) (false ∷ xs) | nothing = nothing
  toPos (Node t₁ t₂) (true  ∷ xs) with toPos t₂ xs
  toPos (Node t₁ t₂) (true ∷ xs) | just x  = just (right x)
  toPos (Node t₁ t₂) (true ∷ xs) | nothing = nothing

  fromPos : ∀ t → Pos t → List Bool
  fromPos Tip here = []
  fromPos (Node t₁ t₂) here      = []
  fromPos (Node t₁ t₂) (left x)  = false ∷ fromPos t₁ x
  fromPos (Node t₁ t₂) (right x) = true  ∷ fromPos t₂ x

  data [_]_<_ : (t : Tree) → Pos t → Pos t → Set where
    left-base  : ∀ {t₁ t₂} {p} → [ Node t₁ t₂ ] here    < left p
    right-base : ∀ {t₁ t₂} {p} → [ Node t₁ t₂ ] right p < here

    left-step  : ∀ {t₁ t₂} {p₁ p₂} → [ t₁ ] p₁ < p₂ → [ Node t₁ t₂ ] left p₁  < left p₂
    right-step : ∀ {t₁ t₂} {p₁ p₂} → [ t₂ ] p₁ < p₂ → [ Node t₁ t₂ ] right p₁ < right p₂

    left-right : ∀ {t₁ t₂} {p₁ p₂} → [ Node t₁ t₂ ] right p₁ < left p₂

  mutual
    rAcc : ∀ t₁ t₂ x →  Acc ([ t₂ ]_<_) x → WfRec ([_]_<_ (Node t₁ t₂)) (Acc ([_]_<_ (Node t₁ t₂))) (right x)
    rAcc t₁ t₂ x (acc rs) here ()
    rAcc t₁ t₂ x (acc rs) (left y) ()
    rAcc t₁ t₂ x (acc rs) (right y) (right-step p) = acc (rAcc t₁ t₂ y (rs y p))

    lAcc : ∀ t₁ t₂ x →  Acc ([ t₁ ]_<_) x → WfRec ([_]_<_ (Node t₁ t₂)) (Acc ([_]_<_ (Node t₁ t₂))) (left x)
    lAcc t₁ t₂ x (acc rs) here left-base         = acc (hAcc t₁ t₂)
    lAcc t₁ t₂ x (acc rs) (left y) (left-step p) = acc (lAcc t₁ t₂ y (rs y p))
    lAcc t₁ t₂ x (acc rs) (right y) left-right   = acc (rAcc t₁ t₂ y (<-WF t₂ y))

    hAcc : ∀ t₁ t₂ → WfRec ([_]_<_ (Node t₁ t₂)) (Acc ([_]_<_ (Node t₁ t₂))) here
    hAcc t₁ t₂ here ()
    hAcc t₁ t₂ (left y) ()
    hAcc t₁ t₂ (right y) right-base = acc (rAcc t₁ t₂ y (<-WF t₂ y))

    <-WF : ∀ t → Well-founded ([ t ]_<_)
    <-WF t x = acc (aux t x)
      where aux : ∀ t x → WfRec ([_]_<_ t) (Acc ([_]_<_ t)) x
            aux Tip here y ()
            aux (Node t₁ t₂) here .(right _) right-base      = acc (rAcc t₁ t₂ _ (<-WF t₂ _))
            aux (Node t₁ t₂) (left x) here left-base         = acc (hAcc t₁ t₂)
            aux (Node t₁ t₂) (left x) (left y) (left-step p) = acc (lAcc t₁ t₂ y (<-WF t₁ y))
            aux (Node t₁ t₂) (left x) (right y) left-right   = acc (rAcc t₁ t₂ y (<-WF t₂ y))
            aux (Node t₁ t₂) (right x) .(right _) (right-step p) = acc (rAcc t₁ t₂ _ (<-WF t₂ _))

  leftmost : ∀ t → Pos t
  leftmost Tip          = here
  leftmost (Node t₁ t₂) = left (leftmost t₁)

  next : ∀ {t} → Pos t → Maybe (Pos t)
  next {Tip} here               = nothing
  next {(Node t₁ t₂)} here      = just (right (leftmost t₂))
  next {(Node t₁ t₂)} (left x)  with next x
  next {(Node t₁ t₂)} (left x) | just p   = just (left p)
  next {(Node t₁ t₂)} (left x) | nothing  = just here
  next {(Node t₁ t₂)} (right x) with next x
  next {(Node t₁ t₂)} (right x) | just p  = just (right p)
  next {(Node t₁ t₂)} (right x) | nothing = nothing

  theorem : ∀ t p x → next p ≡ just x → [ t ] x < p
  theorem Tip here here ()
  theorem (Node t₁ t₂) here .(right (leftmost t₂)) refl = right-base
  theorem (Node t₁ t₂) (left p) x eq  with next p | inspect next p
  theorem (Node t₁ t₂) (left p) .(left x) refl | just x | [ eq₁ ]  = left-step (theorem t₁ p x eq₁)
  theorem (Node t₁ t₂) (left p) .here refl | nothing | [ eq₁ ]     = left-base
  theorem (Node t₁ t₂) (right p) x eq with next p | inspect next p
  theorem (Node t₁ t₂) (right p) .(right x) refl | just x | [ eq₁ ] = right-step (theorem t₂ p x eq₁)
  theorem (Node t₁ t₂) (right p) x () | nothing | [ eq₁ ]

  p : Pos (Node (Node Tip Tip) (Node (Node Tip Tip) Tip))
  p = left (left here)

  list : ∀ {t} → Pos t → List (Pos t)
  list {t} p = aux p (<-WF t p)
    where
      aux : (p : Pos t) → Acc [ t ]_<_ p → List (Pos t)
      aux p (acc rs) with next p | inspect next p
      aux p (acc rs) | just x  | [ eq ] = p ∷ aux x (rs x (theorem t p x eq))
      aux p (acc rs) | nothing | _      = p ∷ []

  data Stack : Set where
    Left  : ∀ (t : Tree) → Stack → Stack
    Right : ∀ (t : Tree) → Stack → Stack
    Top   : Stack

  [_,_]ₛ   : Bool → Tree → Stack
  [ false , t ]ₛ = Left t Top
  [ true  , t ]ₛ = Right t Top

  _++ₛ_ : Stack → Stack → Stack
  Left t x  ++ₛ y = Left  t (x ++ₛ y)
  Right t x ++ₛ y = Right t (x ++ₛ y)
  Top ++ₛ y = y

  revₛ : Stack → Stack
  revₛ (Left t s)  = revₛ s ++ₛ Left t Top
  revₛ (Right t s) = revₛ s ++ₛ Right t Top
  revₛ Top = Top

  data InitLastₛ : Stack → Set where
    Top    : InitLastₛ Top
    Right  : (s : Stack) (t : Tree) → InitLastₛ (s ++ₛ Right t Top)
    Left   : (s : Stack) (t : Tree) → InitLastₛ (s ++ₛ Left  t Top)

  initLastₛ : (s : Stack) → InitLastₛ s
  initLastₛ Top = Top
  initLastₛ (Left t s) with initLastₛ s
  initLastₛ (Left t .Top) | Top = Left Top t
  initLastₛ (Left t .(s ++ₛ Right t₁ Top)) | Right s t₁ = Right (Left t s) t₁
  initLastₛ (Left t .(s ++ₛ Left t₁ Top))  | Left s t₁  = Left  (Left t s) t₁
  initLastₛ (Right t s) with initLastₛ s
  initLastₛ (Right t .Top) | Top = Right Top t
  initLastₛ (Right t .(s ++ₛ Right t₁ Top)) | Right s t₁ = Right (Right t s) t₁
  initLastₛ (Right t .(s ++ₛ Left t₁ Top)) | Left s t₁   = Left (Right t s) t₁

  -- bottom up
  _⊳_ : Tree → Stack → Tree
  t ⊳ Top       = t
  t ⊳ Left x s  = (Node t x) ⊳ s
  t ⊳ Right x s = (Node x t) ⊳ s

  -- top down
  _⊲_  : Tree → Stack → Tree
  t ⊲ Left  t₁ s = Node (t ⊲ s) t₁
  t ⊲ Right t₁ s = Node t₁ (t ⊲ s)
  t ⊲ Top        = t

  lem : ∀ t t₁ s → t ⊳ (s ++ₛ Left t₁ Top) ≡ Node (t ⊳ s) t₁
  lem t t₁ (Left t₂ s)  = lem (Node t t₂) t₁ s
  lem t t₁ (Right t₂ s) = lem (Node t₂ t) t₁ s
  lem t t₁ Top = refl

  lem' : ∀ t t₁ s → t ⊳ (s ++ₛ Right t₁ Top) ≡ Node t₁ (t ⊳ s)
  lem' t t₁ (Left t₂ s)  = lem' (Node t t₂) t₁ s
  lem' t t₁ (Right t₂ s) = lem' (Node t₂ t) t₁ s
  lem' t t₁ Top          = refl

  lemma₁ : ∀ t s → t ⊲ s ≡ t ⊳ (revₛ s)
  lemma₁ t (Left t₁ s)  with lem t t₁ (revₛ s) | lemma₁ t s
  ... | z | q =  trans (cong (λ x → Node x t₁) q) (sym z)
  lemma₁ t (Right t₁ s) with lem' t t₁ (revₛ s) | lemma₁ t s
  ... | z | q = trans (cong (λ x → Node t₁ x) q) (sym z)
  lemma₁ t Top          = refl

  ll : ∀ t t₁ s → Node t t₁ ⊲ s ≡ t ⊲ (s ++ₛ Left t₁ Top )
  ll t t₁ (Left t₂ s)  = cong (λ x → Node x t₂) (ll t t₁ s)
  ll t t₁ (Right t₂ s) = cong (λ x → Node t₂ x) (ll t t₁ s)
  ll t t₁ Top = refl

  ll' : ∀ t t₁ s → Node t₁ t ⊲ s ≡ t ⊲ (s ++ₛ Right t₁ Top )
  ll' t t₁ (Left t₂ s)  = cong (λ x → Node x t₂) (ll' t t₁ s)
  ll' t t₁ (Right t₂ s) = cong (λ x → Node t₂ x) (ll' t t₁ s)
  ll' t t₁ Top = refl

  lemma₂ : ∀ t s → t ⊳ s ≡ t ⊲ (revₛ s)
  lemma₂ t (Left t₁ s)  = trans (lemma₂ (Node t t₁) s) (ll t t₁ (revₛ s))
  lemma₂ t (Right t₁ s) = trans (lemma₂ (Node t₁ t) s) (ll' t t₁ (revₛ s))
  lemma₂ t Top          = refl

  plug-⊳ : Tree × Stack → Tree
  plug-⊳ (t , s) = t ⊳ s

  plug-⊲ : Tree × Stack → Tree
  plug-⊲ (t , s) = t ⊲ s

  makePos : (t×s : Tree × Stack) → Pos (plug-⊲ t×s)
  makePos (t , Left t₁ s)  = left  (makePos (t , s))
  makePos (t , Right t₁ s) = right (makePos (t , s))
  makePos (t , Top)        = here

  makePosR : (t×s : Tree × Stack) → Pos (plug-⊳ t×s)
  makePosR (t , s) with makePos (t , revₛ s)
  ... | p rewrite (sym (lemma₂ t s)) = p

  to-left : Tree → Stack → Tree × Stack
  to-left Tip  s          = Tip , s
  to-left (Node t₁ t₂)  s = to-left t₁ (Left t₂ s)

  to-left-preserves : ∀ t s t′ s′ → to-left t s ≡ (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  to-left-preserves Tip s .Tip .s refl    = refl
  to-left-preserves (Node t t₁) s t′ s′ x = to-left-preserves t (Left t₁ s) t′ s′ x

  to-up-right : Tree → Stack → Maybe (Tree × Stack)
  to-up-right t (Left t₁ s)  = just ((Node t t₁) , s)
  to-up-right t (Right t₁ s) = to-up-right (Node t₁ t ) s
  to-up-right t Top          = nothing

  to-up-right-preserves : ∀ t s t′ s′ → to-up-right t s ≡ just (t′ , s′)  → t ⊳ s ≡ t′ ⊳ s′
  to-up-right-preserves t (Left t₁ s) .(Node t t₁) .s refl = refl
  to-up-right-preserves t (Right t₁ s) t′ s′ x = to-up-right-preserves (Node t₁ t) s t′ s′ x
  to-up-right-preserves t Top t′ s′ ()

  t : Tree
  t = Tip

  s : Stack
  s = Left Tip (Right Tip (Left Tip Top))

  r : Tree × Stack → Maybe (Tree × Stack)
  r (t , Left t₁ s)          = just (Node t t₁  , s)
  r (Tip , Right t₁ s)       = to-up-right Tip (Right t₁ s)
  r (Node t₁ t₂ , Right t s) = just (t₂ , Right t₁ (Right t s))
  r (Tip , Top)        = nothing
  r (Node t₁ t₂ , Top) = just (to-left t₂ (Right t₁ Top))

  to-other : Tree × Stack → Tree × Stack
  to-other (t , s ) = ( t , revₛ s)

  just-injective : ∀ {a} {A : Set a} {a b} → (Maybe A ∋ just a) ≡ just b → a ≡ b
  just-injective refl = refl

  r-preserves : ∀ (t×s : Tree × Stack) (t×s′ : Tree × Stack) → r t×s ≡ just t×s′ → plug-⊳ t×s ≡ plug-⊳ t×s′
  r-preserves (Tip , Left t₁ s₁) .(Node Tip t₁ , s₁) refl = refl
  r-preserves (Tip , Right t₁ s₁) (t , s) x = to-up-right-preserves Tip (Right t₁ s₁) t s x
  r-preserves (Tip , Top) t×s′ ()
  r-preserves (Node t₁ t₂ , Left t₃ s₁) .(Node (Node t₁ t₂) t₃ , s₁) refl     = refl
  r-preserves (Node t₁ t₂ , Right t s₁) (.t₂ , .(Right t₁ (Right t s₁))) refl = refl
  r-preserves (Node t₁ t₂ , Top) (t , s) r      = to-left-preserves t₂ (Right t₁ Top) t s (just-injective r)

  eq-pos : ∀ {t₁ t₂} → t₂ ≡ t₁ → Pos t₁ → Pos t₂
  eq-pos {t₁} {.t₁} refl x₁ = x₁

  data _<S_ : Tree × Stack → Tree × Stack → Set where
    <S-Right-Step : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Right t s₁) <S  (t₂ , Right t s₂)

    <S-Left-Step  : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ , Left t s₁) <S (t₂ , Left t s₂)

    <S-Right-Left : ∀ {t₁ t₂ s₁ s₂}   → (t₁ , Right (t₂ ⊲ s₂) s₁) <S (t₂ , Left (t₁ ⊲ s₁) s₂)

    <S-Right-Base : ∀ {t t₁ s₁}       → (t , Right t₁ s₁) <S (Node t₁ (t ⊲ s₁) , Top)

    <S-Left-Base  : ∀ {t t₁ s₁}       → (Node (t ⊲ s₁) t₁ , Top)    <S (t , Left t₁ s₁)

  related : ∀ t₁ s₁ t₂ s₂ →  (t₁ , s₁) <S (t₂ , s₂) → (t₁ ⊲ s₁ ) ≡ (t₂ ⊲ s₂)
  related t₁ Top t₂ Top ()
  related .(Node (t₂ ⊲ s₂) x₁) Top t₂ (Left x₁ s₂) <S-Left-Base = refl
  related t₁ Top t₂ (Right x₁ s₂) ()
  related t₁ (Left x₁ s₁) t₂ Top ()
  related t₁ (Left x₁ s₁) t₂ (Left .x₁ s₂) (<S-Left-Step x) = cong (λ x → Node x x₁) (related t₁ s₁ t₂ s₂ x)
  related t₁ (Left x₁ s₁) t₂ (Right x₂ s₂) ()
  related t₁ (Right x₁ s₁) .(Node x₁ (t₁ ⊲ s₁)) Top <S-Right-Base = refl
  related t₁ (Right .(t₂ ⊲ s₂) s₁) t₂ (Left .(t₁ ⊲ s₁) s₂) <S-Right-Left = refl
  related t₁ (Right x₁ s₁) t₂ (Right .x₁ s₂) (<S-Right-Step p) = cong (λ x → Node x₁ x) (related t₁ s₁ t₂ s₂ p)

  data [_]ₛ_<_ : Tree → Tree × Stack → Tree × Stack → Set where
     lt :  ∀ t t×s t×s′ → (eq₁ : plug-⊲ t×s ≡ t) → (eq₂ : plug-⊲ t×s′ ≡ t) → (p : t×s <S t×s′) → [ t ]ₛ t×s < t×s′

  plug-⊲-top : ∀ x t → plug-⊲ (x , Top) ≡ t → x ≡ t
  plug-⊲-top x .x refl = refl

  plug-⊲-node-right : ∀ x t t₁ s₁  → plug-⊲ (t₁ , Right t s₁) ≡ Node t x → plug-⊲ (t₁ , s₁) ≡ x
  plug-⊲-node-right .(t₁ ⊲ s₁) t t₁ s₁ refl = refl

  plug-⊲-node-left : ∀ x t t₁ s₁  → plug-⊲ (t₁ , Left t s₁) ≡ Node x t → plug-⊲ (t₁ , s₁) ≡ x
  plug-⊲-node-left .(t₁ ⊲ s₁) t t₁ s₁ refl = refl

  Node-inj-l : ∀ x y t → Node x t ≡ Node y t → x ≡ y
  Node-inj-l x .x t refl = refl

  Node-inj-r : ∀ x y t → Node t x ≡ Node t y → x ≡ y
  Node-inj-r x .x t refl = refl

  other :  ∀ t t₁ s₁ a b → plug-⊲ (t , Right t₁ s₁) ≡ Node a b → (a ≡ t₁ × b ≡ t ⊲ s₁)
  other t t₁ s₁ .t₁ .(t ⊲ s₁) refl = refl , refl

  mutual
    accR : ∀ t x s y → Acc ([ x ⊲ s ]ₛ_<_) y → WfRec ([_]ₛ_<_ (Node t (x ⊲ s))) (Acc ([_]ₛ_<_ (Node t (x ⊲ s)))) (proj₁ y , Right t (proj₂ y))
    accR t x s (y , s₂) (acc rs) .(t₁ , Right t s₁) (lt .(Node t (x ⊲ s)) .(t₁ , Right t s₁) .(y , Right t s₂) eq₁ eq₂ (<S-Right-Step {t₁ = t₁} {s₁ = s₁} p))
      = acc (accR t x s (t₁ , s₁) (rs (t₁ , s₁) (lt (x ⊲ s) (t₁ , s₁) (y , s₂)
            (plug-⊲-node-right (x ⊲ s) t t₁ s₁ eq₁)
            (plug-⊲-node-right (x ⊲ s) t y s₂ eq₂) p)))

    accL : ∀ t x s y →  Acc ([ x ⊲ s ]ₛ_<_) y → WfRec ([_]ₛ_<_ (Node (x ⊲ s) t)) (Acc ([_]ₛ_<_ (Node (x ⊲ s) t))) (proj₁ y , Left t (proj₂ y))
    accL t x s (y , s′) (acc rs) (z , Left .t s₁) (lt .(Node (x ⊲ s) t) .(z , Left t s₁) .(y , Left t s′) eq₁ eq₂ (<S-Left-Step p))
      = acc (accL t x s (z , s₁) (rs (z , s₁) (lt (x ⊲ s) (z , s₁) (y , s′) (plug-⊲-node-left (x ⊲ s) t z s₁ eq₁) (plug-⊲-node-left (x ⊲ s) t y s′ eq₂) p)))
    accL .(z ⊲ s₁) x s (y , s′) (acc rs) (z , Right .(y ⊲ s′) s₁) (lt .(Node (x ⊲ s) (z ⊲ s₁)) .(z , Right (y ⊲ s′) s₁) .(y , Left (z ⊲ s₁) s′) eq₁ eq₂ <S-Right-Left)
      with other z (y ⊲ s′) s₁ (x ⊲ s) (z ⊲ s₁) eq₁
    accL .(z ⊲ s₁) x s (y , s′) (acc rs) (z , Right .(y ⊲ s′) s₁) (lt .(Node (x ⊲ s) (z ⊲ s₁)) .(z , Right (y ⊲ s′) s₁) .(y , Left (z ⊲ s₁) s′) eq₁ eq₂ <S-Right-Left)
      | a , refl rewrite a = acc (accR (y ⊲ s′) z s₁ (z , s₁) (<S-WF (z ⊲ s₁) (z , s₁)))
    accL t x s (y , s′) (acc rs) (.(Node (y ⊲ s′) t) , Top) (lt .(Node (x ⊲ s) t) .(Node (y ⊲ s′) t , Top) .(y , Left t s′) eq₁ eq₂ <S-Left-Base)
      with (Node-inj-l _ _ _ (plug-⊲-top _ _ eq₁))
    ... | z  rewrite z = acc (accH (x ⊲ s) t)

    accH : ∀ t₁ t₂ → WfRec ([_]ₛ_<_ (Node t₁ t₂)) (Acc ([_]ₛ_<_ (Node t₁ t₂))) (Node t₁ t₂ , Top)
    accH t₁ t₂ (y , Left t₃ s₁) (lt .(Node t₁ t₂) .(y , Left t₃ s₁) .(Node t₁ t₂ , Top) eq₁ eq₂ ())
    accH t₁ .(y ⊲ s₁) (y , Right .t₁ s₁) (lt .(Node t₁ (y ⊲ s₁)) .(y , Right t₁ s₁) .(Node t₁ (y ⊲ s₁) , Top) eq₁ refl <S-Right-Base)
      = acc (accR t₁ y s₁ (y , s₁) (<S-WF (y ⊲ s₁) (y , s₁)))
    accH t₁ t₂ (y , Top) (lt .(Node t₁ t₂) .(y , Top) .(Node t₁ t₂ , Top) eq₁ eq₂ ())

    <S-WF : ∀ t → Well-founded ([ t ]ₛ_<_)
    <S-WF t x = acc (aux t x)
      where aux : ∀ t x → WfRec ([_]ₛ_<_ t) (Acc ([_]ₛ_<_ t)) x
            aux .(Node (y ⊲ s₂) t₂) (x , Left .t₂ s₁) (y , Left t₂ s₂) (lt .(Node (y ⊲ s₂) t₂) .(y , Left t₂ s₂) .(x , Left t₂ s₁) refl eq₂ (<S-Left-Step p))
              = acc (accL t₂ y s₂ (y , s₂) (<S-WF (y ⊲ s₂) (y , s₂)))
            aux .(Node (x ⊲ s₁) (y ⊲ s₂)) (x , Left .(y ⊲ s₂) s₁) (y , Right .(x ⊲ s₁) s₂) (lt .(Node (x ⊲ s₁) (y ⊲ s₂)) .(y , Right (x ⊲ s₁) s₂) .(x , Left (y ⊲ s₂) s₁) refl eq₂ <S-Right-Left) = acc (accR (x ⊲ s₁) y s₂ (y , s₂) (<S-WF (y ⊲ s₂) (y , s₂)))
            aux .(Node (x ⊲ s₁) t₁) (x , Left t₁ s₁) (.(Node (x ⊲ s₁) t₁) , Top) (lt .(Node (x ⊲ s₁) t₁) .(Node (x ⊲ s₁) t₁ , Top) .(x , Left t₁ s₁) refl eq₂ <S-Left-Base)
              = acc (accH (x ⊲ s₁) t₁)
            aux t (x , Right t₁ s₁) (y , Left t₂ s₂) (lt .t .(y , Left t₂ s₂) .(x , Right t₁ s₁) eq₁ eq₂ ())
            aux Tip (x , Right .t₂ s₁) (y , Right t₂ s₂) (lt .Tip .(y , Right t₂ s₂) .(x , Right t₂ s₁) () eq₂ (<S-Right-Step p))
            aux (Node .t .(y ⊲ s₂)) (x , Right .t s₁) (y , Right t s₂) (lt .(Node t (y ⊲ s₂)) .(y , Right t s₂) .(x , Right t s₁) refl eq₂ (<S-Right-Step p))
              = acc (accR t y s₂ (y , s₂) (<S-WF (y ⊲ s₂) (y , s₂)))
            aux t (x , Right t₁ s₁) (y , Top) (lt .t .(y , Top) .(x , Right t₁ s₁) eq₁ eq₂ ())
            aux t (x , Top) y (lt .t .y .(x , Top) eq₁ eq₂ p) with plug-⊲-top x t eq₂
            aux t (.t , Top) (y , Left t₁ s₁) (lt .t .(y , Left t₁ s₁) .(t , Top) eq₁ eq₂ ()) | refl
            aux .(Node t₁ (y ⊲ s₁)) (.(Node t₁ (y ⊲ s₁)) , Top) (y , Right t₁ s₁) (lt .(Node t₁ (y ⊲ s₁))
                .(y , Right t₁ s₁) .(Node t₁ (y ⊲ s₁) , Top) refl refl <S-Right-Base) | refl = acc (accR t₁ y s₁ (y , s₁) (<S-WF (y ⊲ s₁) (y , s₁)))
            aux t (.t , Top) (y , Top) (lt .t .(y , Top) .(t , Top) eq₁ eq₂ ()) | refl


  -- leftmost : ∀ t → Pos t
  -- leftmost Tip          = here
  -- leftmost (Node t₁ t₂) = left (leftmost t₁)

  -- next : ∀ {t} → Pos t → Maybe (Pos t)
  -- next {Tip} here               = nothing
  -- next {(Node t₁ t₂)} here      = just (right (leftmost t₂))
  -- next {(Node t₁ t₂)} (left x)  with next x
  -- next {(Node t₁ t₂)} (left x) | just p   = just (left p)
  -- next {(Node t₁ t₂)} (left x) | nothing  = just here
  -- next {(Node t₁ t₂)} (right x) with next x
  -- next {(Node t₁ t₂)} (right x) | just p  = just (right p)
  -- next {(Node t₁ t₂)} (right x) | nothing = nothing

  r-td : Tree → Stack → Maybe (Tree × Stack)
  r-td Tip (Left t₁ s₁)  with r-td Tip s₁
  r-td Tip (Left t₁ s₁) | just x  = just ({!!} , {!!})
  r-td Tip (Left t₁ s₁) | nothing = just (Node Tip t₁ , Top)
  r-td Tip (Right t₁ s₁) = {!!}
  r-td Tip Top = nothing
  r-td (Node t₁ t₂) (Left t₃ s₁)  = {!!}
  r-td (Node t₁ t₂) (Right t₃ s₁) = {!!}
  r-td (Node t₁ t₂) Top = {!!}

  change-rep : Tree × Stack → Tree × Stack
  change-rep (t , s) = t , (revₛ s)

  -- theo : ∀ t s t′ s′ → (eq : r (t , s) ≡ just (t′ , s′)) → (t′ , revₛ s′) <S (t , revₛ s)
  -- theo t s t′ s′ eq with revₛ s= {!!}

\end{code}
