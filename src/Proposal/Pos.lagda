\begin{code}
module Proposal.Pos where

  open import Induction.WellFounded
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality
  open import Data.List
  open import Data.Product
  open import Data.Bool
  open import Function
  open import Data.Sum
  open import Data.Empty

  data Tree : Set where
    Tip  : Tree
    Node : (t₁ t₂ : Tree) → Tree

  data Stack : Set where
    Left  : ∀ (t : Tree) → Stack → Stack
    Right : ∀ (t : Tree) → Stack → Stack
    Top   : Stack

  -- [_,_]ₛ   : Bool → Tree → Stack
  -- [ false , t ]ₛ = Left t Top
  -- [ true  , t ]ₛ = Right t Top

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

  -- lem : ∀ t t₁ s → t ⊳ (s ++ₛ Left t₁ Top) ≡ Node (t ⊳ s) t₁
  -- lem t t₁ (Left t₂ s)  = lem (Node t t₂) t₁ s
  -- lem t t₁ (Right t₂ s) = lem (Node t₂ t) t₁ s
  -- lem t t₁ Top = refl

  -- lem' : ∀ t t₁ s → t ⊳ (s ++ₛ Right t₁ Top) ≡ Node t₁ (t ⊳ s)
  -- lem' t t₁ (Left t₂ s)  = lem' (Node t t₂) t₁ s
  -- lem' t t₁ (Right t₂ s) = lem' (Node t₂ t) t₁ s
  -- lem' t t₁ Top          = refl

  -- lemma₁ : ∀ t s → t ⊲ s ≡ t ⊳ (revₛ s)
  -- lemma₁ t (Left t₁ s)  with lem t t₁ (revₛ s) | lemma₁ t s
  -- ... | z | q =  trans (cong (λ x → Node x t₁) q) (sym z)
  -- lemma₁ t (Right t₁ s) with lem' t t₁ (revₛ s) | lemma₁ t s
  -- ... | z | q = trans (cong (λ x → Node t₁ x) q) (sym z)
  -- lemma₁ t Top          = refl

  -- ll : ∀ t t₁ s → Node t t₁ ⊲ s ≡ t ⊲ (s ++ₛ Left t₁ Top )
  -- ll t t₁ (Left t₂ s)  = cong (λ x → Node x t₂) (ll t t₁ s)
  -- ll t t₁ (Right t₂ s) = cong (λ x → Node t₂ x) (ll t t₁ s)
  -- ll t t₁ Top = refl

  -- ll' : ∀ t t₁ s → Node t₁ t ⊲ s ≡ t ⊲ (s ++ₛ Right t₁ Top )
  -- ll' t t₁ (Left t₂ s)  = cong (λ x → Node x t₂) (ll' t t₁ s)
  -- ll' t t₁ (Right t₂ s) = cong (λ x → Node t₂ x) (ll' t t₁ s)
  -- ll' t t₁ Top = refl

  -- lemma₂ : ∀ t s → t ⊳ s ≡ t ⊲ (revₛ s)
  -- lemma₂ t (Left t₁ s)  = trans (lemma₂ (Node t t₁) s) (ll t t₁ (revₛ s))
  -- lemma₂ t (Right t₁ s) = trans (lemma₂ (Node t₁ t) s) (ll' t t₁ (revₛ s))
  -- lemma₂ t Top          = refl

  plug-⊳ : Tree × Stack → Tree
  plug-⊳ (t , s) = t ⊳ s

  plug-⊲ : Tree × Stack → Tree
  plug-⊲ (t , s) = t ⊲ s

  -- to-left : Tree → Stack → Tree × Stack
  -- to-left Tip  s          = Tip , s
  -- to-left (Node t₁ t₂)  s = to-left t₁ (Left t₂ s)

  -- to-left-preserves : ∀ t s t′ s′ → to-left t s ≡ (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  -- to-left-preserves Tip s .Tip .s refl    = refl
  -- to-left-preserves (Node t t₁) s t′ s′ x = to-left-preserves t (Left t₁ s) t′ s′ x

  -- to-up-right : Tree → Stack → Maybe (Tree × Stack)
  -- to-up-right t (Left t₁ s)  = just ((Node t t₁) , s)
  -- to-up-right t (Right t₁ s) = to-up-right (Node t₁ t ) s
  -- to-up-right t Top          = nothing

  -- to-up-right-preserves : ∀ t s t′ s′ → to-up-right t s ≡ just (t′ , s′)  → t ⊳ s ≡ t′ ⊳ s′
  -- to-up-right-preserves t (Left t₁ s) .(Node t t₁) .s refl = refl
  -- to-up-right-preserves t (Right t₁ s) t′ s′ x = to-up-right-preserves (Node t₁ t) s t′ s′ x
  -- to-up-right-preserves t Top t′ s′ ()

  -- t : Tree
  -- t = Tip

  -- s : Stack
  -- s = Left Tip (Right Tip (Left Tip Top))

  -- r : Tree × Stack → Maybe (Tree × Stack)
  -- r (t , Left t₁ s)          = just (Node t t₁  , s)
  -- r (Tip , Right t₁ s)       = to-up-right Tip (Right t₁ s)
  -- r (Node t₁ t₂ , Right t s) = just (t₂ , Right t₁ (Right t s))
  -- r (Tip , Top)        = nothing
  -- r (Node t₁ t₂ , Top) = just (to-left t₂ (Right t₁ Top))

  -- to-other : Tree × Stack → Tree × Stack
  -- to-other (t , s ) = ( t , revₛ s)

  -- just-injective : ∀ {a} {A : Set a} {a b} → (Maybe A ∋ just a) ≡ just b → a ≡ b
  -- just-injective refl = refl

  -- r-preserves : ∀ (t×s : Tree × Stack) (t×s′ : Tree × Stack) → r t×s ≡ just t×s′ → plug-⊳ t×s ≡ plug-⊳ t×s′
  -- r-preserves (Tip , Left t₁ s₁) .(Node Tip t₁ , s₁) refl = refl
  -- r-preserves (Tip , Right t₁ s₁) (t , s) x = to-up-right-preserves Tip (Right t₁ s₁) t s x
  -- r-preserves (Tip , Top) t×s′ ()
  -- r-preserves (Node t₁ t₂ , Left t₃ s₁) .(Node (Node t₁ t₂) t₃ , s₁) refl     = refl
  -- r-preserves (Node t₁ t₂ , Right t s₁) (.t₂ , .(Right t₁ (Right t s₁))) refl = refl
  -- r-preserves (Node t₁ t₂ , Top) (t , s) r      = to-left-preserves t₂ (Right t₁ Top) t s (just-injective r)

  -- eq-pos : ∀ {t₁ t₂} → t₂ ≡ t₁ → Pos t₁ → Pos t₂
  -- eq-pos {t₁} {.t₁} refl x₁ = x₁

  data _<_ : Tree × Stack → Tree × Stack → Set where
    <-Right-Step : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) < (t₂ , s₂) → (t₁ , Right t s₁) <  (t₂ , Right t s₂)

    <-Left-Step  : ∀ {t t₁ t₂ s₁ s₂} →  (t₁ , s₁) < (t₂ , s₂) → (t₁ , Left t s₁) < (t₂ , Left t s₂)

    <-Right-Left : ∀ {t₁ t₂ s₁ s₂}   → (t₁ , Right (t₂ ⊲ s₂) s₁) < (t₂ , Left (t₁ ⊲ s₁) s₂)

    <-Right-Base : ∀ {t t₁ s₁}       → (t , Right t₁ s₁)         < (Node t₁ (t ⊲ s₁) , Top)

    <-Left-Base  : ∀ {t t₁ s₁}       → (Node (t ⊲ s₁) t₁ , Top)  < (t , Left t₁ s₁)

  related : ∀ t₁ s₁ t₂ s₂ →  (t₁ , s₁) < (t₂ , s₂) → (t₁ ⊲ s₁ ) ≡ (t₂ ⊲ s₂)
  related t₁ Top t₂ Top ()
  related .(Node (t₂ ⊲ s₂) x₁) Top t₂ (Left x₁ s₂) <-Left-Base = refl
  related t₁ Top t₂ (Right x₁ s₂) ()
  related t₁ (Left x₁ s₁) t₂ Top ()
  related t₁ (Left x₁ s₁) t₂ (Left .x₁ s₂) (<-Left-Step x) = cong (λ x → Node x x₁) (related t₁ s₁ t₂ s₂ x)
  related t₁ (Left x₁ s₁) t₂ (Right x₂ s₂) ()
  related t₁ (Right x₁ s₁) .(Node x₁ (t₁ ⊲ s₁)) Top <-Right-Base = refl
  related t₁ (Right .(t₂ ⊲ s₂) s₁) t₂ (Left .(t₁ ⊲ s₁) s₂) <-Right-Left = refl
  related t₁ (Right x₁ s₁) t₂ (Right .x₁ s₂) (<-Right-Step p) = cong (λ x → Node x₁ x) (related t₁ s₁ t₂ s₂ p)

  data [_]ₛ_<_ (t : Tree) : Tree × Stack → Tree × Stack → Set where
     lt :  ∀ t×s t×s′ → (eq₁ : plug-⊲ t×s ≡ t) → (eq₂ : plug-⊲ t×s′ ≡ t) → (p : t×s < t×s′) → [ t ]ₛ t×s < t×s′

  Node-Inj : ∀ {x y a b} → Node x a ≡ Node y b → x ≡ y × a ≡ b
  Node-Inj {x} .{x} {a} .{a} refl = refl , refl

  mutual
    accR : ∀ t t₁ x → Acc ([ t ]ₛ_<_) x → WfRec ([ Node t₁ t ]ₛ_<_ ) (Acc ([_]ₛ_<_ (Node t₁ t))) (proj₁ x , Right t₁ (proj₂ x))
    accR t t₁ (x , s) (acc rs) .(t₂ , Right t₁ s₂) (lt .(t₂ , Right t₁ s₂) .(x , Right t₁ s) eq₁ eq₂ (<-Right-Step {t₁ = t₂} {s₁ = s₂} p))
      = acc (accR t t₁ (t₂ , s₂) (rs (t₂ , s₂) (lt (t₂ , s₂) (x , s) (proj₂ (Node-Inj eq₁)) (proj₂ (Node-Inj eq₂)) p)))

    accL : ∀ t t₁ x →  Acc ([ t ]ₛ_<_) x → WfRec ([ Node t t₁ ]ₛ_<_ ) (Acc ([ Node t t₁  ]ₛ_<_ )) (proj₁ x , Left t₁ (proj₂ x))
    accL t .t₂ (x , s) (acc rs) (y , Left t₂ s′) (lt .(y , Left t₂ s′) .(x , Left t₂ s) eq₁ eq₂ (<-Left-Step p))
      = acc (accL t t₂ (y , s′) (rs (y , s′) (lt (y , s′) (x , s) (proj₁ (Node-Inj eq₁)) (proj₁ (Node-Inj eq₂)) p)))
    accL .(x ⊲ s) .(y ⊲ s′) (x , s) (acc rs) (y , Right .(x ⊲ s) s′) (lt .(y , Right (x ⊲ s) s′) .(x , Left (y ⊲ s′) s) refl eq₂ <-Right-Left)
      = acc (accR (y ⊲ s′) (x ⊲ s) (y , s′) (<-WF (y ⊲ s′) (y , s′)))
    accL .(x ⊲ s) t₁ (x , s) (acc rs) (.(Node (x ⊲ s) t₁) , Top) (lt .(Node (x ⊲ s) t₁ , Top) .(x , Left t₁ s) eq₁ refl <-Left-Base)
      = acc (accH (x ⊲ s) t₁)

    accH : ∀ t₁ t₂ → WfRec ([ Node t₁ t₂ ]ₛ_<_) (Acc ([ Node t₁ t₂ ]ₛ_<_ )) (Node t₁ t₂ , Top)
    accH t₁ t₂ (y , Left t s) (lt .(y , Left t s) .(Node t₁ t₂ , Top) eq₁ eq₂ ())
    accH t₁ t₂ (y , Top) (lt .(y , Top) .(Node t₁ t₂ , Top) eq₁ eq₂ ())
    accH .t .(y ⊲ s) (y , Right t s) (lt .(y , Right t s) .(Node t (y ⊲ s) , Top) refl eq₂ <-Right-Base)
      = acc (accR (y ⊲ s) t (y , s) (<-WF (y ⊲ s) (y , s)))

    <-WF : ∀ t → Well-founded ([ t ]ₛ_<_)
    <-WF t x = acc (aux t x)
      where aux : ∀ t x → WfRec ([ t ]ₛ_<_) (Acc ([ t ]ₛ_<_)) x
            aux .(Node (y ⊲ s′) t₂) (x , Left .t₂ s) (y , Left t₂ s′) (lt .(y , Left t₂ s′) .(x , Left t₂ s) refl eq₂ (<-Left-Step p))
              = acc (accL (y ⊲ s′) t₂ (y , s′) (<-WF (y ⊲ s′) (y , s′)))
            aux .(Node (x ⊲ s) (y ⊲ s′)) (x , Left .(y ⊲ s′) s) (y , Right .(x ⊲ s) s′) (lt .(y , Right (x ⊲ s) s′) .(x , Left (y ⊲ s′) s) refl eq₂ <-Right-Left)
              = acc (accR (y ⊲ s′) (x ⊲ s) (y , s′) (<-WF (y ⊲ s′) (y , s′)))
            aux .(Node (x ⊲ s) t₁) (x , Left t₁ s) (.(Node (x ⊲ s) t₁) , Top) (lt .(Node (x ⊲ s) t₁ , Top) .(x , Left t₁ s) refl eq₂ <-Left-Base)
              = acc (accH (x ⊲ s) t₁)
            aux .(Node t₂ (y ⊲ s′)) (x , Right .t₂ s) (y , Right t₂ s′) (lt .(y , Right t₂ s′) .(x , Right t₂ s) refl eq₂ (<-Right-Step p))
              = acc (accR (y ⊲ s′) t₂ (y , s′) (<-WF (y ⊲ s′) (y , s′)))
            aux t (x , Top) (y , Left t₁ s′) (lt .(y , Left t₁ s′) .(x , Top) eq₁ eq₂ ())
            aux .(Node t₁ (y ⊲ s′)) (.(Node t₁ (y ⊲ s′)) , Top) (y , Right t₁ s′) (lt .(y , Right t₁ s′) .(Node t₁ (y ⊲ s′) , Top) eq₁ refl <-Right-Base)
              = acc (accR (y ⊲ s′) t₁ (y , s′) (<-WF (y ⊲ s′) (y , s′)))
            aux t (x , Top) (y , Top) (lt .(y , Top) .(x , Top) eq₁ eq₂ ())


  -- leftmosty : Tree → Tree × Stack
  -- leftmosty Tip          = Tip , Top
  -- leftmosty (Node t₁ t₂) with leftmosty t₁
  -- leftmosty (Node t₁ t₂) | t , s = t , Left t₂ s

  -- leftmosty-preserves : ∀ t t′ s′  → leftmosty t ≡ (t′ , s′) → t′ ⊲ s′ ≡ t
  -- leftmosty-preserves Tip .Tip .Top refl  = refl
  -- leftmosty-preserves (Node t₁ t₂) t′ s′ x with leftmosty t₁ | inspect leftmosty t₁
  -- leftmosty-preserves (Node t₁ t₂) .t .(Left t₂ s) refl | t , s | Reveal_·_is_.[ eq ]
  --   = cong (λ x → Node x t₂) (leftmosty-preserves _ _ _ eq)

  -- r-td : Tree × Stack → Maybe (Tree × Stack)
  -- r-td (t , Left  t₁ s) with r-td (t , s)
  -- r-td (t , Left t₁ s) | just (t′ , s′) = just (t′ , Left t₁ s′)
  -- r-td (t , Left t₁ s) | nothing = just (Node t t₁ , Top)
  -- r-td (t , Right t₁ s) with r-td (t , s)
  -- r-td (t , Right t₁ s) | just (t′ , s′)  = just (t′ , Right t₁ s′)
  -- r-td (t , Right t₁ s) | nothing = nothing
  -- r-td (Tip , Top)        = nothing
  -- r-td (Node t₁ t₂ , Top) with leftmosty t₂
  -- ... | (t , s) = just (t , Right t₁ s)

  -- r-td-nothing : ∀ t s → r-td (t , s) ≡ nothing → (t ≡ Tip × s ≡ Top) ⊎ (∃ λ { ( t₁ , s′ ) → s ≡ Right t₁ s′ × r-td (t , s′) ≡ nothing})
  -- r-td-nothing t (Left t₁ s) eq   with r-td (t , s) | inspect r-td (t , s)
  -- r-td-nothing t (Left t₁ s) () | just x  | e
  -- r-td-nothing t (Left t₁ s) () | nothing | e
  -- r-td-nothing t (Right t₁ s) eq with r-td (t , s) | inspect r-td (t , s)
  -- r-td-nothing t (Right t₁ s) () | just x  | e
  -- r-td-nothing t (Right t₁ s) eq | nothing | Reveal_·_is_.[ eq₁ ] = inj₂ ((t₁ , s) , refl , eq₁)
  -- r-td-nothing Tip Top refl      = inj₁ (refl , refl)
  -- r-td-nothing (Node t t₁) Top ()

  -- change-rep : Tree × Stack → Tree × Stack
  -- change-rep (t , s) = t , (revₛ s)

  -- r-td-nothing' : ∀ t s → r-td (t , s) ≡ nothing → (s ≡ Top)
  -- r-td-nothing' t (Left t₁ s) x  with r-td (t , s) | inspect r-td (t , s)
  -- r-td-nothing' t (Left t₁ s) () | just (a , b) | e
  -- r-td-nothing' t (Left t₁ s) () | nothing | e
  -- r-td-nothing' t (Right t₁ s) x with r-td (t , s) | inspect r-td (t , s)
  -- r-td-nothing' t (Right t₁ s) () | just x₁ | e
  -- r-td-nothing' t (Right t₁ s) refl | nothing | Reveal_·_is_.[ eq ] = {!!}
  -- r-td-nothing' t Top x = {!!}

  -- r-td-not' : ∀ t s → r-td (t , s) ≡ nothing → ∀ t₁ → r-td (t , Right t₁ s) ≡ nothing
  -- r-td-not' t (Left t₂ s) eq t₁  with r-td (t , s) | inspect r-td (t , s)
  -- r-td-not' t (Left t₂ s) () t₁ | just x | e
  -- r-td-not' t (Left t₂ s) () t₁ | nothing | e
  -- r-td-not' t (Right t₂ s) eq t₁ with r-td (t , s) | inspect r-td (t , s)
  -- r-td-not' t (Right t₂ s) () t₁ | just x | e
  -- r-td-not' t (Right t₂ s) eq t₁ | nothing | e = refl
  -- r-td-not' Tip Top eq t₁ = refl
  -- r-td-not' (Node t t₂) Top eq t₁ with leftmosty t₂ | inspect leftmosty t₂
  -- r-td-not' (Node t t₂) Top () t₁ | z | e

  -- open Deprecated-inspect renaming (inspect to inspect′)


  -- mutual
  --   impl : ∀ t s → (t ⊲ s) ≡ t → (s ≡ Top)
  --   impl Tip (Left t₁ s) ()
  --   impl (Node t₁ t₂) (Left t s) x = {!!}
  --   impl t (Right t₁ s) x = {!!}
  --   impl t Top x = refl

  --   implu : ∀ t t₂ s → (Node t t₂ ⊲ s) ≡ t → ⊥ 
  --   implu Tip t₂ (Left t s) ()
  --   implu (Node t₁ t₃) t₂ (Left t s) x = {!!}
  --   implu t₁ t₂ (Right t s) x with (Node t₁ t₂ ⊲ s)
  --   ... | z = {!!}
  --   implu t₁ t₂ Top ()

  --   implo : ∀ t s → (s ≡ Top) → (t ⊲ s) ≡ t
  --   implo t .Top refl = refl

  -- r-td' : ∀ t s → r-td (t , s) ≡ nothing → t ≡ (t ⊲ s)
  -- r-td' t (Left t₁ s) x  with r-td (t , s) | inspect r-td (t , s)
  -- r-td' t (Left t₁ s) () | just x₁ | e
  -- r-td' t (Left t₁ s) () | nothing | e
  -- r-td' t (Right t₁ s) eq with r-td (t , s) | inspect r-td (t , s)
  -- r-td' t (Right t₁ s) () | just x | e
  -- r-td' t (Right t₁ s) refl | nothing | Reveal_·_is_.[ eq₁ ] with r-td' t s eq₁
  -- ... | z = {!!}
  -- r-td' t Top x = {!!}

  -- r-td-preserves' : ∀ (t : Tree) (t×s : Tree × Stack) (t×s′ : Tree × Stack) → plug-⊲ t×s ≡ t → r-td t×s ≡ just t×s′ → plug-⊲ t×s′ ≡ t
  -- r-td-preserves' tt (t , Left t₁ s) (t′ , s′) peq rd with r-td (t , s) | inspect r-td (t , s)
  -- r-td-preserves' Tip (t , Left t₁ s) (.x , .(Left t₁ y)) () refl | just (x , y) | Reveal_·_is_.[ eq ]
  -- r-td-preserves' (Node .(t ⊲ s) .t₁) (t , Left t₁ s) (.x , .(Left t₁ y)) refl refl | just (x , y) | Reveal_·_is_.[ eq ] = {!!}
  -- r-td-preserves' .(Node (t ⊲ s) t₁) (t , Left t₁ s) (.(Node t t₁) , .Top) refl refl | nothing | Reveal_·_is_.[ eq ]  =  {!!} -- (r-td' t s eq)
  -- r-td-preserves' tt (t , Right t₁ s) (t′ , s′) peq rd with r-td (t , s) | inspect r-td (t , s)
  -- r-td-preserves' tt (t , Right t₁ s) (.a , .(Right t₁ b)) peq refl | just (a , b) | Reveal_·_is_.[ eq ] = {!!}
  -- r-td-preserves' tt (t , Right t₁ s) (t′ , s′) peq rd | nothing | e = {!!}
  -- r-td-preserves' tt (t , Top) (t′ , s′) peq rd = {!!}

  -- theo : ∀ txs txs′ → (eq : r-td txs ≡ just txs′) → txs′ <S txs
  -- theo (t , Left t₁ s₁)  (t′ , s′) eq with r-td (t , s₁) | inspect r-td (t , s₁)
  -- theo (t , Left t₁ s₁) (.t′ , .(Left t₁ s′)) refl | just (t′ , s′) | Reveal_·_is_.[ eq ] = <S-Left-Step (theo (t , s₁) (t′ , s′) eq)
  -- theo (t , Left t₁ s₁) (.(Node t t₁) , .Top) refl | nothing | Reveal_·_is_.[ eq ] with r-td-nothing t s₁ eq
  -- theo (t , Left t₁ .Top) (.(Node t t₁) , .Top) refl | nothing | Reveal_·_is_.[ eq ] | inj₁ (a , refl) = <S-Left-Base
  -- theo (t , Left t₁ .(Right y ys)) (.(Node t t₁) , .Top) refl | nothing | Reveal_·_is_.[ eq ] | inj₂ ((y , ys) , refl , ps)  = {!!}
  -- theo (t , Right t₁ s₁) (t′ , s′) eq with r-td (t , s₁) | inspect r-td (t , s₁)
  -- theo (t , Right t₁ s₁) (.t′ , .(Right t₁ s′)) refl | just (t′ , s′) | Reveal_·_is_.[ eq ] = <S-Right-Step (theo (t , s₁) (t′ , s′) eq)
  -- theo (t , Right t₁ s₁) (t′ , s′) () | nothing | e
  -- theo (Tip , Top) (t′ , s′) ()
  -- theo (Node t₁ t₂ , Top) (t′ , s′) eq with leftmosty t₂ | inspect leftmosty t₂
  -- theo (Node t₁ t₂ , Top) (.t′ , .(Right t₁ s′)) refl | t′ , s′ | [ eq ] with leftmosty-preserves t₂ _ _ eq
  -- theo (Node t₁ .(t′ ⊲ s′) , Top) (.t′ , .(Right t₁ s′)) refl | t′ , s′ | Reveal_·_is_.[ eq ] | refl = <S-Right-Base

\end{code}
