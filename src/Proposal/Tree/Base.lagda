\begin{code}
module Proposal.Tree.Base where

  open import Induction.WellFounded
  open import Data.Maybe
  open import Data.Maybe.Base
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Data.Bool
  open import Function
  open import Data.Sum
  open import Data.Empty

\end{code}
%<*Tree>
\begin{code}
  data Tree : Set where
    Tip   : Tree
    Node  : (t₁ t₂ : Tree) → Tree
\end{code}
%</Tree>

%<*Stack>
\begin{code}
  data Stack : Set where
    Left   : (t : Tree) → Stack → Stack
    Right  : (t : Tree) → Stack → Stack
    Top    : Stack

  Zipper = Tree × Stack
\end{code}
%</Stack>

%<*BUPlug>
\begin{code}
  _⊳_  : Tree → Stack → Tree
  t ⊳ Left   t₁ s  = Node t t₁ ⊳ s
  t ⊳ Right  t₁ s  = Node t₁ t ⊳ s
  t ⊳ Top          = t

  plug-⊳ : Zipper → Tree
  plug-⊳ (t , s) = t ⊳ s
\end{code}
%</BUPlug>


\begin{code}
  _++ₛ_ : Stack → Stack → Stack
  Left t x  ++ₛ y  = Left  t (x ++ₛ y)
  Right t x ++ₛ y  = Right t (x ++ₛ y)
  Top ++ₛ y        = y

  revₛ : Stack → Stack
  revₛ (Left t s)   = revₛ s ++ₛ Left   t Top
  revₛ (Right t s)  = revₛ s ++ₛ Right  t Top
  revₛ Top = Top

  data InitLastₛ : Stack → Set where
    Top    : InitLastₛ Top
    Right  : (s : Stack) (t : Tree) → InitLastₛ s → InitLastₛ (s ++ₛ Right t Top)
    Left   : (s : Stack) (t : Tree) → InitLastₛ s → InitLastₛ (s ++ₛ Left  t Top)

  initLastₛ : (s : Stack) → InitLastₛ s
  initLastₛ Top = Top
  initLastₛ (Left t s) with initLastₛ s
  initLastₛ (Left t .Top) | Top = Left Top t Top
  initLastₛ (Left t .(s ++ₛ Right t₁ Top)) | Right s t₁ s′ = Right (Left t s) t₁ {!!}
  initLastₛ (Left t .(s ++ₛ Left t₁ Top))  | Left s t₁ s′  = Left  (Left t s) t₁ {!!}
  initLastₛ (Right t s) with initLastₛ s
  initLastₛ (Right t .Top) | Top = Right Top t {!!}
  initLastₛ (Right t .(s ++ₛ Right t₁ Top)) | Right s t₁ s′ = Right (Right t s) t₁ {!!}
  initLastₛ (Right t .(s ++ₛ Left t₁ Top)) | Left s t₁   s′ = Left (Right t s) t₁ {!!}
\end{code}

\begin{code}
  to-left : Tree → Stack → Tree × Stack
  to-left Tip  s          = Tip , s
  to-left (Node t₁ t₂)  s = to-left t₁ (Left t₂ s)

  to-up-right : Tree → Stack → Maybe (Tree × Stack)
  to-up-right t (Left t₁ s)  = just ((Node t t₁) , s)
  to-up-right t (Right t₁ s) = to-up-right (Node t₁ t ) s
  to-up-right t Top          = nothing
\end{code}
%<*BURight>
\begin{code}
  right : Zipper → Maybe Zipper
\end{code}
%</BURight>
\begin{code}
  right (t , Left t₁ s)          = just (Node t t₁  , s)
  right (Tip , Right t₁ s)       = to-up-right Tip (Right t₁ s)
  right (Node t₁ t₂ , Right t s) = just (t₂ , Right t₁ (Right t s))
  right (Tip , Top)              = nothing
  right (Node t₁ t₂ , Top) = just (to-left t₂ (Right t₁ Top))

  {-# TERMINATING #-}
\end{code}

%<*BUIterate>
\begin{code}
  rightmost : Zipper → Zipper
  rightmost z with right z
  rightmost z | just z₁  = rightmost z₁
  rightmost z | nothing  = z
\end{code}
%</BUIterate>
\end{code}

%<*TDPlug>
\begin{code}
  _⊲_  : Tree → Stack → Tree
  t ⊲ Left  t₁ s  = Node (t ⊲ s) t₁
  t ⊲ Right t₁ s  = Node t₁ (t ⊲ s)
  t ⊲ Top         = t

  plug-⊲ : Zipper → Tree
  plug-⊲ (t , s) = t ⊲ s

  convert : Zipper → Zipper
  convert (t , s) = t , revₛ s
\end{code}
%</TDPlug>

%<*TDRel>
\begin{code}
  data _<_ : Zipper → Zipper → Set where
    <-Right-Step  : ∀ {t t₁ t₂ s₁ s₂}  → (t₁ , s₁) < (t₂ , s₂) → (t₁ , Right t s₁)  < (t₂ , Right t s₂)
    <-Left-Step   : ∀ {t t₁ t₂ s₁ s₂}  → (t₁ , s₁) < (t₂ , s₂) → (t₁ , Left t s₁)   < (t₂ , Left t s₂)
    <-Right-Left  : ∀ {t₁ t₂ s₁ s₂}    → (t₁ , Right (t₂ ⊲ s₂) s₁)  < (t₂ , Left (t₁ ⊲ s₁) s₂)
    <-Right-Base  : ∀ {t t₁ s₁}        → (t  , Right t₁        s₁)  < (Node t₁ (t ⊲ s₁) , Top)
    <-Left-Base   : ∀ {t t₁ s₁}        → (Node (t ⊲ s₁) t₁  , Top)  < (t , Left t₁ s₁)
\end{code}
%</TDRel>

\begin{code}
  related : ∀ z z′ →  z < z′ → plug-⊲ z ≡ plug-⊲ z′
  related (t , Left t₁ s) (t′ , .(Left t₁ _)) (<-Left-Step x)   = cong (λ x → Node x t₁) (related _ _ x)
  related (t , Right t₁ s) (t′ , Right .t₁ s′) (<-Right-Step x) = cong (λ x → Node t₁ x) (related _ _ x)
  related (t , Right .(t′ ⊲ s′) s) (t′ , Left .(t ⊲ s) s′) <-Right-Left = refl
  related (t , Right t₁ s) (.(Node t₁ (t ⊲ s)) , Top) <-Right-Base   = refl
  related (.(Node (t′ ⊲ s′) t₁) , Top) (t′ , Left t₁ s′) <-Left-Base = refl
  related (t , Top) (t′ , Right t₁ s′) ()
  related (t , Top) (t′ , Top) ()
\end{code}

%<*TDRelIx>
\begin{code}
  data [_]ₛ_<_ (t : Tree) : Zipper → Zipper → Set where
     lt :  ∀ t×s t×s′ → (eq₁ : plug-⊲ t×s   ≡ t)
                      → (eq₂ : plug-⊲ t×s′  ≡ t) → t×s < t×s′ → [ t ]ₛ t×s < t×s′

  from : ∀ t z z′ → [ t ]ₛ z < z′ → z < z′
  from t z z′ (lt .z .z′ eq₁ eq₂ x) = x

  to : ∀ z z′ → z < z′ → [ plug-⊲ z ]ₛ z < z′
  to z z′ x = lt z z′ refl (sym (related z z′ x)) x
\end{code}
%</TDRelIx>

\begin{code}
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
\end{code}
%<*WF>
\begin{code}
    <-WF : ∀ t → Well-founded ([ t ]ₛ_<_)
    <-WF t x = acc (aux t x)
\end{code}
%</WF>
\begin{code}
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
\end{code}
%<*Theorem>
\begin{code}
  just-injective : ∀ {l} {A : Set l} {x y : A} → (Maybe A ∋ just x) ≡ just y → x ≡ y
  just-injective {l} {A} {x} refl = refl

  to-up-right-preserves-⊳ : ∀ t s t′ s′ → to-up-right t s ≡ just (t′ , s′)  → t ⊳ s ≡ t′ ⊳ s′
  to-up-right-preserves-⊳ t (Left t₁ s) .(Node t t₁) .s refl = refl
  to-up-right-preserves-⊳ t (Right t₁ s) t′ s′ x = to-up-right-preserves-⊳ (Node t₁ t) s t′ s′ x
  to-up-right-preserves-⊳ t Top t′ s′ ()

  to-left-preserves-⊳ : ∀ t s t′ s′ → to-left t s ≡ (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  to-left-preserves-⊳ Tip s .Tip .s refl    = refl
  to-left-preserves-⊳ (Node t t₁) s t′ s′ x = to-left-preserves-⊳ t (Left t₁ s) t′ s′ x

  module Preservation where
    right-preserves-⊳ : ∀ z z′ → right z ≡ just z′  → plug-⊳ z ≡ plug-⊳ z′
    right-preserves-⊳ (x , Left t s) .(Node x t , s) refl = refl
    right-preserves-⊳ (Tip , Right t s) (y , s′) eq = to-up-right-preserves-⊳ (Node t Tip) s y s′ eq
    right-preserves-⊳ (Node x x₁ , Right t s) (.x₁ , .(Right x (Right t s))) refl = refl
    right-preserves-⊳ (Tip , Top) z′ ()
    right-preserves-⊳ (Node x x₁ , Top) (y , s) eq = to-left-preserves-⊳ x₁ (Right x Top) y s (just-injective eq)

  Top-ru : ∀ s → s ++ₛ Top ≡ s
  Top-ru (Left t s)  = cong (Left t) (Top-ru s)
  Top-ru (Right t s) = cong (Right t) (Top-ru s)
  Top-ru Top         = refl

  Top-lu : ∀ s → Top ++ₛ s ≡ s
  Top-lu (Left t s)  = refl
  Top-lu (Right t s) = refl
  Top-lu Top = refl

  ++ₛ-assoc : ∀ s₁ s₂ s₃ → s₁ ++ₛ (s₂ ++ₛ s₃) ≡ (s₁ ++ₛ s₂) ++ₛ s₃
  ++ₛ-assoc (Left t s₁) s₂ s₃  = cong (Left t)  (++ₛ-assoc s₁ s₂ s₃)
  ++ₛ-assoc (Right t s₁) s₂ s₃ = cong (Right t) (++ₛ-assoc s₁ s₂ s₃)
  ++ₛ-assoc Top s₂ s₃          = refl

  revₛ-r : ∀ s t → revₛ (s ++ₛ Right t Top) ≡ Right t (revₛ s)
  revₛ-r (Left t₁ s) t  = cong (λ x → x ++ₛ Left t₁ Top ) (revₛ-r s t)
  revₛ-r (Right t₁ s) t = cong (λ x → x ++ₛ Right t₁ Top) (revₛ-r s t)
  revₛ-r Top t = refl

  revₛ-l : ∀ s t → revₛ (s ++ₛ Left t Top) ≡ Left t (revₛ s)
  revₛ-l (Left t₁ s) t  = cong (λ x → x ++ₛ Left t₁ Top ) (revₛ-l s t)
  revₛ-l (Right t₁ s) t = cong (λ x → x ++ₛ Right t₁ Top) (revₛ-l s t)
  revₛ-l Top t = refl

  prop : ∀ x s t → x ⊲ revₛ (s ++ₛ Right t Top) ≡ Node t (x ⊲ revₛ s)
  prop x (Left t₁ s) t  = {!!}
  prop x (Right t₁ s) t = {!!}
  prop x Top t = refl

  pr2 : ∀ x s t → x ⊳ (s ++ₛ Right t Top) ≡ Node t (x ⊳ s)
  pr2 x (Left t₁ s) t  = pr2 (Node x t₁) s t
  pr2 x (Right t₁ s) t = pr2 (Node t₁ x) s t
  pr2 x Top t          = refl

  pr3 : ∀ x s t → x ⊳ (s ++ₛ Left t Top) ≡ Node (x ⊳ s) t
  pr3 x (Left t₁ s) t  = pr3 (Node x t₁) s t
  pr3 x (Right t₁ s) t = pr3 (Node t₁ x) s t
  pr3 x Top t          = refl

  ⊳-to-⊲ : ∀ t s → t ⊳ s ≡ t ⊲ (revₛ s)
  ⊳-to-⊲ t s  = aux t s (initLastₛ s)
    where aux : ∀ t s → InitLastₛ s → t ⊳ s ≡ t ⊲ (revₛ s)
          aux x .Top Top = refl
          aux x .(s ++ₛ Right t Top) (Right s t il)  rewrite revₛ-r s t  | pr2 x s t = cong (Node t) (aux x s il)
          aux x .(s ++ₛ Left t Top)  (Left  s t il)  rewrite revₛ-l s t  | pr3 x s t = cong (λ x → Node x t) (aux x s il)

  lemma : ∀ t₁ t₂ s₁ s₂ s → (t₁ , s₁) < (t₂ , s₂) → (t₁ , s ++ₛ s₁) < (t₂ , s ++ₛ s₂)
  lemma t₁ t₂ (Left t₃ s₁) (Left .t₃ s₂) s (<-Left-Step x) = {!!}
  lemma t₁ t₂ (Right t₃ s₁) (Left t s₂) s x = {!!}
  lemma t₁ t₂ Top (Left t s₂) s x = {!!}
  lemma t₁ t₂ s₁ (Right t s₂) s x = {!!}
  lemma t₁ t₂ (Left t s₁) Top s x = {!!}
  lemma t₁ t₂ (Right t s₁) Top s x = {!!}
  lemma t₁ t₂ Top Top s ()

  eq-pair : ∀ {A B : Set} x y a b  → x ≡ y → a ≡ b → ((A × B) ∋ (x , a)) ≡ (y , b)
  eq-pair _ _ _ _ refl refl = refl

  -- to-left : Tree → Stack → Tree × Stack
  -- to-left Tip  s          = Tip , s
  -- to-left (Node t₁ t₂)  s = to-left t₁ (Left t₂ s)

  to-left-l : ∀ t t′ s s′ → to-left t s ≡ (t′ , s′) → ∃ λ s′′ → s′ ≡ s′′ ++ₛ s 
  to-left-l Tip .Tip s .s refl     = Top , refl
  to-left-l (Node t₁ t₂) t′ s s′ x with to-left-l t₁ t′ (Left t₂ s) s′ x
  to-left-l (Node t₁ t₂) t′ s .(ss ++ₛ Left t₂ s) x | ss , refl = ss ++ₛ Left t₂ Top , {!!}

  theorem : ∀ t₁ s₁ t₂ s₂ → right (t₁ , s₁) ≡ just (t₂ , s₂) → (t₂ , revₛ s₂) < (t₁ , revₛ s₁)
  theorem Tip (Left t s₁) .(Node Tip t) .s₁ refl
    rewrite (eq-pair (Node Tip t) (Node Tip t) (revₛ s₁) (revₛ s₁ ++ₛ Top) refl (sym (Top-ru (revₛ s₁) ))) = lemma (Node Tip t) Tip Top (Left t Top) (revₛ s₁) <-Left-Base
  theorem Tip (Right t s₁) t₂ s₂ x = {!!}
  theorem Tip Top t₂ s₂ ()
  theorem (Node t₁ t₃) (Left t s₁) .(Node (Node t₁ t₃) t) .s₁ refl
    rewrite (eq-pair (Node (Node t₁ t₃) t) (Node (Node t₁ t₃) t) (revₛ s₁) (revₛ s₁ ++ₛ Top) refl (sym (Top-ru (revₛ s₁)))) = lemma (Node (Node t₁ t₃) t) (Node t₁ t₃) Top (Left t Top) (revₛ s₁) <-Left-Base
  theorem (Node t₁ t₃) (Right t s₁) .t₃ .(Right t₁ (Right t s₁)) refl = {!!} -- with the lemma again
  theorem (Node t₁ t₂) Top t s x with to-left t₂ (Right t₁ Top) | inspect (to-left t₂) (Right t₁ Top)
  theorem (Node t₁ t₂) Top .t′ .s′ refl | t′ , s′ | [ eq ] with to-left-l t₂ t′ (Right t₁ Top) s′ eq
  theorem (Node t₁ t₂) Top .t′ .(ss ++ₛ Right t₁ Top) refl | t′ , .(ss ++ₛ Right t₁ Top) | [ eq ] | ss , refl with to-left-preserves-⊳ t₂ (Right t₁ Top) _ _ eq
  ... | z rewrite pr2 t′ ss t₁ | revₛ-r ss t₁ | ⊳-to-⊲ t′ ss | (proj₂ (Node-Inj z)) = <-Right-Base

\end{code}
%</Theorem>
