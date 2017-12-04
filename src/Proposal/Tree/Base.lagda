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
  open import Data.Nat hiding (_<_)

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

  infixl 20 _++ₛ_

  revₛ : Stack → Stack
  revₛ (Left t s)   = revₛ s ++ₛ Left   t Top
  revₛ (Right t s)  = revₛ s ++ₛ Right  t Top
  revₛ Top = Top

  data Reverseₛ : Stack → Set where
    Top    : Reverseₛ Top
    Right  : (s : Stack) (t : Tree) → Reverseₛ s → Reverseₛ (s ++ₛ Right t Top)
    Left   : (s : Stack) (t : Tree) → Reverseₛ s → Reverseₛ (s ++ₛ Left  t Top)

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

  revₛ-++ₛ-distr : ∀ s₁ s₂ → revₛ (s₁ ++ₛ s₂) ≡ revₛ s₂ ++ₛ revₛ s₁
  revₛ-++ₛ-distr (Left t s₁) s₂ rewrite ++ₛ-assoc (revₛ s₂) (revₛ s₁) (Left t Top)   = cong (λ x → x ++ₛ Left t Top) (revₛ-++ₛ-distr s₁ s₂)
  revₛ-++ₛ-distr (Right t s₁) s₂ rewrite ++ₛ-assoc (revₛ s₂) (revₛ s₁) (Right t Top) = cong (λ x → x ++ₛ Right t Top) (revₛ-++ₛ-distr s₁ s₂)
  revₛ-++ₛ-distr Top s₂ rewrite Top-ru (revₛ s₂) = refl

  revₛ-helper : ∀ {xs : Stack} → Reverseₛ xs -> (ys : Stack) -> Reverseₛ (xs ++ₛ ys)
  revₛ-helper {xs} x (Left t ys)  with revₛ-helper (Left xs t x) ys
  ... | z rewrite ++ₛ-assoc xs (Left t Top) ys = z
  revₛ-helper {xs} x (Right t ys) with revₛ-helper (Right xs t x) ys
  ... | z rewrite ++ₛ-assoc xs (Right t Top) ys = z 
  revₛ-helper {xs} x Top rewrite Top-ru xs = x

  reverseₛ : (s : Stack) → Reverseₛ s
  reverseₛ s = revₛ-helper Top s

\end{code}

%<*BURight>
\begin{code}
  to-left : Tree → Stack → Maybe Zipper
  to-left Tip  s          = just (Tip , s)
  to-left (Node t₁ t₂) s  = to-left t₁ (Left t₂ s)

  to-up-right : Tree → Stack → Maybe Zipper
  to-up-right t (Left t₁ s)   = just ((Node t t₁) , s)
  to-up-right t (Right t₁ s)  = to-up-right (Node t₁ t ) s
  to-up-right t Top           = nothing

  right : Zipper → Maybe Zipper
  right (t , Left t₁ s)           = just (Node t t₁  , s)
  right (Tip , Right t₁ s)        = to-up-right (Node t₁ Tip) s
  right (Node t₁ t₂ , Right t s)  = just (t₂ , Right t₁ (Right t s))
  right (Tip , Top)               = nothing
  right (Node t₁ t₂ , Top)        = to-left t₂ (Right t₁ Top)
\end{code}
%</BURight>

\begin{code}

  module Rightmost-non-term where
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

\begin{code}
  module Rightmost-skeleton where
\end{code}

%<*Skeleton>
\begin{code}
    data _<_ : Zipper → Zipper → Set where

    <-Well-founded : Well-founded _<_
    <-Well-founded = {!!}

    to-right-< : (z z′ : Zipper) → right z ≡ just z′ → z′ < z
    to-right-< = {!!}

    rightmost : Zipper → Zipper
    rightmost x = aux x (<-Well-founded x)
      where aux : (z : Zipper) → Acc _<_ z → Zipper
            aux z (acc rs) with right z | inspect right z
            aux z (acc rs) | just z′  | [ eq ]  = aux z′ (rs z′ (to-right-< z z′ eq))
            aux z (acc rs) | nothing  | _       = z
\end{code}
%</Skeleton>

%<*TDPlug>
\begin{code}
  _⊲_  : Tree → Stack → Tree
  t ⊲ Left  t₁ s  = Node (t ⊲ s) t₁
  t ⊲ Right t₁ s  = Node t₁ (t ⊲ s)
  t ⊲ Top         = t

  plug-⊲ : Zipper → Tree
  plug-⊲ (t , s) = t ⊲ s
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

%<*Related>
\begin{code}
  related : ∀ z z′ →  z < z′ → plug-⊲ z ≡ plug-⊲ z′
  related = ∙∙∙
\end{code}
%</Related>
\begin{code}
    where ∙∙∙ : ∀ z z′ →  z < z′ → plug-⊲ z ≡ plug-⊲ z′
          ∙∙∙ (t , Left t₁ s) (t′ , .(Left t₁ _)) (<-Left-Step x)   = cong (λ x → Node x t₁) (related _ _ x)
          ∙∙∙ (t , Right t₁ s) (t′ , Right .t₁ s′) (<-Right-Step x) = cong (λ x → Node t₁ x) (related _ _ x)
          ∙∙∙ (t , Right .(t′ ⊲ s′) s) (t′ , Left .(t ⊲ s) s′) <-Right-Left = refl
          ∙∙∙ (t , Right t₁ s) (.(Node t₁ (t ⊲ s)) , Top) <-Right-Base   = refl
          ∙∙∙ (.(Node (t′ ⊲ s′) t₁) , Top) (t′ , Left t₁ s′) <-Left-Base = refl
          ∙∙∙ (t , Top) (t′ , Right t₁ s′) ()
          ∙∙∙ (t , Top) (t′ , Top) ()
\end{code}

%<*TDRelIx>
\begin{code}
  data [_]ₛ_<_ (t : Tree) : Zipper → Zipper → Set where
     lt :  ∀ t×s t×s′ → (eq₁ : plug-⊲ t×s   ≡ t)
                      → (eq₂ : plug-⊲ t×s′  ≡ t) → t×s < t×s′ → [ t ]ₛ t×s < t×s′
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

\begin{code}
  just-injective : ∀ {l} {A : Set l} {x y : A} → (Maybe A ∋ just x) ≡ just y → x ≡ y
  just-injective {l} {A} {x} refl = refl

  to-up-right-preserves-⊳ : ∀ t s t′ s′ → to-up-right t s ≡ just (t′ , s′)  → t ⊳ s ≡ t′ ⊳ s′
  to-up-right-preserves-⊳ t (Left t₁ s) .(Node t t₁) .s refl = refl
  to-up-right-preserves-⊳ t (Right t₁ s) t′ s′ x = to-up-right-preserves-⊳ (Node t₁ t) s t′ s′ x
  to-up-right-preserves-⊳ t Top t′ s′ ()

  to-left-preserves-⊳ : ∀ t s t′ s′ → to-left t s ≡ just (t′ , s′) → t ⊳ s ≡ t′ ⊳ s′
  to-left-preserves-⊳ Tip s .Tip .s refl    = refl
  to-left-preserves-⊳ (Node t t₁) s t′ s′ x = to-left-preserves-⊳ t (Left t₁ s) t′ s′ x

  right-preserves-⊳ : ∀ z z′ → right z ≡ just z′  → plug-⊳ z ≡ plug-⊳ z′
  right-preserves-⊳ (x , Left t s) .(Node x t , s) refl = refl
  right-preserves-⊳ (Tip , Right t s) (y , s′) eq = to-up-right-preserves-⊳ (Node t Tip) s y s′ eq
  right-preserves-⊳ (Node x x₁ , Right t s) (.x₁ , .(Right x (Right t s))) refl = refl
  right-preserves-⊳ (Tip , Top) z′ ()
  right-preserves-⊳ (Node x x₁ , Top) (y , s) eq = to-left-preserves-⊳ x₁ (Right x Top) y s eq

  ⊳-++ₛ-Right : ∀ {x} {t} s → x ⊳ (s ++ₛ Right t Top) ≡ Node t (x ⊳ s)
  ⊳-++ₛ-Right (Left t s)   = ⊳-++ₛ-Right s
  ⊳-++ₛ-Right (Right t s)  = ⊳-++ₛ-Right s
  ⊳-++ₛ-Right Top          = refl

  ⊳-++ₛ-Left : ∀ {x} {t} s → x ⊳ (s ++ₛ Left t Top) ≡ Node (x ⊳ s) t
  ⊳-++ₛ-Left (Left t s)   = ⊳-++ₛ-Left s
  ⊳-++ₛ-Left (Right t s)  = ⊳-++ₛ-Left s
  ⊳-++ₛ-Left Top          = refl

  ⊲-++ₛ-Right : ∀ {x} {t} s → x ⊲ (s ++ₛ Right t Top) ≡ Node t x ⊲ s
  ⊲-++ₛ-Right (Left t s)   = cong (flip Node t) (⊲-++ₛ-Right s)
  ⊲-++ₛ-Right (Right t s)  = cong (Node t) (⊲-++ₛ-Right s)
  ⊲-++ₛ-Right Top          = refl

  ⊲-++ₛ-Left : ∀ {x} {t} s → x ⊲ (s ++ₛ Left t Top) ≡ Node x t ⊲ s
  ⊲-++ₛ-Left (Left t s)   = cong (flip Node t) (⊲-++ₛ-Left s)
  ⊲-++ₛ-Left (Right t s)  = cong (Node t) (⊲-++ₛ-Left s)
  ⊲-++ₛ-Left Top          = refl
\end{code}

%<*Convert>
\begin{code}
  convert : Zipper → Zipper
  convert (t , s) = t , revₛ s

  ⊳-to-⊲ : ∀ (z : Zipper) → plug-⊳ z ≡ plug-⊲ (convert z)
  ⊳-to-⊲ (t , s) = aux t s (reverseₛ s)
    where aux : ∀ t s → Reverseₛ s → t ⊳ s ≡ t ⊲ (revₛ s)
          aux t .Top Top                             = refl
          aux t .(s ++ₛ Right t₁ Top) (Right s t₁ x)
            rewrite revₛ-++ₛ-distr s (Right t₁ Top)
                  | ⊳-++ₛ-Right {t} {t₁}s         = cong (Node t₁) (aux t s x)
          aux t .(s ++ₛ Left t₁ Top) (Left s t₁ x)
            rewrite revₛ-++ₛ-distr s (Left t₁ Top)
                  | ⊳-++ₛ-Left {t} {t₁} s         = cong (flip Node t₁) (aux t s x)

  ⊲-to-⊳ : ∀ z → plug-⊲ z ≡ plug-⊳ (convert z)
  ⊲-to-⊳ = ∙∙∙
\end{code}
%</Convert>
\begin{code}
    where aux : ∀ t s → Reverseₛ s → t ⊲ s ≡ t ⊳ (revₛ s)
          aux t .Top Top = refl
          aux t .(s ++ₛ Right t₁ Top) (Right s t₁ x)
            rewrite revₛ-++ₛ-distr s (Right t₁ Top)
                  | ⊲-++ₛ-Right {t} {t₁} s        = aux (Node t₁ t) s x
          aux t .(s ++ₛ Left t₁ Top) (Left s t₁ x)
            rewrite revₛ-++ₛ-distr s (Left t₁ Top)
                  | ⊲-++ₛ-Left {t} {t₁} s         = aux (Node t t₁) s x

          ∙∙∙ : ∀ z → plug-⊲ z ≡ plug-⊳ (convert z)
          ∙∙∙ (t , s) = aux t s (reverseₛ s)
\end{code}

\begin{code}

  -- we can prepend any stack and get what we need
  lemma : ∀ {t₁ t₂ s₁ s₂} → (t₁ , s₁) < (t₂ , s₂) → ∀ s → (t₁ , s ++ₛ s₁) < (t₂ , s ++ₛ s₂)
  lemma x (Left t s)  = <-Left-Step  (lemma x s)
  lemma x (Right t s) = <-Right-Step (lemma x s)
  lemma x Top         = x

  eq-pair : ∀ {A B : Set} x y a b  → x ≡ y → a ≡ b → ((A × B) ∋ (x , a)) ≡ (y , b)
  eq-pair _ _ _ _ refl refl = refl

  to-left-l : ∀ t t′ s s′ → to-left t s ≡ just (t′ , s′) → ∃ λ s′′ → s′ ≡ s′′ ++ₛ s 
  to-left-l Tip .Tip s .s refl     = Top , refl
  to-left-l (Node t₁ t₂) t′ s s′ x with to-left-l t₁ t′ (Left t₂ s) s′ x
  to-left-l (Node t₁ t₂) t′ s .(ss ++ₛ Left t₂ s) x | ss , refl rewrite ++ₛ-assoc ss (Left t₂ Top) s = ss ++ₛ Left t₂ Top , refl

  to-up-right-l : ∀ t t′ s s′ → to-up-right t s ≡ just (t′ , s′) → ∃ λ s′′ → s ≡ s′′ ++ₛ s′
  to-up-right-l t .(Node t t₁) (Left t₁ s) .s refl = (Left t₁ Top) , refl
  to-up-right-l t t′ (Right t₁ s) s′ x with to-up-right-l (Node t₁ t) t′ s s′ x
  to-up-right-l t t′ (Right t₁ .(s′′ ++ₛ s′)) s′ x | s′′ , refl = Right t₁ s′′ , refl
  to-up-right-l t t′ Top s′ ()

  propi  : ∀ t s t′ s′ t₁ → (t , s) < (Node t₁ t′ , s ++ₛ s′) → (t , s) < (t′ , s ++ₛ s′ ++ₛ Right t₁ Top)
  propi t (Left t₂ s) t′ s′ t₁ (<-Left-Step x) = <-Left-Step (propi t s t′ s′ t₁ x)
  propi t (Right t₂ s) t′ s′ t₁ (<-Right-Step x) = <-Right-Step (propi t s t′ s′ t₁ x)
  propi t Top t′ (Left t₂ s′) t₁ x with related _ _ x
  propi .(Node (Node t₁ t′ ⊲ s′) t₂) Top t′ (Left t₂ s′) t₁ <-Left-Base | refl rewrite (sym (⊲-++ₛ-Right {t′} {t₁} s′ )) = <-Left-Base
  propi t Top t′ (Right t₂ s′) t₁ ()
  propi t Top t′ Top t₁ ()

  to-u : ∀ t t′ s s′ →  to-up-right t s ≡ just (t′ , s′) → (t′ , revₛ s′) < (t , revₛ s)
  to-u t .(Node t t₁) (Left t₁ s) .s refl
    rewrite (eq-pair (Node t t₁) (Node t t₁) (revₛ s) (revₛ s ++ₛ Top) refl (sym (Top-ru (revₛ s)))) = lemma <-Left-Base (revₛ s)
  to-u t t′ (Right t₁ s) s′ x with to-up-right-l (Node t₁ t) _ s _ x
  to-u t t′ (Right t₁ .(s′′ ++ₛ s′)) s′ x | s′′ , refl with to-u (Node t₁ t) t′ (s′′ ++ₛ s′) s′ x
  ... | z rewrite revₛ-++ₛ-distr s′′ s′ = propi t′ (revₛ s′) t (revₛ s′′) t₁ z
  to-u t t′ Top s′ ()

  theorem : ∀ t₁ s₁ t₂ s₂ → right (t₁ , s₁) ≡ just (t₂ , s₂) → convert (t₂ , s₂) < convert (t₁ , s₁)
  theorem Tip (Left t s) .(Node Tip t) .s refl
    rewrite (eq-pair (Node Tip t) (Node Tip t) (revₛ s) (revₛ s ++ₛ Top) refl (sym (Top-ru (revₛ s)))) = lemma <-Left-Base (revₛ s)
  theorem Tip (Right t s₁) t₂ s₂ x = to-u Tip t₂ (Right t s₁) s₂ x
  theorem Tip Top t₂ s₂ ()
  theorem (Node t₁ t₃) (Left t s₁) .(Node (Node t₁ t₃) t) .s₁ refl
    rewrite (eq-pair (Node (Node t₁ t₃) t) (Node (Node t₁ t₃) t) (revₛ s₁) (revₛ s₁ ++ₛ Top) refl (sym (Top-ru (revₛ s₁)))) = lemma  <-Left-Base (revₛ s₁) 
  theorem (Node t₁ t₂) (Right t s₁) .t₂ .(Right t₁ (Right t s₁)) refl 
    rewrite (eq-pair (Node t₁ t₂) (Node t₁ t₂) (revₛ s₁ ++ₛ Right t Top) ((revₛ s₁ ++ₛ Right t Top) ++ₛ Top) refl (sym (Top-ru (revₛ s₁ ++ₛ Right t Top)))) = lemma <-Right-Base (revₛ s₁ ++ₛ Right t Top)
  theorem = {!!}
  -- theorem (Node t₁ t₂) Top t s x with to-left t₂ (Right t₁ Top) | inspect (to-left t₂) (Right t₁ Top)
  -- theorem (Node t₁ t₂) Top .t′ .s′ refl | just (t′ , s′) | [ eq ] with to-left-l t₂ t′ (Right t₁ Top) s′ eq
  -- theorem (Node t₁ t₂) Top .t′ .(ss ++ₛ Right t₁ Top) refl | t′ , .(ss ++ₛ Right t₁ Top) | [ eq ] | ss , refl with to-left-preserves-⊳ t₂ (Right t₁ Top) _ _ eq
  -- .
  -- .. | z rewrite ⊲-++ₛ-Right {t′} {t₁} ss | revₛ-r ss t₁ | ⊳-to-⊲ (t′ , ss) = {!!} -- (proj₂ (Node-Inj z)) = {!!} -- <-Right-Base

  -- rightmostt : Zipper  → Zipper
  -- rightmostt (t , s) rewrite (sym (⊳-to-⊲ t s)) = aux (t , s) (<-WF (t ⊳ s) (t , revₛ s))
  --   where aux : ∀ (z : Zipper) → Acc ([ plug-⊳ z ]ₛ_<_) (convert z) → Zipper
  --         aux z (acc rs) with right z | inspect right z
  --         aux (t , s) (acc rs) | just (t′ , s′) | [ eq ] with theorem t s t′ s′ eq | right-preserves-⊳ ((t , s)) (t′ , s′) eq
  --         ... | p | z rewrite z = aux ((t′ , s′)) (rs (t′ , revₛ s′) (lt (t′ , revₛ s′) (t , revₛ s) (sym (⊳-to-⊲ t′ s′)) (trans (sym (⊳-to-⊲ t s)) z)  p))
  --         aux z (acc rs) | nothing | e = z

\end{code}
%</Theorem>
