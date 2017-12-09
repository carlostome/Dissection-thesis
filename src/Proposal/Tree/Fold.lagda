\begin{code}
module Proposal.Tree.Fold where

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
  open import Data.Nat.Properties
  open import Data.List
\end{code}

%<*Tree>
\begin{code}
  data Tree : Set where
    Tip   : ℕ → Tree
    Node  : (t₁ t₂ : Tree) → Tree
\end{code}
%</Tree>

%<*Stack>
\begin{code}
  data Stack : Set where
    Left   : (t : Tree)  → Stack → Stack
    Right  : (n : ℕ)     → Stack → Stack
    Top    : Stack

  Zipper = Tree × Stack
\end{code}
%</Stack>

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

  eval : Tree → ℕ
  eval (Tip x) = x
  eval (Node t t₁) = eval t + eval t₁
\end{code}


%<*Plug>
\begin{code}
  _⊲_  : Tree → Stack → Tree
  t ⊲ Left  t₁ s  = Node (t ⊲ s) t₁
  t ⊲ Right n s   = Node (Tip n) (t ⊲ s)
  t ⊲ Top         = t

  plug-⊲ : Zipper → Tree
  plug-⊲ (t , s) = t ⊲ s

  _⊳_  : Tree → Stack → Tree
  t ⊳ Left   t₁ s  = Node t t₁ ⊳ s
  t ⊳ Right  n s   = Node (Tip n) t ⊳ s
  t ⊳ Top          = t

  plug-⊳ : Zipper → Tree
  plug-⊳ (t , s) = t ⊳ s
\end{code}
%</Plug>

%<*load-unload>
\begin{code}
  unload : ℕ → Stack → (ℕ × Tree × Stack) ⊎ ℕ
  unload m Top          = inj₂ m
  unload n (Left t₁ s)  = inj₁ (n , t₁ , s)
  unload m (Right n s)  = unload (m + n) s

  load : Tree → Stack → Tree × Stack
  load (Tip n) s       = Tip n , s
  load (Node t₁ t₂) s  = load t₁ (Left t₂ s)

  load/unload : Zipper → Zipper ⊎ ℕ
  load/unload (Tip x , s)     with unload x s
  load/unload (Tip x , s) | inj₁ (n , t , s′)  = inj₁ (Node (Tip n) t , s′)
  load/unload (Tip x , s) | inj₂ y             = inj₂ y
  load/unload (Node (Tip n) t₂ , s)  = inj₁ (load t₂ (Right n s))
  load/unload (Node t₁ t₂ , s)       = inj₁ (load t₁ (Left t₂ s))
\end{code}
%</load-unload>

%<*fold>
\begin{code}
  _<_ : Zipper → Zipper → Set
  _<_ = {!!}

  <-WF : Well-founded _<_
  <-WF = {!!}

  fold : Tree → ℕ
  fold t = aux (t , Top) (<-WF (t , Top))
    where aux : (z : Zipper) → Acc _<_ z → ℕ
          aux z (acc rs) with load/unload z
          aux z (acc rs) | inj₁ z′  = aux z′ (rs z′ {!!})
          aux z (acc rs) | inj₂ n   = n
\end{code}
%</fold>

  data _<_ : Zipper → Zipper → Set where
    <-Right-Step  : ∀ {t t₁ t₂ s₁ s₂}  → (t₁ , s₁) < (t₂ , s₂) → (t₁ , Right t s₁)  < (t₂ , Right t s₂)
    <-Left-Step   : ∀ {t t₁ t₂ s₁ s₂}  → (t₁ , s₁) < (t₂ , s₂) → (t₁ , Left t s₁)   < (t₂ , Left t s₂)
    <-Right-Left  : ∀ {t₁ t₂ s₁ s₂}    → (t₁ , Right (eval (t₂ ⊲ s₂)) s₁)               < (t₂ , Left (t₁ ⊲ s₁) s₂)
    <-Right-Base  : ∀ {t t₁ s₁}        → (t  , Right (eval t₁)        s₁)               < (Node t₁ (t ⊲ s₁) , Top)
    <-Left-Base   : ∀ {t t₁ s₁}        → (Node (Tip (eval (t ⊲ s₁))) t₁  , Top)         < (t , Left t₁ s₁)

  -- -- lemma1 : ∀ n m t s s′ → unload n s ≡ inj₁ (m , t , s′)
  -- --        → ∃ λ s′′ → s ≡ s′′ ++ₛ Left t s′ × allRight s′′ × m ≡ n + (sum (forget s′′))
  -- -- lemma1 n .n t (Left .t s) .s refl = Top , (refl , refl , {!!}) -- easy 0 identity
  -- -- lemma1 n m t (Right n₁ s) s′ x with lemma1 (n + n₁) m t s s′ x
  -- -- lemma1 n m t (Right n₁ .(s ++ₛ Left t s′)) s′ x | s , refl , pr , eq = (Right n₁ s) , refl , ((cong (Right n₁) pr) , {!!}) -- easy assoc for +
  -- -- lemma1 n m t Top s′ ()

  -- Top-ru : ∀ s → s ++ₛ Top ≡ s
  -- Top-ru (Left t s)  = cong (Left t) (Top-ru s)
  -- Top-ru (Right t s) = cong (Right t) (Top-ru s)
  -- Top-ru Top         = refl

  -- Top-lu : ∀ s → Top ++ₛ s ≡ s
  -- Top-lu (Left t s)  = refl
  -- Top-lu (Right t s) = refl
  -- Top-lu Top = refl

  -- ++ₛ-assoc : ∀ s₁ s₂ s₃ → s₁ ++ₛ (s₂ ++ₛ s₃) ≡ (s₁ ++ₛ s₂) ++ₛ s₃
  -- ++ₛ-assoc (Left t s₁) s₂ s₃  = cong (Left t)  (++ₛ-assoc s₁ s₂ s₃)
  -- ++ₛ-assoc (Right t s₁) s₂ s₃ = cong (Right t) (++ₛ-assoc s₁ s₂ s₃)
  -- ++ₛ-assoc Top s₂ s₃          = refl

  -- revₛ-++ₛ-distr : ∀ s₁ s₂ → revₛ (s₁ ++ₛ s₂) ≡ revₛ s₂ ++ₛ revₛ s₁
  -- revₛ-++ₛ-distr (Left t s₁) s₂ rewrite ++ₛ-assoc (revₛ s₂) (revₛ s₁) (Left t Top)   = cong (λ x → x ++ₛ Left t Top) (revₛ-++ₛ-distr s₁ s₂)
  -- revₛ-++ₛ-distr (Right t s₁) s₂ rewrite ++ₛ-assoc (revₛ s₂) (revₛ s₁) (Right t Top) = cong (λ x → x ++ₛ Right t Top) (revₛ-++ₛ-distr s₁ s₂)
  -- revₛ-++ₛ-distr Top s₂ rewrite Top-ru (revₛ s₂) = refl

  -- -- lemma : ∀ n m t s s′ → unload n s ≡ inj₁ (m , t , s′) → (Node (Tip m) t , revₛ s′) < (Tip n , revₛ s)
  -- -- lemma n .n t (Left .t s) .s refl = {!!}
  -- -- lemma n m t (Right n₁ s) s′ x with lemma1 (n + n₁) m t s s′ x
  -- -- lemma n m t (Right n₁ .(s ++ₛ Left t s′)) s′ x | s , refl , proj₃ , proj₄ rewrite revₛ-++ₛ-distr s (Left t s′) = {!!} -- should be easy
  -- -- lemma n m t Top s′ ()

  -- -- lemmass : ∀ n m t s s′ → unload n s ≡ inj₁ (m , t , s′) → (t , revₛ (Right m s′)) < (Tip n , revₛ s)
  -- -- lemmass n .n t (Left .t s) .s refl = {!!}
  -- -- lemmass n m t (Right n₁ s) s′ x with lemma1 (n + n₁) m t s s′ x
  -- -- lemmass n m t (Right n₁ .(s ++ₛ Left t s′)) s′ x | s , refl , proj₅ , proj₆ = {!!}
  -- -- lemmass n m t Top s′ ()

  -- -- unload′ : (n : ℕ) → (s : Stack) → (∃ λ n′ → ∃₂ λ t s′ → (Node (Tip n′) t , revₛ s′) < (Tip n , revₛ s)) ⊎ ℕ
  -- -- unload′ n s with unload n s | inspect (unload n) s4)  How to Twist Pointers without Breaking them
  -- -- unload′ n s | inj₁ (n′ , t , s′) | [ eq ] = inj₁ (n′ , (t , s′ , lemma n n′ t s s′ eq))
  -- -- unload′ n s | inj₂ y | _ = inj₂ y





  data _isPartialOf_ : Tree → Tree → Set where
    base-l : ∀ {t₁ t₂ t₃ n} → eval (Node t₁ t₂) ≡ n → (Node (Tip n) t₃) isPartialOf (Node (Node t₁ t₂) t₃)
    base-r : ∀ {t₁ t₂ t₃ n} → eval (Node t₁ t₂) ≡ n → (Node t₃ (Tip n)) isPartialOf (Node t₃ (Node t₁ t₂))
    step   : ∀ {t₁ t₂ t₃  } → t₁ isPartialOf t₂ → Node t₁ t₃ isPartialOf Node t₂ t₃
    step-r : ∀ {n t₁ t₂   } → t₁ isPartialOf t₂ → Node (Tip n) t₁ isPartialOf Node (Tip n) t₂

  isPartial : ∀ z z′ → z < z′ → (plug-⊲ z) isPartialOf (plug-⊲ z′)
  isPartial (t , Left t₁ s) z′ x = {!!}
  isPartial (t , Right n s) z′ x = {!!}
  isPartial (.(Node (Tip (eval (t′ ⊲ s′))) t₁) , Top) (t′ , Left t₁ s′) <-Left-Base = {!!}
  isPartial (t , Top) (t′ , Right n s′) ()
  isPartial (t , Top) (t′ , Top) ()

  mutual
    pr1 : ∀ n x → Acc _isPartialOf_ x → WfRec _isPartialOf_ (Acc _isPartialOf_) (Node (Tip n) x)
    pr1 n x (acc rs) (Tip x₂) ()
    pr1 n .(Node _ _) (acc rs) (Node .(Tip n) .(Tip _)) (base-r x) = acc (stop _ n)
    pr1 n x (acc rs) (Node t₁ .x) (step ())
    pr1 n x (acc rs) (Node .(Tip n) t₂) (step-r p) = acc (pr1 n t₂ (rs t₂ p))

    pr2 : ∀ t x → Acc _isPartialOf_ x → Acc _isPartialOf_ t → WfRec _isPartialOf_ (Acc _isPartialOf_) (Node x t)
    pr2 t x x₁ _ (Tip x₃) ()
    pr2 t .(Node _ _) ac acc1 (Node .(Tip _) .t) (base-l x) = acc (pr1 _ t acc1)
    pr2 .(Node _ _) x ac _ (Node .x .(Tip _)) (base-r x₁) = acc (pr3 x _ ac)
    pr2 t x (acc rs) ac (Node t₁ .t) (step p) = acc (pr2 t t₁ (rs t₁ p) ac)
    pr2 t .(Tip _) ac _ (Node .(Tip _) t₂) (step-r p) = acc (pr1 _ t₂ (aux t t₂ p))

    pr3 : ∀ x n → Acc _isPartialOf_ x → WfRec _isPartialOf_ (Acc _isPartialOf_) (Node x (Tip n))
    pr3 .(Node _ _) n ac .(Node (Tip _) (Tip n)) (base-l x) = acc (stop n _)
    pr3 x n (acc rs) .(Node _ (Tip n)) (step x₁) = acc (pr3 _ n (rs _ x₁))
    pr3 .(Tip _) n ac .(Node (Tip _) _) (step-r ())

    stop : ∀ m n → WfRec _isPartialOf_ (Acc _isPartialOf_) (Node (Tip n) (Tip m))
    stop m n (Tip x₁) ()
    stop m n (Node y .(Tip m)) (step ())
    stop m n (Node .(Tip n) y₁) (step-r ())

    aux : ∀ x → WfRec _isPartialOf_ (Acc _isPartialOf_) x
    aux (Tip x₁) y ()
    aux (Node .(Node _ _) x₁) .(Node (Tip _) x₁) (base-l x₂) = acc (pr1 _ x₁ (isPartialOf-WF x₁))
    aux (Node x .(Node _ _)) .(Node x (Tip _)) (base-r x₂)   = acc (pr3 x _ (isPartialOf-WF x))
    aux (Node x x₁) .(Node _ x₁) (step p)                    = acc (pr2 x₁ _ (aux x _ p) (isPartialOf-WF x₁))
    aux (Node .(Tip _) x₁) .(Node (Tip _) _) (step-r p) = acc (pr1 _ _ (aux x₁ _ p))

    isPartialOf-WF : Well-founded _isPartialOf_
    isPartialOf-WF x = acc (aux x)


  --   _<_ : Tree × Stack → Tree × Stack → Set
  --   z < z′ = (plug-⊳ z) isPartialOf (plug-⊳ z′)



  --   eval-step : (ℕ × Stack) → (ℕ × Tree × Stack) ⊎ ℕ
  --   eval-step (n , s) with unload n s
  --   eval-step (n , s) | inj₁ (m , t₁ , s′) with load t₁ (Right m s′)
  --   eval-step (n , s) | inj₁ (m , t₁ , s′) | m′′ , s′′ = unload m′′ s′′
  --   eval-step (n , s) | inj₂ y = inj₂ y

  --   p = eval-step (3 , Left (Tip 1) (Right (5) (Left (Tip 4) Top)))

  --   lemmasss : ∀ n m s t′ s′ → eval-step (n , s) ≡ inj₁ (m , t′ , s′) → (Node (Tip m) t′ , s′) < (Tip n , s)
  --   lemmasss n m (Left (Tip x₁) s) t′ s′ x = {!!}
  --   lemmasss n m (Left (Node t t₁) s) t′ s′ x = {!!}
  --   lemmasss n m (Right n₁ s) t′ s′ x = {!!}
  --   lemmasss n m Top t′ s′ ()
  --   -- lemmasss (Tip x₁) (Left t s) t′ s′ x  = {!!}
  --   -- lemmasss (Tip x₁) (Right n s) t′ s′ x = {!!}
  --   -- lemmasss (Tip x₁) Top t′ s′ ()
  --   -- lemmasss (Node t t₁) s t′ s′ x = {!!}
  --   -- lemma-comp : (t : Tree) (s s′ : Stack) (n m : ℕ) → comp n s ≡ inj₁ (t , s′) → (t , s′) < (Tip n , s)
  --   -- lemma-comp t (Left t₁ s) s′ n m x  with load t (Right m s′)
  --   -- lemma-comp t (Left t₁ s) s′ n m x | t′ , s′′ = {!x!}
  --   -- lemma-comp t (Right n₁ s) s′ n m x = {!!}
  --   -- lemma-comp t Top s′ n m ()
  --   -- lemma-unload t (Left _ s) .s n _ refl = {!!}
  --   -- lemma-unload t (Right n₁ s) s′ n m x = {!!}
  --   -- lemma-unload t Top s′ n m ()

  -- -- p : (Node (Tip 3) (Tip 4)) isPartialOf (Node (Node (Tip 1) (Tip 2)) (Tip 4))
  -- -- p = base-l refl

  -- -- load/unload : Tree → ℕ
  -- -- load/unload t with load t Top
  -- -- ... | t′ , s′ = aux {!!} s′ (<-WF ({!!} , revₛ s′))
  -- --   where
  -- --     aux : (t : PTree) → (s : Stack) → Acc _<_ (t , revₛ s) → ℕ
  -- --     aux (Tip n) s (acc rs)    with unload n s | inspect (unload n) s
  -- --     aux (Tip n) s (acc rs) | inj₁ (t , s′) | [ eq ] = aux t s′ (rs (t , revₛ s′) (lemma-unload n t s s′ eq))
  -- --     aux (Tip n) s (acc rs) | inj₂ m        | -      = m
  -- --     aux (Node n t) s (acc rs) with load {!!} s | inspect (load {!!}) s
  --     -- aux (Node n t) s (acc rs) | _ , s′ | [ eq ]    = aux (Tip {!!}) (Right n s′) (rs (((Tip {!!}) , revₛ (Right n s′))) {!!})
\end{code}
