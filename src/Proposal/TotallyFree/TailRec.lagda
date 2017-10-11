\begin{code}
module Proposal.TotallyFree.TailRec where

  open import Data.Nat     using (ℕ ; zero; suc; _+_)
  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Stream
  open import Agda.Builtin.Coinduction
  open import Function
  open import Data.List
  open import Data.Unit
  open import Data.Empty

  open import Proposal.Expr

  -- tail recursive functions [I → O]
  -- TailRec I O ~ General I (λ _ → ⊥) O
  data TailRec (I : Set) (O : Set) : Set where
    return   : O → TailRec I O
    call⟨_⟩  : I → TailRec I O

  fold : ∀ {I O} {X : Set} → (I → X) → (O → X) → TailRec I O → X
  fold f g (return x)  = g x
  fold f g call⟨ x ⟩   = f x

  -- a tail recursive program
  _⟶_ : Set → Set → Set
  I ⟶ O = (i : I) → TailRec I O

  infixr 1 _⟶_

  -- expand a TailRec given a function I → O
  expand : ∀ {I O} → I ⟶ O → TailRec I O → TailRec I O
  expand f = fold f return

  -- petrol-driven semantics
  engine : ∀ {I O} (f : I ⟶ O ) (n : ℕ) → TailRec I O → TailRec I O
  engine f zero    = id
  engine f (suc n) = engine f n ∘ expand f

  stream : ∀ {I O} (f : I ⟶ O) → TailRec I O → Stream (TailRec I O)
  stream f m = m ∷ ♯ (stream f (expand f m))

  module Example where

    foldl' : ∀ { A B : Set} → (A → B → A) → A × List B ⟶ A
    foldl' f (b , [])     = return b
    foldl' f (b , x ∷ xs) = call⟨ f b x , xs ⟩

    load/unload : (Expr ⊎ ℕ) × Stack ⟶ ℕ
    -- load
    load/unload (inj₁ (Val x) , stk)    = call⟨ inj₂ x , stk ⟩
    load/unload (inj₁ (Add l r) , stk)  = call⟨ inj₁ l , Left r stk ⟩
    -- unload
    load/unload (inj₂ v , Nil)          = return v
    load/unload (inj₂ v , Left r stk)   = call⟨ inj₁ r , Right v stk ⟩
    load/unload (inj₂ v , Right v' stk) = call⟨ inj₂ (v + v') , stk ⟩

    example : Stream (TailRec ((Expr ⊎ ℕ) × Stack) ℕ)
    example = stream load/unload call⟨ (inj₁ (Add (Val 1) (Add (Val 2) (Val 3))) , Nil) ⟩

  -- for TailRec we would like to be able to reify the BC predicate.
  -- we need a type of descriptions that capture this and then a run function
  -- over the BC that terminates.
  -- good luck!

  data CDesc (I : Set) : Set₁ where
    `1 : CDesc I
    `X : (i : I) → CDesc I

  ⟦_⟧ : ∀ { I : Set } → CDesc I → (I → Set) → Set
  ⟦ `1 ⟧ X    = ⊤
  ⟦ `X i ⟧ X  = X i

  record CFunc (I : Set) : Set₁ where
    constructor mk
    field func : I → CDesc I

  data μ {I : Set} (R : CFunc I) (i : I) : Set where
    con : ⟦ CFunc.func R i ⟧ (μ R) → μ R i

  -- from a tail recursive program prog we can build a Bove-Capretta predicate
  module BC {I : Set} {O : Set} (prog : I ⟶ O) where

    dom : TailRec I O → CDesc I
    dom (return _) = `1
    dom call⟨ a ⟩  = `X a

    Dom : CFunc I
    Dom = CFunc.mk λ x → dom (prog x)

    mutual
      run : (input : I) → μ Dom input → O
      run i (con domS)  = run1 (prog i) (mapRun {prog i} domS)
    -- --   run : (a : A) → μ Dom a → B a
    -- --   run a (con domS) = run1 (prog a) (mapRun {p = prog a} domS)

      mapRun : ∀{p : TailRec I O} → ⟦ dom p ⟧ (μ Dom) → ⟦ dom p ⟧ (λ _ → O)
      mapRun {return x₁} tt  = tt
      mapRun {call⟨ a ⟩} x   = run a x
    --   -- mapRun {p = returnRec x} tt = tt
    --   -- mapRun {p = callRec a rec} (domA , domRec) =
    --   --   run a domA , λ b → mapRun {p = rec b} (domRec b)

      run1 : (p : TailRec I O ) → ⟦ dom p ⟧ (λ _ → O) → O
      run1 (return x) tt  = x
      run1 call⟨ x ⟩ d    = d

  module Silly-Function where

    silly : ℕ ⟶ ℕ
    silly zero    = return zero
    silly (suc x) = call⟨ x ⟩

    DomSilly : ℕ → Set
    DomSilly = μ (BC.Dom silly)

    silly-bove : ∀ (n : ℕ) → DomSilly n → ℕ
    silly-bove = BC.run silly

    silly-wf : (n : ℕ) →  DomSilly n
    silly-wf zero    = con tt
    silly-wf (suc n) = con (silly-wf n)

    silly' : ℕ → ℕ
    silly' n = silly-bove n (silly-wf n)

  module TL-length where

    aux : ∀ {A : Set} → ℕ × List A ⟶ ℕ
    aux (l , [])     = return l
    aux (l , x ∷ xs) = call⟨ (1 + l) , xs ⟩

    DomAux : ∀ {A : Set} (inp : ℕ × List A) → Set
    DomAux = μ (BC.Dom aux)

    aux-bove : ∀ {A : Set} (inp : ℕ × List A) → DomAux inp → ℕ
    aux-bove = BC.run aux

    aux-wf : ∀ {A : Set} (inp : ℕ × List A) → DomAux inp
    aux-wf (l , [])     = con tt
    aux-wf (l , x ∷ xs) = {!!}

  Dom-load/unload : (Expr ⊎ ℕ) × Stack → Set
  Dom-load/unload = μ (BC.Dom Example.load/unload)

  load/unload-Bove : ∀ (inp : (Expr ⊎ ℕ) × Stack) → Dom-load/unload inp → ℕ
  load/unload-Bove = BC.run Example.load/unload

  load/unload-wf : ∀ (inp : (Expr ⊎ ℕ) × Stack) → Dom-load/unload inp
  load/unload-wf = {!!}

  load-unload' : (Expr ⊎ ℕ) × Stack → ℕ
  load-unload' inp = load/unload-Bove inp (load/unload-wf inp) 

  example-expr = Add (Val 1) (Add (Val 2) (Val 3))

  init : Expr → (Expr ⊎ ℕ) × Stack
  init e = inj₁ e , Nil

\end{code}
