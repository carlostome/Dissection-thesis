\begin{code}
module Proposal.Dissection where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; _,_)
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
  open import Data.List    using (List; []; _∷_)

  open import Proposal.FDesc
  open import Proposal.BiFDesc
\end{code}

%<*Dissection>
\begin{code}
  ∇ : FDesc -> BiFDesc
  ∇ I₁        = K₂ ⊤
  ∇ (K₁ A)    = K₂ ⊥
  ∇ (f +₁ g)  = ∇ f +₂ ∇ g
  ∇ (p ×₁ q)  = ∇ p ×₂ J q +₂ C p ×₂ ∇ q
\end{code}
%</Dissection>

%<*right>
\begin{code}
  mutual
    right : ∀ {c j : Set} (P : FDesc)
          → (⟦ P ⟧₁ j ⊎  (⟦ ∇ P ⟧₂ c j × c)) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧₁ c)
    right I₁ (inj₁ j)         = inj₁ (j , tt)
    right I₁ (inj₂  (tt , c)) = inj₂ c

    right (K₁ A) (inj₁ x)     = inj₂ x
    right (K₁ A) (inj₂ (() , _))

    right (P +₁ Q) (inj₁ (inj₁ pj))   with right P (inj₁ pj)
    ... | inj₁ (j , pd)  = inj₁ (j , inj₁ pd)
    ... | inj₂ pc        = inj₂ (inj₁ pc)
    right (P +₁ Q) (inj₁ (inj₂ qj))   with right Q (inj₁ qj)
    ... | inj₁ (j , qd′)  = inj₁ (j , (inj₂ qd′))
    ... | inj₂ qc         = inj₂ (inj₂ qc)
    right (P +₁ Q) (inj₂ (inj₁ pd , c)) with right P (inj₂ (pd , c))
    ... | inj₁ (j , pd′)  = inj₁ (j , inj₁ pd′)
    ... | inj₂ pc         = inj₂ (inj₁ pc)
    right (P +₁ Q) (inj₂ (inj₂ qd , c)) with right Q (inj₂ (qd , c) )
    ... | inj₁ (j , qd′)  = inj₁ (j , (inj₂ qd′))
    ... | inj₂ qc         = inj₂ (inj₂ qc)

    right (P ×₁ Q) (inj₁ (pj , qj)) = goL P Q (right P (inj₁ pj)) qj
    right (P ×₁ Q) (inj₂ (inj₁ (pd , qj) , c))  = goL P Q (right P (inj₂ (pd , c))) qj
    right (P ×₁ Q) (inj₂ (inj₂ (pc , qd) , c))  = goR P Q pc (right Q (inj₂ (qd , c)))

    private
      goL : ∀ {c j : Set} (P Q : FDesc) → ((j × ⟦ ∇ P ⟧₂ c j) ⊎ ⟦ P ⟧₁ c) → ⟦ Q ⟧₁ j
                                        → ((j × ⟦ ∇ (P ×₁ Q) ⟧₂ c j) ⊎ ⟦ P ×₁ Q ⟧₁ c)
      goL P Q (inj₁ (j , pd)) qj = inj₁ (j , inj₁ (pd , qj))
      goL P Q (inj₂ pc)       qj = goR P Q pc (right Q (inj₁ qj))

      goR : ∀ {c j : Set} (P Q : FDesc) → ⟦ P ⟧₁ c → ((j × ⟦ ∇ Q ⟧₂ c j) ⊎ ⟦ Q ⟧₁ c)
                                        → ((j × ⟦ ∇ (P ×₁ Q) ⟧₂ c j) ⊎ ⟦ P ×₁ Q ⟧₁ c)
      goR P Q pc (inj₁ (j , qd)) = inj₁ (j , (inj₂ (pc , qd)))
      goR P Q pc (inj₂ y)        = inj₂ (pc , y)
\end{code}
%</right>

%<*tcata>
\begin{code}
  module Raw-tcata where
    {-# TERMINATING #-}
    mutual
      load   : ∀ {A : Set} (F : FDesc) -> (⟦ F ⟧₁ A → A) -> μ F → List (⟦ ∇ F ⟧₂ A (μ F)) → A
      load F φ (μ-in x) stk = next F φ (right F (inj₁ x)) stk

      unload : ∀ {A : Set} (F : FDesc) → (⟦ F ⟧₁ A -> A) → A -> List (⟦ ∇ F ⟧₂ A (μ F)) → A
      unload F φ v []          = v
      unload F φ v (pd ∷ stk)  = next F φ (right F (inj₂ (pd , v))) stk

      next : ∀ {A : Set} (F : FDesc) → (⟦ F ⟧₁ A → A)
          → (μ F × ⟦ ∇ F ⟧₂ A (μ F)) ⊎ ⟦ F ⟧₁ A → List (⟦ ∇ F ⟧₂ A (μ F)) → A
      next F φ (inj₁ (t , pd)) stk  = load F φ t (pd ∷ stk)
      next F φ (inj₂ pv) stk        = unload F φ (φ pv) stk

    tcata : ∀ {A : Set} (F : FDesc) -> (⟦ F ⟧₁ A -> A) -> μ F -> A
    tcata F φ m = load F φ m []
\end{code}

%</tcata>

