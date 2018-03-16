\begin{code}
module Graph where

  open import Data.Unit
  open import Data.Nat
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Induction.WellFounded
  open import Data.Sum
  data Type : Set where
    nat  : Type
    _⇒_  : Type → Type → Type

  ⟦_⟧ : Type → Set
  ⟦ nat ⟧   = ℕ
  ⟦ t ⇒ s ⟧ = ⟦ t ⟧ → ⟦ s ⟧

  -- Graph reduction from Implementing functional programming languages
  data Graph : Type → Set where
    _◆_  : ∀ {σ τ} → Graph (σ ⇒ τ) → Graph σ → Graph τ
    em   : ∀ {τ}   → ⟦ τ ⟧                   → Graph τ

  ◆-injective : ∀ {τ σ} {f g : Graph (σ ⇒ τ)} {x y : Graph σ} → f ◆ x ≡ g ◆ y → f ≡ g × x ≡ y
  ◆-injective refl = refl , refl

  infixl 50 _◆_

  -- (+ 6 (+ 5 4))
  expr₁ : Graph nat 
  expr₁ = (em _+_ ◆ em 6) ◆ (em _+_ ◆ em 5 ◆ em 4)

  _$_ : ∀ {A B : Set} → (A → B) → A → B
  f $ x = f x
  
  eval : ∀ {ty} → Graph ty → ⟦ ty ⟧
  eval (f ◆ x) = eval f $ eval x
  eval (em x)  = x

  data Stack⇓ : Type → Type → Set where
    nil   : ∀ {σ}     → Stack⇓ σ σ
    left  : ∀ {σ} {τ} → Graph σ                                            → Stack⇓ (σ ⇒ τ) (σ ⇒ τ) → Stack⇓ (σ ⇒ τ) τ
    right : ∀ {σ} {τ} → (g : Graph (σ ⇒ τ)) → (f : ⟦ σ ⟧  → ⟦ τ ⟧) → eval g ≡ f → Stack⇓ σ σ        → Stack⇓ σ τ

  plug⇓ : ∀ {τ σ} → Graph τ → Stack⇓ τ σ → Graph σ
  plug⇓ g nil             = g
  plug⇓ g (left x s)      = plug⇓ g s ◆ x
  plug⇓ g (right f _ _ s) = f ◆ plug⇓ g s

  data Decomp⇓ (τ : Type) : Set where
    _,_ : ∀ {σ} (g : Graph σ) → (s : Stack⇓ σ τ) → Decomp⇓ τ

  plugD⇓ : ∀ {τ} →  Decomp⇓ τ → Graph τ
  plugD⇓ (g , s) = plug⇓ g s
  
  data [[_]]_<_ : (τ : Type) → Decomp⇓ τ → Decomp⇓ τ → Set where
    <-Right-step : ∀ {τ} {f} {g g₁ g₂} {s₁ s₂} {eq : eval g ≡ f} → [[ τ ]]     ( g₁ , s₁ ) < (g₂ , s₂) → [[ τ ]] (g₁ , right g f eq s₁) < (g₂ , right g f eq s₂)
    <-Left-Step  : ∀ {τ σ} {g g₁ g₂} {s₁ s₂}                     → [[ τ ⇒ σ ]] ( g₁ , s₁ ) < (g₂ , s₂) → [[ σ ]] (g₁ , left g s₁)       < (g₂ , left g s₂)
    <-Right-left : ∀ {τ σ} {f : ⟦ σ ⟧ → ⟦ τ ⟧} {g₁ g₂} {s₁ s₂} {g₁′ g₂′} {eq : eval g₁′ ≡ f} → g₁′ ≡ plug⇓ g₂ s₂
                                                                                             → g₂′ ≡ plug⇓ g₁ s₁ → [[ τ ]] (g₁ , right g₁′ f eq s₁) < (g₂ , left g₂′ s₂)
                                                                                             
  data [_][_]_<_ (τ : Type) (g : Graph τ) : Decomp⇓ τ → Decomp⇓ τ → Set where
    lt : (z₁ z₂ : Decomp⇓ τ) → plugD⇓ z₁ ≡ g → plugD⇓ z₂ ≡ g → [[ τ ]] z₁ < z₂ → [ τ ][ g ] z₁ < z₂

  mutual
    accR : ∀ {τ} {σ} (l : Graph (σ ⇒ τ)) (r : Graph σ) a s f eq → Acc [ σ ][ r ]_<_ (a , s)  → WfRec ([ τ ][ l ◆ r ]_<_) (Acc ([ τ ][ l ◆ r ]_<_)) (a , right l f eq s)
    accR l .(plug⇓ g₁ s₁) a s f eq (acc rs) .(g₁ , right l f eq s₁) (lt .(g₁ , right l f eq s₁) .(a , right l f eq s) refl eq₂ (<-Right-step {g₁ = g₁} {s₁ = s₁} p))
      = acc (accR l (plug⇓ g₁ s₁) g₁ s₁ f eq (rs (g₁ , s₁) (lt (g₁ , s₁) (a , s) refl (proj₂ (◆-injective eq₂)) p)))

    accL : ∀ {τ} {σ} (l : Graph (σ ⇒ τ)) (r : Graph σ) a s → Acc [ σ ⇒ τ ][ l ]_<_ (a , s)  → WfRec ([ τ ][ l ◆ r ]_<_) (Acc ([ τ ][ l ◆ r ]_<_)) (a , left r s)
    accL .(plug⇓ g₁ s₁) r a s (acc rs) .(g₁ , left r s₁) (lt .(g₁ , left r s₁) .(a , left r s) refl eq₂ (<-Left-Step {g₁ = g₁} {s₁ = s₁} p))
      = acc (accL (plug⇓ g₁ s₁) r g₁ s₁ (rs (g₁ , s₁) (lt (g₁ , s₁) (a , s) refl (proj₁ (◆-injective eq₂)) p)))
    accL .(plug⇓ a s) .(plug⇓ g₁ s₁) a s (acc rs) .(g₁ , right (plug⇓ a s) f eq s₁)
         (lt .(g₁ , right (plug⇓ a s) f eq s₁) .(a , left (plug⇓ g₁ s₁) s) refl eq₂ (<-Right-left {f = f} {g₁} {s₁ = s₁} {eq = eq} refl refl))
      = acc (accR (plug⇓ a s) (plug⇓ g₁ s₁) g₁ s₁ f eq (<-WF (plug⇓ g₁ s₁) (g₁ , s₁)))
    
    <-WF : ∀ {τ} (g : Graph τ) → Well-founded [ τ ][ g ]_<_
    <-WF g x = acc (aux g x)
      where
        aux : ∀ {τ} (t : Graph τ) (x : Decomp⇓ τ) → WfRec ([ τ ][ t ]_<_) (Acc ([ τ ][ t ]_<_)) x
        aux {τ} .(g ◆ plug⇓ g₂ s₁) (g₁ , .(right g f eq s₂)) (g₂ , .(right g f eq s₁))
                 (lt .(g₂ , right g f eq s₁) .(g₁ , right g f eq s₂) refl eq₂ (<-Right-step {f = f} {g} {s₁ = s₁} {s₂} {eq} p))
          = acc (accR g (plug⇓ g₂ s₁) g₂ s₁ f eq (<-WF (plug⇓ g₂ s₁) (g₂ , s₁)))
        aux .(plug⇓ g₂ s₁ ◆ g) (g₁ , .(left g s₂)) (g₂ , .(left g s₁))
            (lt .(g₂ , left g s₁) .(g₁ , left g s₂) refl eq₂ (<-Left-Step {g = g} {s₁ = s₁} {s₂} p))
          = acc (accL (plug⇓ g₂ s₁) g g₂ s₁ (<-WF (plug⇓ g₂ s₁) (g₂ , s₁)))
        aux .(plug⇓ g₁ s₂ ◆ plug⇓ g₂ s₁) (g₁ , .(left (plug⇓ g₂ s₁) s₂)) (g₂ , .(right (plug⇓ g₁ s₂) f eq s₁))
            (lt .(g₂ , right (plug⇓ g₁ s₂) f eq s₁) .(g₁ , left (plug⇓ g₂ s₁) s₂) refl refl
                (<-Right-left {f = f} {s₁ = s₁} {s₂} {.(plug⇓ g₁ s₂)} {.(plug⇓ g₂ s₁)} {eq} refl refl))
          = acc (accR (plug⇓ g₁ s₂) (plug⇓ g₂ s₁) g₂ s₁ f eq (<-WF (plug⇓ g₂ s₁) (g₂ , s₁)))

  data Stack⇑ : Type → Type → Set where
    nil   : ∀ {σ}         → Stack⇑ σ σ
    left  : ∀ {σ} {τ} {ρ} → Graph σ                                                 → Stack⇑ τ ρ  → Stack⇑ (σ ⇒ τ) ρ
    right : ∀ {σ} {τ} {ρ} → (g : Graph (σ ⇒ τ)) → (f : ⟦ σ ⟧  → ⟦ τ ⟧) → eval g ≡ f → Stack⇑ τ ρ  → Stack⇑ σ ρ
  
  plug⇑ : ∀ {τ σ} → Graph σ → Stack⇑ σ τ → Graph τ
  plug⇑ g nil              = g
  plug⇑ g (left x s)       = plug⇑ (g ◆ x) s
  plug⇑ g (right h f x s)  = plug⇑ (h ◆ g) s

  data Decomp⇑ (τ : Type) : Set where
    _,_ : ∀ {σ} (e : ⟦ σ ⟧) → (s : Stack⇑ σ τ) → Decomp⇑ τ

  plugD⇑ : ∀ {τ} →  Decomp⇑ τ → Graph τ
  plugD⇑ (e , s) = plug⇑ (em e) s
  
  wind : ∀ {τ σ} → Graph σ → Stack⇑ σ τ → Decomp⇑ τ ⊎ ⟦ τ ⟧
  wind (f ◆ x) s =  wind f (left x s)
  wind (em x)  s =  inj₁ (x , s)

  unwind : ∀ {τ σ} → (g : Graph τ) → (v : ⟦ τ ⟧) → eval g ≡ v → Stack⇑ τ σ → Decomp⇑ σ ⊎ ⟦ σ ⟧
  unwind g v eq nil              = inj₂ v
  unwind g v eq (left x s)       = wind x (right g v eq s)
  unwind g v eq (right g₁ f x s) = unwind (g₁ ◆ g) (f v) {!!} s

  step : ∀ {σ} → Decomp⇑ σ → Decomp⇑ σ ⊎ ⟦ σ ⟧
  step (e , s) = unwind (em e) e refl s

  app : ∀ {σ τ} → Stack⇓ σ τ → Stack⇓ σ σ → Stack⇓ σ τ
  app nil y               = y
  app (left x xs) ys      = left x (app xs ys)
  app (right g f x xs) ys = right g f x (app xs ys)
  
  Stack⇑-to-Stack⇓ : ∀ {σ τ} → Stack⇑ σ τ → Stack⇓ σ τ
  Stack⇑-to-Stack⇓ nil = nil
  Stack⇑-to-Stack⇓ (left x s)      = app (Stack⇑-to-Stack⇓ {!s!}) {!left!}
  Stack⇑-to-Stack⇓ (right g f x s) = app {!!} {!!}

  convert : ∀ {σ} → Decomp⇑ σ → Decomp⇓ σ
  convert (e , s) = (em e) , {!!}
