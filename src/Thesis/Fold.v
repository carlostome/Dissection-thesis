Require Import Relations.
Inductive Tree : Type :=
  | Tip  : nat -> Tree
  | Node : Tree -> Tree -> Tree.

Fixpoint eval (t : Tree) : nat :=
  match t with
    | Tip x => x
    | Node t1 t2 => eval t1 + eval t2
  end.

    
(* dummy wrapper to lift Tree to Prop *)
Inductive TreeP : Prop :=
  | TreeP_Tip  : nat   -> TreeP
  | TreeP_Node : TreeP -> TreeP -> TreeP.
  
Fixpoint LiftTree (t : Tree) : TreeP :=
  match t with
    | Tip x => TreeP_Tip x
    | Node t1 t2 => TreeP_Node (LiftTree t1) (LiftTree t2)
  end.

Definition Stack : Type := list (Tree + (TreeP * nat)).
Definition Zipper : Type := nat * Stack.

(* plug_up lives in Prop because uses the TreeP from the Stack *)  
Fixpoint plug_up (t : TreeP) (s : Stack) : TreeP :=
  match s with
    | nil => t
    | cons (inl t1) s => plug_up (TreeP_Node t (LiftTree t1)) s
    | cons (inr (t1 , _)) s => plug_up (TreeP_Node t1 t) s
  end.


(* A Prop version of the Zipper *)
Inductive ZipperP : Prop := 
  | ZipperP_constr : nat * Stack -> ZipperP.

Definition LiftZipper (z : Zipper) : ZipperP :=
  ZipperP_constr (fst z , snd z).

Definition plug_up_zipper (z : ZipperP) : TreeP :=
  match z with
    | ZipperP_constr (n , s) => plug_up (TreeP_Tip n) s
  end.


Fixpoint to_left (t : Tree) (s : Stack) : Zipper + nat :=
  match t with
    | Node t1 t2 => to_left t1 (cons (inl t2) s)
    | Tip x      => inl (x , s)
  end.

Fixpoint to_up_right (t : TreeP) (n : nat) (s : Stack) : Zipper + nat :=
  match  s with
    | nil                   => inr n
    | cons (inl t1) s       => to_left t1 s
    | cons (inr (t1 , m)) s => to_up_right (TreeP_Node t1 t) (n + m) s
  end.

Definition step (z : Zipper) : Zipper + nat :=
  to_up_right (TreeP_Tip (fst z)) (fst z) (snd z).






Inductive Smaller_than : ZipperP -> ZipperP -> Prop :=
  | Right_Step : forall n t t1 t2 s1 s2, 
                   Smaller_than (ZipperP_constr (t1 , s1)) 
                                (ZipperP_constr (t2 , s2)) 
                   ->     
                   Smaller_than (ZipperP_constr (t1 , cons (inr (t , n)) s1))
                                (ZipperP_constr (t2 , cons (inr (t , n)) s2))

  | Left_Step : forall t t1 t2 s1 s2, 
                   Smaller_than (ZipperP_constr (t1 , s1)) 
                                (ZipperP_constr (t2 , s2)) -> 
                   Smaller_than (ZipperP_constr (t1 , cons (inl t) s1)) 
                                (ZipperP_constr (t2 , cons (inl t) s2))

 | Right_Left : forall n t t1 t2 s1 s2, plug_up (TreeP_Tip t1) s1 = (LiftTree t) ->
         Smaller_than (ZipperP_constr (t1 , cons (inr (plug_up (TreeP_Tip t2) s2 , n)) s1))
                      (ZipperP_constr (t2 , cons (inl t) s2)).









Inductive Smaller_than_ix (t : TreeP) : ZipperP -> ZipperP -> Prop :=
  lt : forall z1 z2, plug_up_zipper z1 = t -> plug_up_zipper z2 = t -> Smaller_than z1 z2 -> 
     Smaller_than_ix t z1 z2.
     
Notation "x < y" := (Smaller_than x y).
Notation "[ t ] x < y" := (Smaller_than_ix t x y) (at level 50).
(*
      accR : ∀ {l r : Tree} (t : ℕ) (s : Stack) eq₁
               {a : A} {eq : treeCata tAlg l ≡ a} →
               Acc ([[_]]⇓_<_ r) ((t , s) ,, Node-injᵣ eq₁) → 
             (y : Zipper⇓ (Node l r)) → [[ Node l r ]]⇓ y < ((t , inj₂ (a , l , eq) ∷ s) ,, eq₁) → Acc ([[_]]⇓_<_ (Node l r)) y
      accR t s eq₁ {a} {eq} (acc rs) .((t₁ , inj₂ (a , _ , eq) ∷ s₁) ,, refl) (<-Right-Step {t₁ = t₁} {s₁ = s₁} refl .eq₁ p)
          = acc (accR t₁ s₁ refl (rs ((t₁ , s₁) ,, refl) p))
*)
Lemma accR : forall l r t s n, Acc (Smaller_than_ix r) (ZipperP_constr (t , s)) 
           -> forall y, Smaller_than_ix (TreeP_Node l r) y 
                                        (ZipperP_constr (t , cons (inr (l , n)) s)) 
           -> Acc (Smaller_than_ix (TreeP_Node l r)) y.
Proof.
  intros l r t s n.
  intros ACC_TS y.
  intro SMALLER_Y.
  destruct SMALLER_Y.
  destruct H1.

Theorem Smaller_than_ix_acc : forall t, forall z, Acc (Smaller_than_ix t) z.
Proof.
  intros.
  rename z into x.
  constructor.
  intro.
  intro Y_LT_Z.
  
  destruct Y_LT_Z as [y x].
  destruct H1. (*as [ xt  | y | y ].*)
  - (* Both to the right *)
    Acc_ind
  - admit.
  - admit.
  
Lemma Smaller_than_acc : forall z, Acc Smaller_than z.
Proof.
  intros. destruct z. destruct p. induction s.
  + constructor. intros y H. inversion H.
    - constructor. intros.
  + destruct t.
      * admit. (*The relation 
      * 
  

Extraction Language Haskell.
Extraction  right.