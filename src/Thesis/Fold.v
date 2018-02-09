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
Definition Zipper : Type := Tree * Stack.

Fixpoint to_left (t : Tree) (s : Stack) : Zipper :=
  match t with
    | Node t1 t2 => to_left t1 (cons (inl t2) s)
    | Tip x      => (Tip x , s)
  end.

(* plug_up lives in Prop because uses the TreeP from the Stack *)  
Fixpoint plug_up (t : TreeP) (s : Stack) : TreeP :=
  match s with
    | nil => t
    | cons (inl t1) s => plug_up (TreeP_Node t (LiftTree t1)) s
    | cons (inr (t1 , _)) s => plug_up (TreeP_Node t1 t) s
  end.

Definition plug_up_zipper (z : Zipper) : TreeP :=
  plug_up (LiftTree (fst z)) (snd z).

Lemma to_left_preserves_plug_up : 
  forall t s t' s', to_left t s = (t' , s') -> plug_up (LiftTree t) s = plug_up (LiftTree t') s'.
Proof.
  intro.
  induction t.
    + intros. inversion H. reflexivity.
    + intros. simpl in H. apply IHt1 in H. simpl in H. assumption.
Qed.

(* the (t : TreeP) is only hold to reconstruct the full Tree *)
Fixpoint to_up_right (t : TreeP) (n : nat) (s : Stack) : Zipper + nat :=
  match  s with
    | nil                   => inr n
    | cons (inl t1) s       => inl (t1 , cons (inr (t , n)) s)
    | cons (inr (t1 , m)) s => to_up_right (TreeP_Node t1 t) (n + m) s
  end.

Lemma to_up_right_preservers_plug_up : 
  forall t s t' s' n , to_up_right t n s = inl (t' , s') 
    -> plug_up t s = plug_up (LiftTree t') s'.
Proof.
  intros t s.
  generalize dependent t.
  induction s.
    + intros. inversion H.
    + intros. destruct a.
      * inversion H. simpl. reflexivity.
      * destruct p. inversion H. apply IHs in H1. simpl. assumption.
Qed.

Definition right (z : Zipper) : Zipper + nat :=
  match z with
    | (Tip x , s)      => to_up_right (TreeP_Tip x) x s
    | (Node t1 t2 , s) => inl (to_left (Node t1 t2) s)
  end.
 
Lemma right_preserves_plug_up :
 forall t s t' s', right (t , s) = inl (t' , s') 
    -> plug_up (LiftTree t) s = plug_up (LiftTree t') s'.
Proof.
  intros.
  destruct t.
    + simpl. apply (to_up_right_preservers_plug_up _ _ _ _ n). assumption.
    + apply (to_left_preserves_plug_up). inversion H. simpl. reflexivity.
Qed.

(* A Prop version of the Zipper *)
Inductive ZipperP : Prop := 
  | ZipperP_constr : TreeP * Stack -> ZipperP.

Definition LiftZipper (z : Zipper) : ZipperP :=
  ZipperP_constr (LiftTree (fst z) , snd z).

Inductive Smaller_than : ZipperP -> ZipperP -> Prop :=
  | Right_Left : forall n t t1 t2 s1 s2, plug_up t1 s1 = (LiftTree t) ->
                   Smaller_than (ZipperP_constr (t1 , cons (inr (plug_up t2 s2 , n)) s1))
                                (ZipperP_constr (t2 , cons (inl t) s2))

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
  | Right_base : forall t t1 s n, 
                   Smaller_than (ZipperP_constr (t1 , cons (inr (t , n)) s))
                                (ZipperP_constr (TreeP_Node t1 (plug_up t s) , nil)).
                                
                                
Notation "x < y" := (Smaller_than x y).

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