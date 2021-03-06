%include generic.fmt

\chapter{A verified generic tail-recursive catamorphism}
\label{chap:generic}

In the previous \namecref{chap:expression}, \cref{chap:expression}, we showed
how to \emph{manually} construct a tail-recursive evaluation function for the
type of binary trees, and prove that is both terminating and equal to the
original fold. 

%{
%format load = "\AF{load}"
%format unload = "\AF{unload}"
In this chapter, we build upon this work and we define a terminating tail-recursive
function that we prove equivalent to any fold over any (simple) algebraic
datatype that can be generically expressed in the \emph{regular} universe. We
begin in \cref{sec:generic:dissection}, recapitulating the idea of
\emph{dissection}, due to \cite{McBride:2008:CLM:1328438.1328474}, and show how
it leads (\Cref{sec:generic:stack,sec:generic:genconf}) to the definition of
generic configurations of the abstract machine. Subsequently, in
\cref{sec:generic:onestep}, we introduce the generic version of the functions
|load| and |unload|, which compute one step of the fold. In
\cref{sec:generic:relation} we set up the relation over generic configurations
and present its well-foundedness proof. Finally, in
\cref{sec:generic:machine}, we define the terminating tail-recursive abstract
machine as the iteration of the one step function fueled by well-founded
recursion. The correctness proof, \cref{sec:generic:correct}, follows directly
from the construction. In \cref{sec:generic:example}, we present some examples
of the generic tail-recursive fold in action. We conclude this chapter
(\Cref{sec:generic:discussion}) discussing some open issues about the
construction.
%}

\section{Dissection}
\label{sec:generic:dissection}

The configurations of the abstract machine, which computes the tail-recursive
fold for the type |Expr|, are instances of a more general concept: McBride's
dissections~\citeyearpar{McBride:2008:CLM:1328438.1328474}. We briefly recap this
construction, showing how it allow us to calculate the type of configurations of
the abstract machine that computes the catamorphism of any type expressible in
the regular universe (\Cref{subsec:background:regular}).

The key definition of \emph{dissections} is a new interpretation function over
the regular universe, |nabla|, that maps elements of the universe into
bifunctors:
%
\begin{code}
  nabla : (R : Reg) -> (Set -> Set -> Set)
  nabla Zero      X Y  = Bot
  nabla One       X Y  = Bot
  nabla I         X Y  = Top
  nabla (K A)     X Y  = Bot
  nabla (R O+ Q)  X Y  = nabla R X Y U+ nabla Q X Y
  nabla (R O* Q)  X Y  = (nabla R X Y * interpl Q interpr Y)  U+  (interpl R interpr X * nabla Q X Y)
\end{code}

Following the metaphor of a functor as a container of things, the reader may
find useful to think of its dissection as tearing apart the container in two
subcontainers. The elements contained in the left subcontainer do not need to be
of the same type as those stored in the right. The |nabla| operation
applied to a code |R : Reg| considers all the possible ways in which exactly one of
the recursive positions---code |I|, inhabited by terms of type |X|---is in focus
and serves as the breaking point. Because only one variable is specially
distinguished, the recursive positions appearing to its left can be interpreted
over a different type than those on its right: this is where |nabla| differs
from a \emph{zipper}. 

The last clause of the definition of |nabla| is of particular interest: to
\emph{dissect} a product, we either \emph{dissect} the left component pairing it
with the second component interpreted over the second variable |Y|; or we
\emph{dissect} the right component and pair it with the first interpreted over
|X|.

A \emph{dissection} is then formally defined as the pair of the context,
resulting from \emph{dissecting} a concrete code |R|,  and the missing value
that fits in it:
%
\begin{code}
  Dissection : (R : Reg) -> (X Y : Set) -> Set
  Dissection R X Y = nabla R X Y * Y
\end{code}

Given a \emph{dissection}, we define a |plug| operation that assembles the
context and current value in focus to produce a value of type |interpl R interpr
Y|:
%
\begin{code}
  plug : (R : Reg) -> (X -> Y) -> Dissection R X Y -> interpl R interpr Y
  plug Zero      eta  (Empty , x)
  plug One       eta  (Empty , x)
  plug I         eta  (tt , x)             = x
  plug (K A)     eta  (Empty , x)
  plug (R O+ Q)  eta  (inj1 r , x)         = inj1 (plug R eta (r , x))
  plug (R O+ Q)  eta  (inj2 q , x)         = inj2 (plug Q eta (q , x))
  plug (R O* Q)  eta  (inj1 (dr , q) , x)  = (plug R eta (dr , x)  , q)
  plug (R O* Q)  eta  (inj2 (r , dq) , x)  = (fmap R eta r         , plug Q eta (dq , x))
\end{code}
%
In the last clause of the definition, the dissected value is the right component
of the pair, leaving |r : interpl R interpr X| to the left. In such case, it is
only possible to construct a term of type |interpl R interpr Y| if we have a
function |eta| to recover |Y|s from the |X|s contained in |r|.

Using a type-indexed type, we can bundle together a dissection with the value 
of type |interpl R interpr Y| to which it \emph{plug}s:
%
\begin{code}
  data IxDissection (R : Reg) (X Y : Set) (eta : X -> Y) (tx : interpl R interpr Y) : Set where
    prodOp : (d : Dissection R X Y) -> plug R eta d == tx -> IxDissection R X Y eta tx 
\end{code}

\section{Generic stacks}
\label{sec:generic:stack}

While the \emph{dissection} computes the bifunctor underlying the functorial
layer of the generic tree, we still need to take the fixed point of this bifunctor
to obtain the type of stacks of the generic abstract machine. 

A generic tree, |mu R|, is a recursive structure formed by layers of the functor
with code |R| interpreted over generic trees, |interpl R interpr (mu R)|. A
dissection calculates how a concrete layer can be decomposed into a subtree in
focus and its context, but, on its own it does not account for the recursivity
induced by the fixed point. In order to focus on a subtree that may be deeply
buried within the generic tree, we need to take a list of dissections, where
each element of the list is a particular dissection of the corresponding
functorial layer. As an analogy, in the |Expr| datatype each constructor |Add|
corresponds to a value of the functorial layer where there are recursive
occurrences---marked with code |I|. Each time we decompose a layer, we select a
subexpression, or subtree, such that the rest of the stack points to a leaf in
it. In the case of |Expr| each constructor of the |Stack1| records the specific
subexpression, left or right, while in the generic case, the value of the
dissection marks the selected subtree. The |Stack1| for |Expr| is a list of
|Left| or |Right| constructors that account for all the occurrences of the
constructor |Add| in a value of type |Expr|. Thus, in the generic case we use a
list of dissections for all the intermediate nodes---that is, functorial
layers---that have recursive subtrees. The type of generics stacks is as
follows:

\begin{code}
  StackG : (R : Reg) -> (X Y : Set) -> Set
  StackG R X Y = List (nabla R X Y)
\end{code}
%
Huet's zipper corresponds with instantiating both |X| and |Y| to
generic trees of type |mu R|. Given such instantiation, we can define a pair 
of functions that reconstruct the tree by traversing the stack:
%
\begin{code}
  plug-mudownG  : (R : Reg) -> mu R -> StackG R (mu R) (mu R) -> mu R
  plug-mudownG R t []         = t
  plug-mudownG R t (h :: hs)  = In (plug R id (h , plug-mudownG R t hs))

  plug-muupG  : (R : Reg) -> mu R -> StackG R (mu R) (mu R) -> mu R
  plug-muupG R t []         = t
  plug-muupG R t (h :: hs)  = plug-muupG R (In (plug R id (h , t))) hs
\end{code}
%
We can interpret the zipper both as the path starting from the root and
descending to the subtree in focus, |plug-mudownG|, or beginning from the
position of the subtree and navigating up to the root, |plug-muupG|. We pass 
the identity function to |plug| because the left side of the dissection already 
stores generic trees.

An abstract machine, which computes the tail-recursive catamorphism, traverses a
generic tree from left to right. The stack of such machine is a list of
dissections of type |nabla X (mu R)|: for each of the subtrees that have been
already processed we store a value of type |X|, while we save those that still
have to be visited untouched---type |mu R|.

As we did in the concrete tail-recursive evaluator for the type |Expr|,
\cref{subsec:expression:invariant}, we have to keep extra information in the
stack to assist \Agda's termination checker and later prove correctness of the
construction. For such matter, we define a record type that stores values,
subtrees, and the corresponding correctness proofs:
%
\begin{code}
 record Computed (R : Reg) (X : Set) (alg : interpl R interpr X -> X) : Set where
    constructor _,_,_
    field
      Tree   : mu R
      Value  : X
      Proof  : Catamorphism R alg Tree Value
\end{code}
%
\begin{digression}

Compared to the stack of the tail-recursive evaluator, |tail-rec-eval|, the type
of correctness proofs is not anymore propositional equality, but a custom
relation that reifies the function |catamorphism|:
%
\begin{code}
  data Catamorphism (R : Reg) (alg : interpl R interpr X -> X) : mu R -> X -> Set where

    Cata : {i : interpl R interpr (mu R)} {o : interpl R interpr X}  -> MapFold R alg R i o 
                                                                     -> Catamorphism R alg (In i) (alg o)

  data  MapFold (Q : Reg) (alg : interpl Q interpr X -> X)  : (R : Reg) 
                                                           -> interpl R interpr (mu Q) -> interpl R interpr X -> Set where
    MapFold-One  : MapFold Q alg One tt tt
    MapFold-I    : {i : interpl Q interpr (mu Q)} {o : interpl Q interpr X} 
                 -> MapFold Q alg Q i o -> MapFold Q alg I (In i) (alg o)
    MapFold-K    : {a : A}  -> MapFold Q alg (K A) a a
    MapFold-+1   : {R P : Reg} {i : interpl R interpr (mu Q)} {o : interpl R interpr X} 
                 -> MapFold Q alg R i o -> MapFold Q alg (R O+ P) (inj1 i) (inj1 o)
    MapFold-+2   : {R P : Reg} {i : interpl P interpr (mu Q)} {o : interpl P interpr X} 
                 -> MapFold Q alg P i o -> MapFold Q alg (R O+ P) (inj1 i) (inj2 o)
    MapFold-*    :  {R P : Reg} {i1 : interpl R interpr (mu Q)} {i2 : interpl P interpr (mu Q)} 
                    {o1 : interpl R interpr X} {o2 : interpl P interpr X} 
                 ->  MapFold Q alg R i1 o1 -> MapFold Q alg P i2 o2 
                 ->  MapFold Q alg (R O* P) (i1 , i2) (o1 , o2)
\end{code}
%
The reason for choosing a relation over propositional equality is practical:
most of the functions and theorems are inductively defined over the generic
code. A datatype indexed by the same code facilitates building proofs for each
specific case. Nonetheless, from a value of the reified function we are able to
recover the propositional equality proof:
%
\begin{code}
  MapFold-to-mapFold  :   forall (Q : Reg) -> (alg : interpl Q interpr X -> X) -> (R : Reg) 
                          -> (t : interpl R interpr (mu Q)) -> (x : interpl R interpr X) 
                          -> MapFold Q alg R t x -> mapFold R Q alg t ≡ x
\end{code}
%
\begin{code}
  Cata-to-cata  : forall (R : Reg) -> (alg : interpl R interpr X -> X) -> (t : mu R) -> (x : X) 
                -> Catamorphism R alg t x -> cata R alg t ≡ x
  Cata-to-cata R alg ..(In i) ..(alg o) (Cata {i} {o} x) 
    = cong alg (MapFold-to-mapFold R alg R i o x)
\end{code}
%
In the rest of this chapter, we use propositional equality to indicate equality
whereas in the accompanying code, for every function that is involved in a
equality proof, we use a datatype that reifies the call graph of such function.
\end{digression}

Finally, the type of stacks of the generic abstract machine is defined as a
list of \emph{dissections}: on the left we have the |Computed| results; on the
right, we have the subtrees of type |mu R|:
%
\begin{code}
  Stack : (R : Reg) -> (X : Set) -> (alg : interpl R interpr X -> X) -> Set
  Stack R X alg = List (nabla R (Computed R X alg) (mu R))
\end{code}
%
Note that the |Stack| datatype is parametrised by the algebra |alg| as the
|Proof| field of the |Computed| record refers to it.

Given a stack, |Stack|, and the subtree in focus, |mu R|, we define two
different \emph{plugging} operations: one top-down, another bottom-up:
%
\begin{code}
  plug-mudown   : (R : Reg) -> {alg : interpl R interpr X -> X}
                -> mu R -> Stack R X alg -> mu R
  plug-mudown R t []         = t
  plug-mudown R t (h :: hs)  = In (plug R Computed.Tree h (plug-mudown R t hs))

  plug-muup   : (R : Reg) -> {alg : interpl R interpr X -> X}
              -> mu R -> Stack R X alg -> mu R
  plug-muup R t []         = t
  plug-muup R t (h :: hs)  = plug-muup R (In (plug R Computed.Tree h t)) hs
\end{code}
%
Both functions pass the projection |Computed.Tree| as an argument to |plug| to
extract the subtree from the |Computed| record.

\section{Generic configurations}
\label{sec:generic:genconf}

Recapitulating from the tail-recursive evaluator, |tail-rec-eval|, the type of
configurations of the abstract machine represent locations within the expression
that is being evaluated. However, we are not interested in any location within the
generic tree, but only on those paths that lead to a leaf. A question, then, is to be
asked: what constitutes a leaf in the generic setting?

First, let us recall the two different levels of recursion present in a generic tree: 
  \begin{enumerate}
      \item At the functorial layer, because the universe allows
        functors to be combined: the (co)product of two functors is also a
        functor. 
      \item At fixed point level, because positions marked with the constructor |I|
        are interpreted over generic subtrees.
  \end{enumerate}
It would be troubled to enforce that a leaf is truly non-recursive value,
thus, we consider only to be leaves those values of the functor layer that do
not contain subtrees, but otherwise might be recursive because of (1).

To describe a generic leaf, we introduce the following predicate:
%
\begin{code}
  data NonRec : (R : Reg) -> interpl R interpr X -> Set where
    NonRec-One  : NonRec One tt
    NonRec-K    : (B : Set) -> (b : B) -> NonRec (K B) b
    NonRec-+1   : (R Q : Reg) -> (r : interpl R interpr X)
                -> NonRec R r -> NonRec (R O+ Q) (inj1 r)
    NonRec-+2   : (R Q : Reg) -> (q : interpl Q interpr X)
                -> NonRec Q q -> NonRec (R O+ Q) (inj2 q)
    NonRec-*    : (R Q : Reg) -> (r : interpl R interpr X) -> (q : interpl Q interpr X)
                -> NonRec R r -> NonRec Q q -> NonRec (R O* Q) (r , q)

\end{code}
%
Given a value of type |t : interpl R interpr X|, the predicate is only true,
i.e. we can build a term of type |NonRec R t|, \emph{iff} it has no occurrences of
elements of type |X|.

As an example, in the pattern functor for the \AD{Expr} type, |K Nat O+ (I O* I)|,
terms built using the left injection are non-recursive: 
%
\begin{code}
Val-NonRec : forall (n : Nat) -> NonRec (K Nat O+ (I O* I)) (inj1 n)
Val-NonRec : n = NonRec-+1 (K Nat) (I O* I) n (NonRec-K Nat n)
\end{code}
%
This corresponds to the idea that the constructor |Val| is a leaf in a tree of
type |Expr|. 

On the other hand, we cannot prove that the predicate |NonRec| holds for
terms using the right injection. The occurrences of recursive positions disallow
us from constructing the proof (The type |NonRec| does not have a constructor such as
|NonRec-I : (x : X) -> NonRec I x|).

Now, we define the notion of leaf generically; it is a value of the functor
layer that does not have recursive subtrees:\footnote{|Sigma| is \Agda's type
for dependent pair.}
%
\begin{code}
  Leaf : Reg -> Set -> Set
  Leaf R X = Sigma (interpl R interpr X) (NonRec R)
\end{code}

A leaf is independent of the type |X|, the predicate |NonRec| proves it, thus
we can coerce it to a different type:
%
\begin{code}
  coerce : (R : Reg) -> (x : interpl R interpr X) -> NonRec R x -> interpl R interpr Y  
\end{code}
%
The function is defined by induction over the proof |NonRec R x|. The case for
the code |I| is eliminated which means we do not have to produce a value of
type |Y| out of thin air.

Just as before, a generic configuration is given by the current leaf in
focus and the stack that stores partial results and unprocessed subtrees---or
points to it:
%
\begin{code}
  Zipper : (R : Reg) -> (X : Set) -> (alg : interpl R interpr X -> X) -> Set
  Zipper R X alg = Leaf R X * Stack R X alg
\end{code}

From a configuration of the abstract machine, |Zipper|, we should be able to
recover the input generic tree that is being folded. Crucially, we can embed the
value of the leaf into a larger tree by coercing the type |X| in the leaf to |mu
R|. In a similar fashion as in the previous chapter
(\Cref{sec:expression:wellfounded}), we define a pair of \emph{plugging}
functions that recompute the input tree:

\begin{code}
  plugZ-mudown : (R : Reg) {alg : interpl R interpr X -> X} -> Zipper R X alg -> mu R ->  Set
  plugZ-mudown R ((l , isl) , s) t = plug-mudown R (In (coerce l isl)) s t

  plugZ-muup : (R : Reg) {alg : interpl R interpr X -> X} -> Zipper R X alg -> mu R ->  Set
  plugZ-muup R ((l , isl) , s) t = plug-muup R (In (coerce l isl)) s t
\end{code}

Moreover, to ensure that the configurations preserve the invariant---the input
tree does not change during the evaluation of the tail-recursive catamorphism---we 
define a pair of datatypes indexed by the input tree:
%
\begin{code}
  data Zipperdown (R : Reg) (X : Set) (alg : interpl R interpr X -> X) (t : mu R) : Set where
    _,_ : (z : Zipper R X alg) -> plugZ-mudown R z == t -> Zipperup R X alg t

  data Zipperup (R : Reg) (X : Set) (alg : interpl R interpr X -> X) (t : mu R) : Set where
    _,_ : (z : Zipper R X alg) -> plugZ-muup R z == t -> Zipperup R X alg t 
\end{code}

\section{One step of a catamorphism}
\label{sec:generic:onestep}

%{
%format load = "\AF{load}"
%format unload = "\AF{unload}"
In this section, we show how to define the generic operations that correspond to
the functions |load| and |unload| given in \cref{sec:expression:stage}.
Moreover, we outline the proofs of several properties we later require to show
correctness and termination.
%}
\subsection{Load}

The function |load| traverses the input term to find its leftmost leaf. Any
other subtrees the |load| function encounters are stored on the stack. Once the
|load| function encounters a constructor, without subtrees, it is has found the
desired leaf. Its definition is as follows:\footnote{As in the introduction, we
use a sum type |U+| to align its type with that of |unload|.}
%
\begin{code}
load  : (R : Reg) {alg : interpl R interpr X -> X} -> mu R
      -> Stack R X alg -> Zipper R X alg U+ X
load R (In t) s = first-cps R R t id (lambda l -> inj1 . prodOp l) s
\end{code}

We write |load| by appealing to an auxiliary definition |first-cps|, that uses
continuation passing style (CPS) to keep the definition tail-recursive and
obviously structurally recursive. If we were to try to define |load| by
recursion directly, we would need to find the leftmost subtree and recurse on
it---but this subtree is not syntactically smaller for the termination checker.
The continuations are also necessary for the function |first-cps| to be
tail-recursive; we will come back to this point in our discussion
(\Cref{sec:generic:discussion}).


The type of our |first-cps| function is daunting at first:
%
\begin{code}
first-cps : (R Q : Reg) {alg : interpl Q interpr X -> X}
          ->  interpl R interpr (mu Q)
          ->  (nabla R (Computed Q X alg) (mu Q) -> (nabla Q (Computed Q X alg) (mu Q)))
          ->  (Leaf R X -> Stack Q X alg -> Zipper Q X alg U+ X)
          ->  Stack Q X alg
          ->  Zipper Q X alg U+ X
\end{code}
%
The first two arguments are codes of type |Reg|. The code |Q|
represents the datatype for which we are defining a traversal; the
code |R| is the code on which we pattern match. In the initial call to
|first-cps| these two codes are equal. As we define our function,
we pattern match on |R|, recursing over the codes in (nested) pairs or
sums---yet we still want to remember the original code for our data
type, |Q|.

The next argument of type |interpl R interpr (mu Q)| is the data we
aim to traverse. Note that the `outermost' layer is of type |R|, but
the recursive subtrees are of type |mu Q|. The next two arguments are
two continuations: the first is used to gradually build the
\emph{dissection} of |R|; the second continues on another branch once
one of the leaves have been reached. The last argument of type |Stack
Q X alg| is the current stack.  

We shall fill the definition of |first-cps| by cases.  The clauses for the base
cases are as expected. In |Zero| there is nothing to be done. The |One| and
|K A| codes consist of applying the second continuation to the tree and the \emph{stack}.
%
\begin{code}
  first-cps Zero Q Empty _
  first-cps One  Q x k f s    = f (tt , NonRec-One) s
  first-cps (K A) Q x k f s   = f (x , NonRec-K A x) s
\end{code}
%
The recursive case, constructor |I|, corresponds to the occurrence of a subtree.
The function |first-cps| is recursively called over that subtree with the stack
incremented by a new element that corresponds to the \emph{dissection} of the
functor layer up to that point. The second continuation is replaced with the
initial one:
%
\begin{code}
  first-cps I Q (In x) k f s  = first-cps Q Q x id (lambda z  -> inj1 . prodOp z) (k tt :: s)
\end{code}
%
In the coproduct, both cases are similar, just having to account for the
use of different constructors in the continuations:
%
\begin{code}
  first-cps (R O+ Q) P (inj1 x) k f s = first-cps R P x  (k . inj1) cont s
    where cont (l , isl) = f ((inj1 l) , NonRec-+1 R Q l isl)
  first-cps (R O+ Q) P (inj2 y) k f s = first-cps Q P y  (k . inj2) cont s
    where cont (l , isl) = f ((inj1 l) , NonRec-+2 R Q l isl)
\end{code}
%
The interesting clause is the one that deals with the product. First the
function |first-cps| is recursively called on the left component  of the pair
trying to find a subtree to recurse over. It may be the case that there
are no subtrees at all, thus, it is passed as the first continuation a call to
|first-cps| over the right component of the product.  In case the
continuation fails to to find a subtree, it returns the leaf as-is.
%
\begin{code}
  first-cps (R O* Q) P (r , q) k f s  = first-cps R P r  (k . inj1 . (_, q)) cont s
    where cont (l , isl) = first-cps Q P q (k . inj2 . prodOp (coerce l isl)) cont'
      where cont' (l' , isl') = f (l , l') (NonRec-* R Q l l' isl isl')
\end{code}

Using continuations in the definition of |first-cps| might seem overkill,
however, they are necessary to keep the function tail-recursive. We will
discuss this issue further at the end of the chapter
(\Cref{sec:generic:discussion}).

There is one important property that the function |load| satisfies: it preserves
the input tree. In the previous chapter (\Cref{sec:expression:tailrec}), we proved such property directly by
induction over the stack, however, in the generic case we need a more involved
construction due to the genericity and CPS nature of the auxiliary 
function, |first-cps|. The signature of the property is spelled as follows:

\begin{code}
  load-preserves-plugup  :  forall (R : Reg) {alg : interpl R interpr X -> X} -> (r : mu R) 
                            -> (s : Stack R X alg) -> (z : Zipper R X alg) 
                            -> load R r s ≡ inj1 z 
                            -> ∀ (t : mu R) -> plug-muup R r s == t -> plugZ-muup R z == t
\end{code}

The function |load| directly calls |first-cps|, so proving the above lemma
amounts to show that it holds for |first-cps|. However, from its type
it is not clear what property we need. We start with the
obvious skeleton:
%
\begin{code}
    first-cps-lemma  : (R Q : Reg) {alg : interpl Q interpr X -> X} 
        -> (r : interpl R interpr (mu Q)) 
        -> (k : nabla R (Computed Q X alg) (mu Q) -> nabla Q (Computed Q X alg) (mu Q))
        -> (f : Leaf R X -> List (nabla Q (Computed Q X alg) (mu Q)) -> Zipper Q X alg U+ X)
        -> (s : Stack Q X alg) -> (z : Zipper Q X alg)
        -> first-cps R Q r k f s == inj1 z
        -> forall (t : mu Q)  -> ?? -> plugZ-muup Q z == t
\end{code}
%
Naively, we could try to fill the hole with the type |plug-muup R r s == t|,
however, the recursive subtrees in |r| are of type |mu Q| while the outermost
layer is a functor of a different code |R|; the equality does not typecheck. The
type of the hole, |??|, has to relate both continuations, |f| and |k|, to the
value |r| that is subject to recursion and the stack |s|. 

Given a term of type |interpl R interpr (mu Q)|, for any |R| and |Q|, there are
two possibilities: either the term is a leaf and recursive subtrees do not
occur; or the term can be \emph{dissected} into a context and the subtree that
fits in it. We express this in \Agda~as a
view\citep{wadler1987views,mcbride2004view}:
%
\begin{code}
    view  : (R Q : Reg) -> {alg : interpl Q interpr X -> X} -> (r : interpl R interpr (mu Q))
          ->  (Sigma  (nabla R (Computed Q X alg) (mu Q)) 
                      lambda dr ->  Sigma  (mu Q) 
                                           lambda q -> plug R Computed.Tree (dr , q) == r)
              U+ (Sigma  (interpl R interpr X) 
                         lambda leaf -> (NonRec R leaf * [ R ]-[ mu Q ] r ~[ X ] leaf))
\end{code}
%
The value |r : interpl R interpr (mu Q)| either decomposes into a dissection,
|dr|, and the subtree |q|, such that plugged together recompose to |r|; or there is
a leaf, |leaf|, \textit{equal} to |r|. The variables |r| and |leaf| are not of
the same type, thus, we cannot assert they are equal using propositional
equality. Instead, we need a different notion of equality: heterogeneous
equality. Its definition is as follows:
%
\begin{code}
  data HetEq : (R : Reg)  -> (X : Set) -> interpl R interpr X
                          -> (Y : Set) -> interpl R interpr Y -> Set1 where
    ~-One  : {X : Set} {Y : Set}                    -> [ One  ]-[ X ] tt ~[ Y ] tt
    ~-K    : {A : Set} {a : A} {X : Set} {Y : Set}  -> [ K A ]-[ X ] a  ~[ Y ] a
    ~-I    : {X : Set} {x : X}                      -> [ I ]-[ X ] x ~[ X ] x
    ~-+1   : {R Q : Reg} {X Y : Set} {x : interpl R interpr X} {y : interpl R interpr Y} 
           -> [ R ]-[ X ] x ~[ Y ] y -> [ R O+ Q ]-[ X ] (inj1 x) ~[ Y ] (inj1 y)
    ~-+2   : {R Q : Reg} {X Y : Set} {x : interpl Q interpr X} {y : interpl Q interpr Y} 
           -> [ Q ]-[ X ] x ~[ Y ] y -> [ R O+ Q ]-[ X ] (inj2 x) ~[ Y ] (inj2 y)
    ~-*    : {R Q : Reg} {X Y : Set}  {x1 : interpl R interpr X} {x2 : interpl R interpr Y} 
                                      {y1 : interpl Q interpr X} {y2 : interpl Q interpr Y}  
           -> [ R ]-[ X ] x1 ~[ Y ] x2 -> [ Q ]-[ X ] y1 ~[ Y ] y2 
           -> [ R O* Q ]-[ X ] (x1 , y1) ~[ Y ] (x2 , y2)
\end{code}
%
Two functors with the same code can be interpreted over different types, |X| and
|Y|, as long as the code is not |I|. In that case, constructor |~-I|, both types
must coincide. Heterogeneous equality is an equivalence relation as expected:
%
\begin{code}
  ~-refl    : ∀ {X : Set} {R : Reg} {x} -> [ R ]-[ X ] x ~[ X ] x

  ~-sym     : ∀ {X Y : Set} {R : Reg} {x y} 
            -> [ R ]-[ X ] x ~[ Y ] y -> [ R ]-[ Y ] y ~[ X ] x

  ~-trans   : ∀ {X Y Z : Set} {R : Reg} {x y z} 
            -> [ R ]-[ X ] x ~[ Y ] y -> [ R ]-[ Y ] y ~[ Z ] z -> [ R ]-[ X ] x ~[ Z ] z
\end{code}
%
In the particular case of both types agreeing it turns into plain propositional equality:
%
\begin{code}
  ~-to-== : ∀ {X : Set} {R : Reg} {x y} -> [ R ]-[ X ] x ~[ X ] y -> x == y
\end{code}

Continuing with the lemma |first-cps-lemma|, we apply the view on the
input |r| and for each case define a sensible property:
%
\begin{code}
    Prop  : forall (R Q : Reg) {alg : interpl Q interpr X -> X} 
          -> interpl R interpr (mu Q) 
          -> (nabla R (Computed Q X alg) (mu Q) -> nabla Q (Computed Q X alg) (mu Q))
          -> (Leaf R X -> Stack Q X alg -> Zipper Q X alg U+ X) 
          -> Stack Q X alg -> mu Q -> Set
    Prop {X} R Q r k f s t with view {X} R Q r
    ...  | inj1 (dr , q , _)  
         = Sigma  (interpl Q interpr (mu Q)) 
                  lambda e -> plug Q Computed.Tree (k dr , q) == e * plug-muup Q (In e) s == t
    ...  | inj2 (l , isl , _) with f (l , isl) s
         ... |  inj1 z  = plugZ-muup Q z == t
         ... |  inj2 _  = Bot 
\end{code}
%
When the value can be decomposed into a dissection, |dr|, and a subtree |q|,
there exists a tree |e : mu q|, such that applying the continuation |k| to the
dissection and plugging back |q| results in |e|. Moreover, recursively plugging
|e| to the stack yields |t|. On the other hand, when |r| is a leaf, |l|, we apply the
second continuation |f|, and in case it returns another configuration, |z|, it 
should plug to the tree |t|. 

Using |Prop|, we can complete the type signature of the lemma |first-cps-lemma|.
The proof is done by decomposing the input with |view|, induction on the
code, and using properties of heterogeneous equality.

Other properties about how the function |load| behaves follow the same pattern.
First, state the property for |load| and, subsequently, for |first-cps| using the
|view| to differentiate the possible cases.

\subsection{Unload}

Armed with |load| we turn our attention to |unload|. First of all, it is
necessary to define an auxiliary function, |right|, that given a
\emph{dissection} and a value, of the type of the left variables, either finds
a dissection |Dissection R X Y| or it shows that  there are no occurrences of
the variable left. In the latter case, it returns the functor interpreted over
|X|, | interpl R interpr X|.

\begin{code}
  right  : (R : Reg) -> nabla R X Y -> X -> interpl R interpr X U+ Dissection R X Y
\end{code}

Its definition is simply by induction over the code |R|, with the special case
of the product, |R O* Q|, that needs another ancillary definition to look for the
leftmost occurrence of the variable position within the left component of type 
|interpl R interpr X|.

We define the function |unload| by induction over the \emph{stack}. If the
\emph{stack} is empty the job is done and a final value is returned. In case the
\emph{stack} has at least one \emph{dissection} in its head, the function
|right| is called to check whether there are any more holes left. If there are
none, a recursive call to |unload| is dispatched, otherwise, if there is still a
subtree to be processed the function |load| is called.

\begin{code}
  unload  : (R : Reg) -> (alg : interpl R interpr X -> X)
          -> (t : mu R) -> (x : X) -> catamorphism R alg t == x -> Stack R X alg
          -> Zipper R X alg U+ X
  unload R alg t x eq []        = inj2 x
  unload R alg t x eq (h :: hs) with right R h (t , x , eq)
  ...  | inj1 r with compute R R r
       ... | (rx , rr) , eq'   = unload R alg (In rp) (alg rx) (cong alg eq') hs
  ...  | inj2 (dr , q)         = load R q (dr :: hs)
\end{code}

When the function |right| returns a |inj1| it means that there are not
subtrees left in the \emph{dissection}. If we take a closer look, the type of
the |r| in |inj1 r| is | interpl R interpr (Computed R X alg) |. The functor
|interpl R interpr| is storing at the variable positions both values, subtrees and proofs.

What is needed for the recursive call, however, is: first, the functor
interpreted over values, | interpl R interpr X|, to apply the algebra;
second, the functor interpreted over subtrees, | interpl R interpr (mu R)|, to
use the unevaluated subtree for termination; third, the proof that the
value equals to applying a |catamorphism| over the subtree.  The function
|compute| massages |r| to adapt the arguments for the recursive call to
|unload|:
%
\begin{code}
  compute : (R Q : Reg) {alg : interpl Q interpr X -> X}
      -> interpl R interpr (Computed Q X alg)
      -> Sigma (interpl R interpr X * interpl R interpr (mu Q)) lambda { (r , t) -> mapFold Q alg R t == r }
\end{code}

To conclude, we can prove the expected property that |unload| satisfies: it
preserves the input tree:
%
\begin{code}
  unload-preserves  : forall (R : Reg) {alg : interpl R interpr X -> X}
                    -> (t : mu R) (x : X) (eq : catamorphism R alg t == x) (s : Stack R X alg)
                    -> (z : Zipper R X alg)
                    -> unload R alg t x eq s == inj1 z
                    -> forall  (e : mu R) -> plug-muup R t s == e  -> plugZ-muup R z == e
\end{code}
%
The proof follows directly by induction over the stack.

\section{Relation over generic configurations}
\label{sec:generic:relation}

We can engineer a \emph{well-founded} relation over elements of type |Zipperdown
t|, for some concrete tree |t : mu R|, by explicitly separating the functorial layer
from the recursive layer induced by the fixed point. At the functor level, we
impose the order over \emph{dissection}s of |R|, while at the fixed point level
we define the order by induction over the \emph{stack}s.

To reduce clutter in the definition, we give a non type-indexed
relation over terms of type |Zipper|. We can later use the same technique as in
\cref{sec:expression:wellfounded} to recover a fully type-indexed relation over
elements of type |Zipperdown t| by requiring that the configurations respect the
invariant, |plugZ-mudown z == t|. We define inductively the relation over the
|Stack| part of the configurations as follows:
%
\begin{code}
  data <ZOp : Zipper R X alg -> Zipper R X alg -> Set where
    Step  :  (t1 , s1) <Z (t2 ,  s2) -> (t1 , h :: s1) <Z (t2 , h  :: s2)

    Base  : plugZ-mudown R (t1 , s1) == e1 -> plugZ-mudown R (t2 , s2) == e2
          -> (h1 , e1) <Nabla (h2 , e2) -> (t1 , h1 :: s1) <Z (t2 , h2 :: s2)
\end{code}

This relation has two constructors:

\begin{itemize}
\item The |Step| constructor covers the
inductive case. When the head of both \emph{stacks} is the same, i.e., both
|Zipper|s share the same prefix, it recurses directly
on tail of both stacks.
\item The constructor |Base| accounts for the case
when the head of the \emph{stack}s is different. This means that the paths given
by the configurations denote different subtrees of the same node. In such case, the
relation we are defining relies on an auxiliary relation, |<NablaOp|, that orders
\emph{dissections} of type |Dissection R (Computed R X alg) (mu R)|.
\end{itemize}

We can define this relation on dissections directly; we do not need to consider
the recursivity due to the fixed point. The definition of the relation over
dissections, interpreted on \emph{any} sets |X| and |Y|, is the following:
%
\begin{code}
  data <NablaOp : (R : Reg) -> Dissection R X Y -> Dissection R X Y -> Set where
    step-+1  :   llcorner  R lrcorner      (r , t1)       <Nabla    (r' , t2)
             ->  llcorner R O+ Q lrcorner  (inj1 r , t1)  <Nabla (inj1 r' , t2)

    step-+2  :   llcorner   Q              (q , t2)       <Nabla (q' , t2)
             ->  llcorner R O+ Q lrcorner  (inj2 q , t1)  <Nabla (inj2 q' , t2)

    step-*1  :   llcorner R lrcorner       (dr , t1)             <Nabla (dr' , t2)
             ->  llcorner R O* Q lrcorner  (inj1 (dr , q) , t1)  <Nabla (inj1 (dr' , q) , t2)

    step-*2  :   llcorner Q lrcorner       (dq , t1)             <Nabla (dq' , t2)
             ->  llcorner R O* Q lrcorner  (inj2 (r , dq) , t1)  <Nabla (inj2 (r , dq') , t2)

    base-*   :   llcorner R O* Q lrcorner (inj2 (r , dq) , t1)   <Nabla  (inj1 (dr , q) , t2)
\end{code}
%
The idea is that we order the elements of a \emph{dissection} in a left-to-right
fashion.  All the constructors except for |base-*| simply follow the inductive
structure of the dissection. To define the base case, |base-*|, recall that the
\emph{dissection} of the product of two functors, |R O* Q|, has two possible
values: it is either a term of type |nabla R X Y * interpl Q interpr Y|, such as
|inj1 (dr , q)|; or a term of type |interpl R interpr X * nabla Q X Y| like
|inj2 (r , dq)|. The former denotes a configuration pointing to the left subtree
of the pair while the latter denotes a position in the right subtree.  The
|base-*| constructor states that positions to the right are \textit{smaller}
than those to the left.

This completes the order relation on configurations; we still need to prove our
relation is \emph{well-founded}.  To prove this, we write a type-indexed version
of each relation. The first relation, |<ZOp|, has to be type-indexed by the tree
of type |mu R| to which both \emph{configurations} recursively plug through
|plugZ-mudown|. Likewise, the auxiliary relation on \emph{dissections},
|<NablaOp|, needs to be type-indexed by the functor of type | interpl R interpr
X | to which both \emph{dissections} |plug|:

\begin{code}
  data IxLt  {X Y : Set} {eta : X -> Y} :  (R : Reg) -> (tx : interpl R interpr Y) 
             -> IxDissection R X Y eta tx -> IxDissection R X Y eta tx -> Set where


  data IxLtdown  {X : Set} (R : Reg) {alg : interpl R interpr X -> X}  : (t : mu R) 
                 -> Zipperdown R X alg t -> Zipperdown R X alg t -> Set where
\end{code}

The proof that the first relation is well-founded follows from induction over
the code. Like the proof in the relation for expressions, \cref{subsec:expression:wellfounded}, 
it necessitates several lemmas covering each of the constructors.
Writing an indexed relation is, again, crucial to prove the lemma. Otherwise,
the proof cannot recursively call itself because the inputs are not structurally
related.

The proof of \emph{well-foundedness} of |IxLtdown|, on the other hand, is not as
straightforward. The recursive subtrees occurring in the functor layer are not
directly accessible, thus, recursive calls are rejected by the termination
checker. We tackle this issue in three steps: first, we define a predicate over
functors that states whether a property holds for all the values in variable
positions; second, we use recursion to build the proof that all such values are
well-founded; third, if the property holds, then it also holds for any subtree
resulting from a dissection over the value. The three definitions are as
follows:
%
\begin{code}
  data All {A : Set} (P : A -> Set) : (R : Reg) -> interpl R interpr A -> Set1 where
    ...
\end{code}

\begin{code}
  all-is-WF  :  forall (R Q : Reg) (alg : interpl R interpr X -> X) -> (t : interpl Q interpr (mu R)) 
                -> All (mu R) (lambda r -> Well-founded (llcorner R lrcornerllcorner r lrcornerIxLtdown)) Q t
\end{code}

\begin{code}
  all-to-plug :  forall {X : Set}  {R Q : Reg} {eta : X -> mu Q} {P : mu Q -> Set}
                 -> (t : interpl R interpr (mu Q)) -> All (mu Q) P R t 
                 -> forall (r : mu Q) (dr : nabla R X (mu Q)) -> plug R eta (dr , r) == t -> P r
\end{code}
%
The predicate, |All|, is defined by induction over the code.  In the particular
case of the constructor |I|, we require a proof that the predicate holds for the
concrete value of the type variable. Both lemmas, |all-is-WF| and |all-to-plug|,
follow directly by induction over the code. 

The full proof that the relation is well-founded can be found in the
accompanying code. Here we only spell its signature:
%
\begin{code}
  <Z-WF : (R : Reg)  -> (t : mu R) -> Well-founded (llcorner R lrcornerllcorner t lrcornerIxLtdown)
\end{code}

\section{A generic tail-recursive machine}
\label{sec:generic:machine}

Finally, we are ready to define a generic tail-recursive machine. To do so we
assemble the generic machinery we have developed so far, following the same
outline as in \cref{sec:expression:tailrec}.

The first point is to write a wrapper around the function |unload| that performs
one step of the \emph{catamorphism}:
%
\begin{code}
  step  : (R : Reg) -> (alg : interpl R interpr X -> X)
        -> Zipper R X alg -> Zipper R X alg U+ X
  step R alg ((x , nr-x) , s) = unload R alg (In (coerce x nr-x)) (alg x) (...) s
\end{code}
%
The function |step| performs a call to |unload|, coercing the leaf of type
|interpl R interpr X| in the |Zipperdown| argument to a generic tree of type
|interpl R interpr (mu R)|. Moreover, it supplies a proof, here omitted with
elipsis, stating that applying the catamorphism over a \emph{coerced} leaf is the
same as directly evaluating the algebra on the leaf, |alg x|. Next, we define a
type-indexed step function that statically enforces the configurations, both in its
argument and in its result, to be states of the catamorphism over the same generic tree:
%
\begin{code}
  stepIx  : (R : Reg) -> (alg : interpl R interpr X -> X) -> (t : mu R)
          -> Zipperup R X alg t -> Zipperup R X alg t U+ X
  stepIx R alg t (z , s) with step R alg (z , s) | inspect (step R alg) (z , s)
    ... | inj1 z |  [ Is ]  = inj1 (z , unload-preserves ... z t Is ...)
    ... | inj2 x |  _       = inj2 x
\end{code}

The key ingredient of our construction consists of proving that the function
|stepIx| delivers a smaller configuration, by |IxLtdown|, each time the function
is called. The required lemma has the following signature:
%
\begin{code}
  step-<  : forall (R : Reg) (alg : interpl R interpr X -> X) -> (t : mu R)
          -> (z1 : Zipperup R X alg t)
          ->  forall (z2 : Zipperup R X alg t)
              -> stepIx R alg t z1 == inj1 z2 
              -> llcorner R lrcornerllcorner t lrcorner (Zipperup-to-Zipperdown z2) <Z (Zipperup-to-Zipperdown z1)
\end{code}

As the function |step| is a wrapper over |unload| (\Cref{sec:generic:onestep}),
it suffices to prove a similar property for such function.  The function
|unload| does two things: first, it calls the function |right| to check whether
the \emph{dissection} has any more recursive subtrees to the right, which still
have to be processed; second, it dispatches to either |load|, if there is a
subtree left, or recurses over the stack otherwise.  In the former circumstance,
a new \emph{dissection} is returned by |right|.  Proving that the new
configuration is smaller, amounts to showing that the returned \emph{dissection} is
smaller by |<NablaOp|. The lemma states:

\begin{code}
  right-<  : forall  (R : Reg) (t : mu R) (x : X) (eq : cata R alg t == x)
                     (dr  : nabla (Computed R X alg) (mu R)) 
            -> (t' : mu R) (dr' : nabla (Computed R X alg) (mu R)) 
            -> right R dr (t , x , eq) == inj2 (dr' , t') -> llcorner R lrcorner (dr' , t') <Nabla (dr , t) 
\end{code}
%
The proof of this lemma follows  by induction over the code. 

Extending this result to show that the function |unload| delivers a smaller
value is straightforward. By induction over the input stack we check if the
traversal is done or not. If it is not yet done, there is at least one
dissection in the top of the stack.  The function |right| applied to that
element returns either a smaller dissection or a tree with all values on the
leaves. If we obtain a new dissection, we use the |right-<| lemma; in the latter
case, we continue by induction over the stack. 

Finally, we can write the \emph{tail-recursive machine}, |tail-rec-cata|, as the
combination of an auxiliary recursor over the accessibility predicate and a top-level
function that initiates the computation with suitable arguments:
%
\begin{code}
  rec  : (R : Reg) (alg : interpl R interpr X -> X) (t : mu R) 
       -> (z : Zipperup R X alg t) 
       -> Acc (llcorner R lrcornerllcorner t lrcornerIxLtdown ) (Zipperup-to-Zipperdown z) -> X
  rec R alg t z (acc rs) with step R alg t z | inspect (step R alg t) z
  ... | inj1 z'  |  [ Is  ] = rec R alg t z' (rs   (Zipperup-to-Zipperdown z') 
                                                   (step-< R alg t z z' Is))
  ... | inj2 x   |  [ _   ] = x
\end{code}
%
\begin{code}
  tail-rec-cata : (R : Reg) -> (alg : interpl R interpr X -> X) -> mu R -> X
  tail-rec-cata R alg x  with load R alg x []
  ... | inj1 z = rec R alg (z , ...) (<Z-WF R z)
\end{code}

\section{Correctness}
\label{sec:generic:correct}
%{
%format tail-rec-eval = "\AF{tail-rec-eval}"
The proof that our tail-recursive function produces the same output as the
catamorphism is uncomplicated. The function |step| is type-indexed by the input
generic tree which remains constant across invocations, thus, the result of the
catamorphism does so as well. As we did in the |tail-rec-eval| evaluator,
\cref{sec:expression:correctness}, we use an ancillary definition indicating that
when the result of |stepIx| is an |inj2|, the final value, then it equates
to applying the catamorphism to the input:
%
\begin{code}
  stepIx-correct  :  forall (R : Reg) (alg : interpl R interpr X -> X) (t : mu R) 
                  -> (z : Zipperup R X alg t)
                     -> forall (x : X) -> stepIx R alg t z ≡ inj2 x -> catamorphism R alg t == x
\end{code}
%
Recall that |stepIx| is a wrapper around |unload|, hence it suffices to prove
the following lemma:
%
\begin{code}
  unload-correct  : forall  (R : Reg) (alg : interpl R interpr X -> X)
                            (t : mu R) (x : X) (eq : catamorphism R alg t == x)
                            (s : Stack R X alg) (y : X)  
                  -> unload R alg t x eq s == inj2 y
                  -> ∀ (e : mu R) -> plug-muup R t s == e -> catamorphism R alg e == y
\end{code}

The correctness of our generic tail-recursive function is an immediate consequence of
the above lemmas:
\begin{code}
  correctness  : forall (R : Reg) (alg : interpl R interpr X -> X) (t : mu R)
               -> catamorphism R alg t == tail-rec-cata R alg t
\end{code}

\section{Examples}
\label{sec:generic:example}

To conclude the construction of the generic tail-recursive evaluator, we show
how to use the generic machinery to implement two tail-recursive evaluators: one
for the type of |Expr| from the previous chapter (\Cref{chap:expression}); and
another for a problem dubbed "the balancer of Calder mobiles" by
~\cite{Danvy_2004}. By doing so, we demonstrate how we get a
correct-by-construction tail-recursive machine almost for free.

\paragraph{Expressions}

First, we remind the \emph{pattern} functor underlying the type |Expr|:
%
\begin{code}
  expr : Reg
  expr = K Nat O+ (I O* I)
\end{code}
%
The type |Expr| type is isomorphic to tying the knot over |expr|:
%
\begin{code}
  ExprG : Set
  ExprG = mu expr
\end{code}
%
The function |eval| is equivalent to instantiating the \emph{catamorphism} with
an appropriate algebra:
%
\begin{code}
  phinat : expr Nat -> Nat
  phinat (inj1 n)          = n
  phinat (inj2 (e1 , e2))  = e1 + e2

  eval : ExprG -> Nat
  eval = cata expr phinat
\end{code}
%
Finally, we can define a tail-recursive machine \emph{equivalent} to the one we
derived in \cref{sec:expression:tailrec}, |tail-rec-eval|:
%
\begin{code}
  tail-rec-evalG : ExprG -> Nat
  tail-rec-evalG = tail-rec-cata expr phinat
\end{code}

\paragraph{Calder mobiles}

We define a Calder mobile inductively as an object of a certain weight or a bar
of a certain weight and two sub-mobiles:
%
\begin{code}
  data Mobile : Set where
    OBJ : Nat -> Mobile
    BAR : Nat -> Mobile -> Mobile -> Mobile 
\end{code}
%
For instance, |mob1| and |mob2| are two |Mobile|s:
\begin{code}
  mob1 : Mobile
  mob1 = BAR 1  (BAR 1  (OBJ 2) 
                        (OBJ 2)) 
                (OBJ 5)

  mob2 : Mobile
  mob2 = BAR 1  (OBJ 6) 
                (BAR 1  (OBJ 2) 
                        (OBJ 9))
\end{code}
%
The weight of a |Mobile| is the sum of the weight of its objects and its bars.
The following function computes recursively the weight of a |Mobile|:
%
\begin{code}
  weight : Mobile -> Nat
  weight (OBJ n)        = n
  weight (BAR n m1 m2)  = n + weight m1 + weight m2
\end{code}
%
For example, the |weight| of |mob1| is 11 and the |weight| of |mob2| is 19:
%
\begin{code}
  prop1 : weight mob1 == 11
  prop1 = refl

  prop2  : weight mob2 == 19
  prop2 = refl
\end{code}

A |Mobile| is in equilibrium if it is an |OBJ|, or if it is a |BAR| and its
sub-mobiles are of the same weight and also in equilibrium. The following
function determines whether a |Mobile| is in equilibrium:
%
\begin{code}
  equilibrium : Mobile -> Bool
  equilibrium (OBJ _)        = true
  equilibrium (BAR _ m1 m2)  = weight m1 =Nat weight m2 and equilibrium m1 and equilibrium m2
\end{code}

This solution is highly inefficient because it repeatedly traverses the
|Mobile|s to compute the weight and the equilibrium. In order to reduce the
number of traversals we can fuse together the weight and the equilibrium. We use
an auxiliary function that returns a |Maybe Nat| indicating whether the |Mobile|
is in equilibrium, and in the positive case, its weight:
%
\begin{code}
  equilibrium : Mobile → Bool
  equilibrium m = is-just (go m)
    where  go : Mobile -> Maybe Nat
           go (OBJ n)        = just n
           go (BAR n m1 m2)  =  
             case (go m1) of lambda
               { nothing    -> nothing
               ; (just n1)  -> case (go m2) of lambda
                                 {  nothing   -> nothing
                                 ; (just n2)  -> if n1 =Nat n2  then just (n + (n1 + n2)) 
                                                                else nothing 
                                 } 
               }
\end{code}

The definition of |equilibrium| is rather involved. In the definition of |go|,
we mix together the recursive calls with the logic of combining their results.
Moreover, the function |go| is not tail-recursive and its transformation into
one requires a lot of---manual and error-prone---work. Instead we can use
generic programming to derive a direct solution that by using our construction
is tail-recursive for free.

First, let us express the representation of the type |Mobile| in the regular
universe:
%
\begin{code}
  MobileF : Reg
  MobileF = K Nat O+ (K ℕ O* I O* I)
  
  MobileG : Set
  MobileG = mu MobileF
\end{code}
%
And the embedding from |Mobile| into its generic representation:
%
\begin{code}
  from : Mobile → MobileG
  from (OBJ n)        = In (inj1 n)
  from (BAR n m1 m2)  = In (inj2 (n , from m1 , from m2))
\end{code}  

Now, we can define a much more efficient solution in terms of performance and
code size using the generic tail-recursive evaluator. First and foremost, we
define an algebra of the functor |MobileF| interpreted over |Maybe Nat|. A |just
n| denotes that the |Mobile| is in equilibrium and has weight |n|, while
|nothing| means the |Mobile| is not in equilibrium. Its definition is as
follows:
%
\begin{code}
  phimob : interpl MobileF interpr (Maybe Nat) -> Maybe Nat
  phimob (inj1 n)                        = just n
  phimob (inj2 (n , just m1 , just m2))  = if m1 =Nat m2  then  just (n + m1 + m2) 
                                                          else  nothing
  phimob (inj2 (_ , _ , _))              = nothing
\end{code}

We define the tail-recursive function that traverses each |Mobile| only once
using the generic tail-recursive evaluator, |tail-rec-cata|:
%
\begin{code}
  equilibriumG : Mobile → Bool
  equilibriumG = is-just . tail-rec-cata MobileF phimob . from
\end{code}

Using the generic equilibrium function, we show that |mob1| is in
equilibrium, but |mob2| is not:
%
\begin{code}
  prop3 : equilibriumG mob1 == true
  prop3 = refl

  prop4 : equilibriumG mob2 == false
  prop4 = refl
\end{code}

There is still an inefficiency in the code. In case the left sub-mobile is not
in equilibrium, it is not necessary to check whether the right is in equilibrium
or not. Danvy~\citeyearpar{Danvy_2004} proposes to either use exceptions (in
\emph{ML}) or transform the evaluator to continuation passing style to
overcome this inefficiency. 

Unfortunately, the |tail-rec-cata| function has to traverse the full |Mobile|
term to obtain an answer: we cannot short-circuit the catamorphism at any point
using the algebra.

\section{Discussion}
\label{sec:generic:discussion}

In this \namecref{chap:generic}, we have explained how to derive a generic
machine that computes the catamorphism of any algebra over any regular datatype.
Adhering to the steps we followed in the construction of the tail-recursive
evaluator for the |Expr| datatype, \cref{chap:expression}, we derived an
abstract machine that we proved to be both terminating and correct. Before
concluding the chapter there are some open questions that are worth discussing:

\paragraph{Choice of universe} The generic tail-recursive machine that we
implemented in this chapter works over a rather limited universe. The motivation
behind this choice was practical: the universe is expressive enough to implement
many simple algebraic datatypes, but, is sufficiently simple to to transport
`directly' the ideas from the concrete example, |Expr| type, to the generic
setting.

Nevertheless, our work is generalizable to other universes. The landmark
of every approach to generic programming is to show that is possible to define
Huet's notion of \emph{zipper} generically.  Because dissections are a
generalization of zippers, the steps we follow to construct our generic
tail-recursive machine can be taken as a guide to implement terminating and
correct-by-construction tail-recursive machines for those universes.

\paragraph{The function |load| written in continuation passing style} The
function |load|, as we defined it in \cref{sec:generic:onestep}, uses the
ancillary function |first-cps| to look for the leftmost leaf in the input tree.
Such function is defined in continuation passing style, which makes its
definition looks overly complicated. However, it is necessary to keep the
machine tail-recursive. 

The function is defined by induction over the code. When the code is a product
of codes, |R O* Q|, the input tree has the shape of |(x , y)| for some |x :
interpl R interpr (mu (R O* Q))| and |y : interpl Q interpr (mu (R O* Q))|.
There are three possible situations: the value |x| is not a leaf, |x| is a leaf
but |y| is not, or |x| and |y| are leaves and the product is a leaf itself. In
the first case, it is necessary to perform recursion over |x|, while storing |y|
on the stack; in the second case, the recursion is on the right component, |y|,
saving |x| on the stack; and in the last case, there is no recursion involved and 
the leaf |(x , y)| is immediately returned. The problem is that checking whether 
|x| or |y| are leaves requires already to perform recursion over them. If the function
|first-cps| was to wait until the result of the recursive call is available to
decide which case is met, the function would not be tail-recursive anymore.

%{
%format load = "\AF{load}"
For specific datatypes, we learn by pattern matching whether the constructor has
recursive subtrees or not. In the former case, we call the |load| function over
the leftmost subtree and save the rest of the node on the stack. For regular
datatypes, however, pattern matching on the code does not reveal enough
information about the term to decide if it has recursive occurrences or not; it
is necessary to traverse the full term to gain such information.
%}

\paragraph{Irrelevance} The generic tail-recursive machine should not have extra
runtime impact due to termination and correctness proofs. The inclusion of
subtrees and proofs along with |Computed| values in the stack indeed incur
memory overhead during execution. We could use \emph{again} computational
irrelevance to identify the parts of the stack not needed during runtime so they
are automatically removed. However, it is not clear how to do so in Agda due the
narrowness of irrelevance as we previously discussed in
\cref{sec:expression:discuss}.
