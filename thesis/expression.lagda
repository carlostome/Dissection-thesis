%include polycode.fmt
%include expression.fmt

\chapter{Verified tail-recursive fold for Expr}
\label{sec:basics}

 Before tackling the generic case, we will present the termination
 and correctness proof for the tail-recursive evaluator presented in
 the introduction in some detail.

  The problematic call for Agda's termination checker is the last clause of the
  |unload| function, that calls |load| on the expression stored on the top of the
  stack. From the definition of |load|, it is clear that we only ever push
  subtrees of the input on the stack. However, the termination checker has no
  reason to believe that the expression at the top of the stack is structurally
  smaller in any way. Indeed, if we were to redefine |load| as follows:
  \begin{code}
      load (Add e1 e2)  stk = load e1 (Left (f e2) stk)
  \end{code}
  we might use some function |f : Expr -> Expr| to push \emph{arbitrary}
  expressions on the stack, potentially leading to non-termination.

  The functions |load| and |unload| use the stack to store subtrees and partial
  results while folding the input expression. Thus, every node in the original
  tree is visited twice during the execution: first when the function |load|
  traverses the tree, until it finds the leftmost leaf; second when |unload|
  inspects the stack in searching of an unevaluated subtree. This process is
  depicted in \Cref{fig:load-unload}.

 \begin{figure}
   % \input{figures/figure1}
   \caption{Traversing a tree with {\color{blue}load} and {\color{red}unload}}
   \label{fig:load-unload}
 \end{figure}

As there are finitely many nodes on a tree, the depicted traversal
using |load| and |unload| must terminate -- but how can we convince
Agda's termination checker of this?

As a first approximation, we revise the definitions of |load| and
|unload|. Rather than consuming the entire input in one go with a pair
of mutually recursive functions, we rewrite them to compute one `step' of the
fold.

The function |unload| is defined by recursion over the stack as before, but with
one crucial difference. Instead of always returning the final result, it may
also\footnote{|U+| is Agda's type of disjoint union.} return a new configuration
of our abstract machine, that is, a pair |Nat * Stack|:
\begin{code}
  unload : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload v   Top             = inj2 v
  unload v   (Right v' stk)  = unload (v' + v) stk
  unload v   (Left r stk)    = load r (Right v stk)
\end{code}

The other key difference arises in the definition of |load|:
\begin{code}
  load : Expr -> Stack -> (Nat * Stack) U+ Nat
  load (Val n)      stk = inj1 (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)
\end{code}
Rather than calling |unload| upon reaching a value, it returns the current stack
and the value of the leftmost leaf. Even though the function never returns an
|inj2|, its type is aligned with the type of |unload| so the definition of both
functions resembles an an abstract machine more closely.

Both these functions are now accepted by Agda's termination checker as
they are clearly structurally recursive. We can use both these functions 
to define the following evaluator %\footnote{We ignore |load|'s impossible case, it
%can always be discharged with \hbox{|bot-elim : forall {X : Set} -> Bot -> X|}.}:
%{
%format nrec   = "\nonterm{" rec "}"
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e with load e Top
  ... | inj1 (n , stk)  = rec (n , stk)
    where
      nrec : (Nat * Stack) -> Nat
      rec (n , stk) with unload n stk
      ... | inj1 (n' , stk' )  = nrec (n' , stk')
      ... | inj2 r             = r
\end{code}
%}
Here we use |load| to compute the initial configuration of our machine
-- that is, it finds the leftmost leaf in our initial expression and its associated stack.
We proceed by
repeatedly calling |unload| until it returns a value.  This version of
our evaluator, however, does not pass the termination checker. The new
state, |(n' , stk')|, is not structurally smaller than the initial
state |(n , stk)|. If we work under the assumption that we have a
relation between the states |Nat * Stack| that decreases after every
call to |unload| and a proof that the relation is well-founded -- we know
this function will terminate eventually.
We now define the following version of the tail-recursive evaluator:
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e with load e Top
  ... | inj1 (n , stk)  = rec (n , stk) ??1
    where
      rec : (c : Nat * Stack) -> Acc ltOp c -> Nat
      rec (n , stk) (acc rs) with unload n stk
      ... | inj1 (n' , stk')  = rec (n' , stk') (rs ??2)
      ... | inj2 r            = r
\end{code}
To complete this definition, we still need to define a suitable
relation |ltOp| between configurations of type |Nat *
Stack|, prove the relation to be well-founded (|??1 : Acc ltOp (n , stk)|)
and show that the calls to |unload| produce `smaller'
states (|??2 : (n' , stk') < (n , stk)|).
In the next section, we will define such a relation and prove it is
well-founded.

\subsection{Well-founded tree traversals}
\label{sec:wf-example}
The type of configurations of our abstract machine can be seen as a variation
of Huet's \emph{zippers}~\citeyearpar{huet}. The zipper associated
with an expression |e : Expr| is pair of a (sub)expression of |e| and
its \emph{context}. As demonstrated by~\citet{dissection}, the zippers
can be generalized further to \emph{dissections}, where the values to
the left and right of the current subtree may have different types. It
is precisely this observation that we will exploit when considering
the generic tail-recursive traversals in the later sections; for now,
however, we will only rely on the intuition that the configurations of
our abstract machine, given by the type |Nat * Stack|, are an instance
of \emph{dissections}, corresponding to a partially evaluated
expression:
\begin{code}
  ZipperType : Set
  ZipperType = Nat * Stack
\end{code}
These configurations, are more restrictive than dissections in
general. In particular, the configurations presented in the previous
section \emph{only} ever denote a \emph{leaf} in the input expression.

The tail-recursive evaluator, |tail-rec-eval| processes the leaves of the input
expression in a left-to-right fashion. The leftmost leaf -- that is the first
leaf found after the initial call to |load| -- is the greatest element; the
rightmost leaf is the smallest. In our example expression from
\Cref{sec:intro}, we would number the leaves as follows:

\begin{figure}[ht]
  % \input{figures/figure2}
  \caption{Numbered leaves of the tree}
  \label{fig:numbered}
\end{figure}

This section aims to formalize the relation that orders elements of
the |ZipperType| type (that is, the configurations of the abstract machine) and
prove it is \emph{well-founded}. However, before doing so there are
two central problems with our choice of |ZipperType| datatype:

\begin{enumerate}
\item The |ZipperType| datatype is too liberal. As we evaluate our input expression
  the configuration of our abstract machine changes constantly, but satisfies
  one important \emph{invariant}: each configuration is a decomposition of the
  original input. Unless this invariant is captured, we will be hard pressed
  to prove the well-foundedness of any relation defined on configurations.

\item The choice of the |Stack| datatype, as a path from the leaf to the
  root is convenient to define the tail-recursive machine, but impractical
  when defining the coveted order relation. The top of a stack stores information about
    neighbouring nodes, but to compare two leaves we need \emph{global} information
    about their positions relative to the root.
\end{enumerate}

We will now address these limitations one by one. Firstly, by refining
the type of |ZipperType|, we will show how to capture the desired
invariant (\Cref{subsec:stack}). Secondly, we
explore a different representation of stacks, as paths from the root, that facilitates
the definition of the desired order relation (\Cref{subsec:topdown}).
Finally we will define the relation over configurations,
\Cref{subsec:relation}, and sketch the proof that it is well-founded.

\subsection{Invariant preserving configurations}
\label{subsec:stack}

A value of type |ZipperType| denotes a leaf in our input expression. In the
previous example, the following |ZipperType| corresponds to the third leaf:

\begin{figure}[ht]
  % \input{figures/figure3}
  \caption{Example: \emph{Configuration} of leaf number 3}
  \label{fig:examplezipper}
\end{figure}

As we observed previously, we would like to refine the type |ZipperType| to
capture the invariant that execution preserves: every |ZipperType| denotes a
unique leaf in our input expression, or equivalently, a state of the abstract
machine that computes the fold.
There is one problem still: the |Stack| datatype stores the values of the subtrees that have
been evaluated, but does not store the subtrees themselves.
In the example in \Cref{fig:examplezipper}, 
when the traversal has reached the third leaf, all the
subexpressions to its left have been evaluated.

In order to record the necessary information, we redefine the |Stack| type as follows:
\begin{code}
  data Stack2 : Set where
    Left   : Expr -> Stack2 -> Stack2
    Right  : (n : Nat) -> (e : Expr) -> eval e == n -> Stack2 -> Stack2
    Top    : Stack2
\end{code}
The |Right| constructor now not only stores the value |n|, but also
records the subexpression |e| and the proof that |e| evaluates to
|n|. Although we are modifying the definition of the |Stack| data
type, we claim that the expression |e| and equality are not necessary
at run-time, but only required for the proof of well-foundedness -- a
point we will return to in our discussion (\Cref{sec:discussion}).
From now onwards, the type |ZipperType| uses |Stack2| as its right 
component:
\begin{code}
ZipperType = Nat * Stack2
\end{code}

A value of type |ZipperType| contains enough information to recover the input
expression. This is analogous to the |plug| operation on zippers:
\begin{code}
  plugup : Expr -> Stack2 -> Expr
  plugup e Top                    = e
  plugup e (Left t       :: stk)  = plugup (Add e t) stk
  plugup e (Right _ t _  :: stk)  = plugup (Add t e) stk

  plugZup : ZipperType -> Expr
  plugZup (n , stk) = plugup (Val n) stk
\end{code}

Any two terms of type |ZipperType| may still represent states of a fold over two
entirely different expressions. As we aim to define an order relation comparing
configurations during the fold of the input expression, we need to ensure that
we only ever compare configurations within the same expression. We
can \emph{statically} enforce such requirement by defining a new wrapper data
type over |ZipperType| that records the original input expression:

\begin{code}
  data Zipperup (e : Expr) : Set where
    prodOp : (z : ZipperType) -> plugZup z == e -> Zipperup e
\end{code}

For a given expression |e : Expr|, any two terms of type |Zipperup e| are
configurations of the same abstract machine during the tail-recursive fold over
the expression |e|.

\subsection{Up and down configurations}
\label{subsec:topdown}

Next, we would like to formalize the left-to-right order on the configurations
of our abstract machine.
The |Stack| in the |ZipperType| represents a path upwards, from the leaf to the
root of the input expression.
This is useful when navigating to neighbouring nodes, but makes it harder
to compare the relative positions of two configurations.
We now consider the value of |ZipperType| corresponding to
leaves with numbers 3 and 4 in our running example:

\begin{figure}[ht]
  % \input{figures/figure4}
  \caption{Comparison of \emph{configurations} for leaves 3 and 4}
  \label{fig:comparison}
\end{figure}

The natural way to define the desired order relation is by induction over the
|Stack|.  However, there is a problem. The first element of both stacks does not
provide us with sufficient information to decide which position is `smaller.'
The top of the stack only stores information about the location of the leaf with
respect to its \emph{parent} node. This kind of \emph{local} information cannot be
used to decide which one of the leaves is located in a position further to the
right in the original input expression.

Instead, we would like to compare the \emph{last} elements of both
stacks.  The common suffix of the stacks shows that both positions are
in the left subtree of the root. Once these paths -- read from right
to left -- diverge, we have found the exact node |Add| where one of the
positions is in the left subtree and the other in the right.

When comparing two |Stack|s, we therefore want to consider them as
paths \emph{from the root}. Fortunately, this observation does not
require us to change our definition of the |Stack| type; instead, we
can define a variant of the |plugup| function that interprets our
contexts top-down rather than bottom-up:
\begin{code}
  plugdown : Expr -> Stack2 -> Expr
  plugdown e Top                    = e
  plugdown e (Left t       :: stk)  = Add (plugdown e stk) t
  plugdown e (Right _ t _  :: stk)  = Add t (plugdown e stk)

  plugZdown : ZipperType -> Expr
  plugZdown (n , stk) = plugdown (Val n) stk
\end{code}
We can convert freely between these two interpretations by reversing
the stack. Furthermore, this conversion satisfies the
|plugdown-to-plugup| property, relating the two variants of plug:

\begin{code}
  convert : ZipperType -> ZipperType
  convert (n , s) = (n , reverse s)

  plugdown-to-plugup  : forall (z : ZipperType)
                      → plugZdown z ==  plugZup (convert z)
\end{code}
As before, we can create a wrapper around |ZipperType| that enforces
that our |ZipperType| denotes a leaf in the input expression |e|:
\begin{code}
  data Zipperdown (e : Expr) : Set where
    prodOp : (z : ZipperType) -> plugZdown z == e -> Zipperdown e
\end{code}
As a corollary of the |plugdown-to-plugup| property, we can define a
pair of functions to switch between |Zipperup| and |Zipperdown|:

\begin{code}
 Zipperdown-to-Zipperup : (e : Expr) → Zipperdown e -> Zipperup e

 Zipperup-to-Zipperdown : (e : Expr) -> Zipperup e -> Zipperdown e
\end{code}

\subsection{Ordering configurations}
\label{subsec:relation}

Finally, we can define the ordering relation over values of type
|Zipperdown|. Even if the |Zipperup| is still used during execution of our
tail-recursive evaluator, the |Zipperdown| type will be used to prove
its termination.

The |IxLtOp| type defined below relates two configurations of type
|Zipperdown e|, that is, two states of the abstract machine evaluating
the input expression |e|:
\begin{code}
  data IxLtOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set where
    <-StepR  : llcorner r lrcorner (t1 , s1) < (t2 , s2)
             ->  llcorner Add l r lrcorner (t1 , Right l n eq :: s1) < (t2 , Right l n eq :: s2)
    <-StepL  : llcorner l lrcorner (t1 , s1) < (t2 , s2)
             ->  llcorner Add l r lrcorner (t1 , Left r :: s1)       < (t2 , Left r :: s2)

    <-Base  :   (e1 == plugZdown t2 s2) ->  (e2 == plugZdown t1 s1)
            ->  llcorner Add e1 e2 lrcorner (t1 , Right n e1 eq :: s1) < (t2 , Left e2 :: s2)
\end{code}
Despite the apparent complexity, the relation is straightforward.
The constructors |<-StepR| and |<-StepL| cover the inductive cases, consuming
the shared path from the root. When the paths diverge, the |<-Base| constructor
states that the positions in the right subtree are `smaller than' those in the
left subtree.

Now we turn into showing that the relation is \emph{well-founded}. We sketch the
proof below:
\begin{code}
    <-WF : forall (e : Expr) -> Well-founded (llcorner e lrcornerLtOp)
    <-WF e x = acc (aux e x)
          where
            aux : forall (e : Expr)  (x y : Zipperdown e)
                → llcorner e lrcorner y < x → Acc (llcorner e lrcornerLtOp) y
            aux = ...
\end{code}
The proof follows the standard schema\footnote{Most well-founded proofs in Agda standard
library follow this pattern.} of most proofs of well-foundedness. It
uses an auxiliary function, |aux|, that proves every configuration smaller than
|x| is accessible.

The proof proceeds initially by induction over our relation. The inductive
cases, corresponding to the |<-StepR| and |<-StepL| constructors, recurse on the
relation. In the base case, |<-Base|, we cannot recurse further on the relation.
We then proceed by recursing over the original expression |e|; without the type
index, the subexpressions to the left |e1| and right |e2| are not syntactically
related thus a recursive call is not possible. This step in the proof relies on
only comparing configurations arising from traversing the same initial
expression |e|.

\subsection{A terminating and correct tail-recursive evaluator}
\label{sec:basic-assembling}

We now have almost all the definitions in place to revise our tail-recursive
fold, |tail-rec-eval|. However, we are missing one essential ingredient: we still
need to show that the configuration decreases after a call to the |unload|
function.

Unfortunately, the function |unload| and the relation that we have
defined work on `different' versions of the |Stack|: the relation
compares stacks top-down; the |unload| function manipulates stacks
bottom-up. Furthermore, the function |unload| as defined previously
manipulates elements of the |ZipperType| type directly, with no further type-level
constraints relating these to the original input expression.

In the remainder of this section, we will reconcile these differences, complete
the definition of our tail-recursive evaluator and finally prove its
correctness.

\paragraph{Decreasing recursive calls}

To define our tail-recursive evaluator, we will begin by defining an
auxiliary |step| function that performs a single step of
computation. We will define the desired evaluator by iterating the
|step| function, proving that it decreases in each iteration.

The |step| function calls |unload| to produce a new configuration, if
it exists.  If the |unload| function returns a natural number, |inj2
v|, the entire input tree has been processed and the function
terminates:
\begin{code}
  step : (e : Expr) -> Zipperup e -> Zipperup e U+ Nat
  step e ((n , stk) , eq)
    with unload (Val n) n refl 
    ... | inj1 (n' , stk')  = ((n' , stk' ) , ...)
    ... | inj2 v            = inj2 v
\end{code}
We have omitted the second component of the result returned in the
first branch, corresponding to a proof that |plugZup (n' , stk') ==
e|. The crucial lemma that we need to show to complete this proof,
demonstrates that the |unload| function respects our invariant:
\begin{code}
  unload-preserves-plugup  :
    forall (e : Expr) (x : Nat) (eq : eval e == x) (s : Stack2) (z' : ZipperType)
    -> unload e x eq s == inj1 z'
    -> forall (t : Expr) -> plugup e s == t -> plugZup z' == t
\end{code}

Finally, we can define the theorem stating that the |step| function always
returns a smaller configuration.

\begin{code}
  step-<  : forall (e : Expr) -> (z z' : Zipperup e) -> step e z == inj1 z'
          -> llcorner e lrcorner Zipperup-to-Zipperdown z' < Zipperup-to-Zipperdown z
\end{code}

Proving this statement directly is tedious, as there are many cases to
cover and the expression |e| occurring in the types makes it difficult
to identify and prove lemmas covering the individual cases. Therefore,
we instead define another relation over our configurations directly,
and prove that there is an injection between both relations under
suitable assumptions:

\begin{code}
  data LtOp :  ZipperType -> ZipperType -> Set where
    ...

  to  :  (e : Expr) (z1 z2 : ZipperType)
      -> (eq1 : plugZdown z1 == e) (eq2 : plugZdown z2 == e)
      -> z1 < z2 -> llcorner e lrcorner (z1 , eq1) < (z2 , eq2)
\end{code}

Thus to complete the previous theorem, it is sufficient to show that the function
|unload| delivers a smaller |ZipperType|:

\begin{code}
  unload-<  : forall (n : Nat) (s : Stack2) (e : Expr) (s' : Stack2)
            -> unload (Val n) n refl s == inj1 (t' , s')
            -> (t' , reverse s') ltOp (n , reverse s)
\end{code}
The proof is done by induction over the stack supported; the complete
proof requires some bookkeeping, covering around 200 lines of code,
but is conceptually not complicated.

The function |tail-rec-eval| is now completed as follows\footnote{|inspect| is
an Agda idiom needed to remember that |z'| is the result of the call |step e z|.}:
\begin{code}
  rec  : (e : Expr) -> (z : Zipperup e)
       -> Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z) -> Zipperup e U+ Nat
  rec e z (acc rs) = with step e z | inspect (step e) z
  ...  | inj2 n  | _       = inj2 n
  ...  | inj1 z' | [ Is ]
       = rec e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is)

  tail-rec-eval : Expr -> Nat
  tail-rec-eval e with load e Top
  ... | inj1 z = rec e (z , ...) (<-WF e z)
\end{code}
Agda's termination checker now accepts that the repeated calls to
|rec| are on strictly smaller configurations.

\subsection{Correctness}
\label{sec:basic-correctness}

As we have indexed our configuration datatypes with the input expression,
proving correctness of it is relatively straightforward. The type of the
function |step| guarantees that the configuration returned points to a leaf in
the input expression.

Proving the function |tail-rec-eval| correct amounts to show
that the auxiliary function, |rec|, that is iterated until a value is
produced, will behave the same as the original evaluator, |eval|. This
is expressed by the following lemma, proven by induction over the
accessibility predicate:
\begin{code}
  rec-correct  : forall (e : Expr) → (z : Zipperup e)
               -> (ac : Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z))
               -> eval e == rec e z ac
  rec-correct e z (acc rs)
    with step e z | inspect (step e) z
  ...  | inj1 z'  | [ Is ]
       = rec-correct e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))
  ...  | inj2 n   | [ Is ] = step-correct n e eq z
\end{code}
At this point, we still need to prove the |step-correct| lemma that it is
repeatedly applied.  As the |step| function is defined as a wrapper around the
|unload| function, it suffices to prove the following property of |unload|:
\begin{code}
  unload-correct  : forall (e : Expr) (n : Nat) (eq : eval e == n) (s : Stack2)
                  -> unload e n eq s ≡ inj2 n -> eval (plugup e s) == n
\end{code}
This proof follows immediately by induction over |s : Stack2|.

The main correctness theorem now states that |eval| and
|tail-rec-eval| are equal for all inputs:
\begin{code}
  correctness : forall (e : Expr) -> eval e == tail-rec-eval e
  correctness e with load e []
  ... | inj1 z = rec-correct e (z , ...) (<-WF e z)
  ... | inj2 _ = bot-elim ...
\end{code}
This finally completes the definition and verification of a
tail-recursive evaluator. 


\section{Verified tail-recursive fold for binary trees}\label{sec:tree}

  In this chapter, we present the transformation of a catamorphism for binary
  trees with natural numbers in the leaves onto a tail-recursive function.
  Moreover, we show how to prove that the resulting function terminates and that
  it is correct (for every possible input it computes the same result as the
  original fold).

  In order to do so, in \cref{subsec:bintree} we introduce the type of binary
  trees along with several examples of evaluation functions and how their common
  structure can be abstracted into a catamorphism. Then, in \cref{subsec:zipper},
  we explain the concept of a Zipper with its many type indexed variants and in
  \cref{subsec:onestep}.

  % In order to do, we first introduce the type of binary trees. In \subi We
  % provide both a proof of the termination of the transformation by defining a
  % suitable well-founded relation and also prove that the transformation is
  % correct.


  % The purpose of this thesis is to formalize the notion of dissection and its
  % usage to transform a fold into a tail-recursive function.

  % The first step is to prove that it is possible to write a function that
  % computes the fold of a non-linear (tree like) structure by tail recursion over
  % a explicit stack and that this function terminates.

  % This section is devoted to show that by using \emph{well founded} recursion we
  % can solve the problem for a specific datatype, the binary tree. simplified
  % version of the problem; that of traversing a tree from left to right. This
  % simplification from folding to traversing a tree will not be an impediment to
  % later generalize our results. A traversal can be conceptually thought as a
  % fold that does nothing.

  % The recursive structure of a inductive type is naturally defined in a top to
  % bottom manner. However, the traversing function has to exploit the left to
  % right inductive structure that is implicit in any tree-like type. For this
  % reason we cannot directly write the function that performs the traversal in
  % \Agda. The termination checker warns that it does not terminate because the
  % argument is not --manifestly-- structurally smaller.

  % In \cref{sec:termination} we reviewed several well known techniques that can
  % be used to assist \Agda's termination checker. \emph{Well founded} recursion
  % is the only one that allows us to make evident the left to right inductive
  % structure and provides us with a means for exploiting it.

%\subsection{Binary trees}\label{subsec:bintree}
%% Binary tree type
%% Evaluation
%% Abstraction with algebra
%% Catamorphism

%  The type of binary trees with natural numbers on the leaves is represented in
%  \Agda using the following inductive type.

%\begin{code}
%  data Tree : Set where
%    Tip   :  Nat   -> Tree
%    Node  :  Tree  -> Tree -> Tree
%\end{code}

%  As examples of binary trees for example we can have:

%  \todo{photo example}

%  Binary trees can be used to represent the syntax of arithmetic expressions. A
%  value of type |Tree| is an expression where the |Node| constructor stands for
%  addition and the natural numbers stand for themselves. Under this view, we can
%  interpret (or evaluate) an expression into a natural number using a function
%  |eval|.

%%{
%%format n     = "\AB{n}"
%%format t1    = "\AB{\ensuremath{t_1}}"
%%format t2    = "\AB{\ensuremath{t_2}}"
%\begin{code}
%  eval : Tree -> Nat
%  eval (Tip n)       = n
%  eval (Node t1 t2)  = eval t1 + eval t2
%\end{code}
%%}

%  The function |eval| is defined compositionally (in the style of denotational
%  semantics) where the value of a |Node| depends only on the values of the left
%  and right subtree.

%  Analogously, we can write another interpetation function that pretty prints a
%  binary tree. This is a function of type |Tree -> String|.

%%{
%%format n     = "\AB{n}"
%%format t1    = "\AB{\ensuremath{t_1}}"
%%format t2    = "\AB{\ensuremath{t_2}}"
%\begin{code}
%  pretty : Tree -> String
%  pretty (Tip n)       = show n
%  pretty (Node t1 t2)  = pretty t1 ++ " + " ++ pretty t2
%\end{code}
%%}

%  Both interpretation functions share some underlying structure. In the case of
%  |eval|, when evaluating the constructor |Node| we combine the results of both
%  subtrees using the addition operator |+| while when pretty printing we combine
%  them by concatenating the resulting |String|s. The concrete functions used in
%  both can be abstracted into an algebra.

%\begin{code}
%  record TreeAlg : Set1 where
%    field
%      A      : Set
%      TipA   : Nat -> A
%      NodeA  : A -> A -> A
%\end{code}

%  Given an algebra, we can define a catamorphism that folds a tree into a value
%  of the carrier type specified by the algebra.

%%{
%%format n     = "\AB{n}"
%%format t1    = "\AB{\ensuremath{t_1}}"
%%format t2    = "\AB{\ensuremath{t_2}}"
%\begin{code}
%  treeCata : (tAlg : TreeAlg) -> Tree -> A tAlg
%  treeCata tAlg (Tip n)       = TipA  tAlg n
%  treeCata tAlg (Node t1 t2)  = NodeA tAlg (treeCata tAlg t1) (treeCata tAlg t2)
%\end{code}
%%}

%  Using the catamorphism, the function |eval| is equivalent to |eval'|.

%%{
%%format tAlg = "\AB{tAlg}"
%\begin{code}
%  eval' : Tree -> Nat
%  eval' = treeCata tAlg
%    where
%      tAlg : TreeAlg
%      tAlg = record { A = Nat  ;  TipA = id  ;  NodeA = \_+\_ }
%\end{code}
%%}


%\subsection{Zipper}\label{subsec:zipper}

%  Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any leaf of a
%  binary tree can be represented as a pair of the natural number it holds and
%  the path from the root of the tree to the position it occupies.

%\begin{code}
%  UZipper : Set
%  UZipper = Nat * Stack
%\end{code}

%  At each |Node| constructor, the path has to record whether the leaf occurs in
%  the left or the right subtree. Moreover, from a value of \emph{Zipper} we
%  should be able to reconstruct the original tree thus each time the path choses
%  between left or right it has to keep track of the remaining subtree.

%\begin{code}
%  Stack : Set
%  Stack = List (Tree U+ Tree)
%\end{code}

%  In \cref{fig:zipperexample}, there are two examples of \emph{Zipper} where the
%  leaf in focus is marked with a box $\Box$. The \emph{Zipper} shown on the
%  bottom is a tuple with the path to the leaf and the natural number. In the
%  path, a left arrow {\color{red}$\leftarrow$} (correspondingly a right arrow
%  {\color{green}$\rightarrow$}) represents that the rest of the path points to a
%  leaf in the left (right) subtree of the |Node|.

%\begin{figure}[h]
%\begin{center}
%  \includegraphics[scale=0.06]{images/zipperexample}
%  \caption{Example of \emph{Zipper}}
%  \label{fig:zipperexample}
%\end{center}
%\end{figure}

%  If we were able to freeze a traversal from left to right over a binary tree, a
%  value of type \emph{Zipper} would represent a concrete state of this
%  procedure. At each leaf, everything that has already been traversed appears to
%  the left of the |Stack| while the parts of the tree that still have to be
%  processed show up on the right.

%\begin{figure}[h]
%\begin{center}
%  \includegraphics[scale=0.04]{images/zippertraversal}
%  \caption{Example of freezing a traversal}
%  \label{fig:zippertraversal}
%\end{center}
%\end{figure}

%  In order to represent the state of folding a binary tree from left to right,
%  we can enrich the type of the |Stack| save not only the left subtrees (in case
%  the path points to the right {\color{green}$\rightarrow$}) but also the value
%  it evaluates (using the catamorphism) to and a proof of this equality.

%  The rest of the constructions we are going to show assume there is an ambient
%  tree algebra and that it is constant across all definitions and proofs. To
%  achieve this in \Agda, we create a new module parametrized by a |TreeAlg|.

%\begin{code}
%  module _ (tAlg : TreeAlg) where

%    open TreeAlg tAlg
%\end{code}

%  By |open|ing |tAlg| we bring into scope the type |A| and the fields |TipA| and
%  |NodeA| without need to make any further reference to |tAlg|. The type of
%  |Stack| is now defined as follows.

%%{
%%format a  = "\AB{a}"
%%format t  = "\AB{t}"
%%format eq = "\AB{eq}"

%\begin{code}
%  Stack : Set
%  Stack = List (Tree U+ Sigma A lambda a  -> Sigma Tree lambda t
%                                          -> treeCata tAlg t == a)

%  pattern Left   t       = inj1 t
%  pattern Right  a t eq  = inj2 (a , t , eq)
%\end{code}

%  The only piece of information required to compute the catamorphism of a |Tree|
%  are the |a| values that come from evaluating the subtrees that appear to the
%  left of the position under focus. However, as we will show later in
%  \todo{ref}, it is neccesary for proving termination to keep around the |Tree|
%  where the value came from. We say that |t| and the equality proof in
%  |Stack| are computationally irrelevant. However, in \Agda~we cannot express
%  such fact\footnote{In other systems like Coq the Tree would live in Prop}.
%%}

%  Given a |Stack| and a |Tree| (we can always embed a |Nat| into a |Tree| using
%  |Tip|), the original |Tree| can be reconstructed by recursing over the
%  |Stack|. At each step, it is known to which subtree the position belongs.

%%{
%%format t  = "\AB{t}"
%%format t1 = "\AB{t\ensuremath{_1}}"
%%format s  = "\AB{s}"
%\begin{code}
%    plugD : Tree → Stack → Tree
%    plugD t []                  = t
%    plugD t (Left t1 :: s)       = Node (plugD t s) t1
%    plugD t (Right _ t1 _ :: s)  = Node t1 (plugD t s)
%\end{code}

%  Until now, we have only considered that the |Stack| represents the path from
%  the root of the tree way down to the focused leaf. We can instead reverse the
%  |Stack| part of the \emph{Zipper} so the path travels bottom-up from the leaf
%  up to the root of the tree.

%\begin{figure}[h]
%\begin{center}
%  \includegraphics[scale=0.05,angle=270]{images/zipperbuvstd}
%  \caption{Bottom-Up versus Top-Down \emph{Zipper}}
%  \label{fig:zipperbuvstd}
%\end{center}
%\end{figure}

%  Under this view, we can reconstruct the original |Tree| from the
%  |Stack|.

%\begin{code}
%  plugU : Tree -> Stack -> Tree
%  plugU t (Left   t1 :: s)      = plugU (Node t t1) s
%  plugU t (Right  _ t1 _ :: s)  = plugU (Node t1 t) s
%  plugU t []                   = t
%\end{code}
%%}

%  The only difference between both interpretations of the \emph{Zipper} is that
%  to translate from one to the other we just need to reverse the |Stack|. We can
%  show that indeed the original |Tree| is preserved by the conversion.

%%{
%%format plugU-to-plugD = plugU "\AF{-to-}" plugD
%%format plugD-to-plugU = plugD "\AF{-to-}" plugU
%%format reverse = "\AF{reverse}"
%%format t = "\AB{t}"
%%format s = "\AB{s}"
%%format z = "\AB{z}"

%\begin{code}
%    plugU-to-plugD : forall t s -> plugU t s == plugD t (reverse s)
%    plugU-to-plugD  t  s = cdots

%    plugD-to-plugU : forall t s -> plugD t s == plugU t (reverse s)
%    plugD-to-plugU t  s = cdots
%\end{code}

%\subsection{One-step of a fold}\label{subsec:onestep}

%  The \emph{Zipper} type represents a snapshot of the internal state of a
%  catamorphism over a binary tree. From one value of \emph{Zipper} we can write
%  a pair of functions, |load| and |unload| that combined together perform one
%  step of the fold.

%\begin{code}
%    load : Tree -> Stack -> UZipper U+ A
%    load (Tip x) s       = inj1 (x , s)
%    load (Node t₁ t₂) s  = load t₁ (Left t₂ ∷ s)

%    unload : (t : Tree) → (a : A) → (eq : treeCata tAlg t) ≡ a -> Stack -> UZipper U+ A
%    unload t a eq []                     = inj2 a
%    unload t a eq (Left t′ ∷ s)          = load t′ (Right a t eq :: s)
%    unload t a eq (Right a′ t′ eq′ ∷ s)  = unload  (Node t′ t) (NodeA a′ a) (cong₂ NodeA eq′ eq) s
%\end{code}

%  The function |unload| traverses the |Stack| combining all the results of
%  evaluating the subtrees that were on the left of the position until either
%  reaches a |Node| that has an unevaluated subtree on the right (|Left|
%  constructor) or the |Stack| is empty and the |Tree| has been fully evaluated.
%  When the former case occurs the |load| function is in charge of traversing the
%  subtree on the right to find the leftmost leaf.

%  \todo{maybe talk about irrelevance of t and eq?}

%  A folding step just consists of calling |unload| passing appropiate arguments.

%\begin{code}
%    step : UZipper -> UZipper U+ A
%    step (n , s) = unload (Tip n) (TipA n) refl s
%\end{code}

%  More graphically, the proccess of folding the tree one step is depicted in in
%  \cref{fig:onestep},

%\begin{figure}[h]
%\begin{center}
%  \includegraphics[scale=0.05,angle=180]{images/onestep}
%  \caption{One step of fold}
%  \label{fig:onestep}
%\end{center}
%\end{figure}
%%}

%\subsection{Folding a |Tree|}

%  From the machinery we have developed so far one would be inclined to think
%  that in order to fold a |Tree| it will suffice to find a fixed point of the
%  function |step|.

%\begin{code}
%  foldTree : Tree -> Nat
%  foldTree t with load t []
%  ... | inj2 n = n
%  ... | inj1 z = rec z
%    where
%      rec : UZipper -> Nat
%      rec z with step z
%      ... | inj1 z'  = rec z'
%      ... | inj2 n   = n
%\end{code}

%  However, it does not work. \Agda's termination checker is right when it warns
%  that the |z'| passed as an argument to the recursive call on |rec| is not
%  structurally smaller than |z| and therefore the fixed point of |step| might
%  not exists\footnote{|rec| loops forever}.

%  From an outer perspective, it is fair to assert that for any possible input of
%  type |UZipper|, the function |rec| has a fixed point. A value of |UZipper|
%  focus on the position of a concrete leaf in a value of type |Tree|, and the
%  function |step| refocuses the to the next leaf on the right. Because there are
%  finitely many leaves on a |Tree|, the function |rec| must always terminate.

%  In order to solve this problem, in the next subsections we will develop the
%  notion of indexed \emph{Zipper} and show how it allows us to define an order
%  relation between positions (\emph{Zipper}s) of the same |Tree|. This will be
%  the key to define |rec| by structural recursion.

%\subsection{Indexed \emph{Zipper}}\label{subsec:ixzipper}

%  The current type of \emph{Zipper}, |UZipper| does not encode too much
%  information. Given a value, it is not possible to statically know the |Tree|
%  from which it represents a position. If we are to compare a pair of |UZipper|
%  we need them to represent positions on the same |Tree| otherwise it does not
%  make sense.

%  We can address this shortcoming in the current representation by creating a
%  new type wrapper over |UZipper| that is type indexed by the |Tree| where it is
%  a position.

%\begin{code}
%  plugZD : UZipper -> Tree
%  plugZD (t , s) = plugD (Tip t) s
%\end{code}

%\begin{code}
%  data ZipperD (t : Tree) : Set where
%    _,_ : (z : UZipper) -> plugZD z == t -> ZipperD t
%\end{code}

%  From an indexed \emph{Zipper} we can forget the extra information and recover
%  the original |UZipper|.

%\begin{code}
%    forgetD : ∀ {t : Tree} -> (z : ZipperD t) -> UZipper
%    forgetD (z , _) = z
%\end{code}
%%}
%\subsection{\emph{Well founded} recursion}

%\subsection{Catamorphism}
%\subsection{Correctness}
%\subsection{Discussion}

%   Any tree-like datatype shares a common branching structure with the type of
%   skeleton binary trees. We will use this type as the basis of our work.

%   \InsertCode{Proposal/Tree/Base.tex}{Tree}

%   Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any position
%   in the tree can be represented as a pair of a subtree and a stack that holds
%   all the trees, to the left and to the right, in the path to the root.

%   \InsertCode{Proposal/Tree/Base.tex}{Stack}

%   Given a value of type \AD{Zipper} it is possible to \emph{plug} the subtree
%   and the stack together to reconstruct the original tree.

%   \InsertCode{Proposal/Tree/Base.tex}{BUPlug}

%   Navigating one position to the right in the tree can be easily defined in a
%   tail-recursive manner.

%   \InsertCode{Proposal/Tree/Base.tex}{BURight}

%   However, it is not possible to write a function that calculates the rightmost
%   position of the tree by iterating the \AF{right} function until it yields
%   \AI{nothing}.

%   \InsertCode{Proposal/Tree/Base.tex}{BUIterate}

%   Pattern matching on the result of \AF{right}\AS{}\AB{z} does not reveal any
%   structural relation between the input \AB{z} and \AB{z₁}. Thus \Agda~'s
%   termination checker rightfully classifies the function as non-terminating. It
%   does not know in which sense the recursive call is made on a smaller argument.

% \subsection{Setting the stage}
% \label{subsec:preparing}

%   To be able to define \AF{rightmost}, we should find the structure
%   that decreases with each call to the function \AF{right} so \AF{rightmost} can
%   be defined by \emph{well founded} recursion over it.

%   Any position in the tree has a finite number of positions to the right of
%   itself. A value of type \AD{Zipper} represents a position in the tree and for
%   this reason each time we apply the function \AF{right} to some input the
%   number of positions to the right decreases.

%   Using \emph{well founded} recursion, as explained in \cref{sec:termination},
%   we can define a relation \AD{\_<\_} over elements of \AD{Zipper} that exposes
%   the decreasing structure of moving to the right.

%   Additionally, by proving \textit{well foundedness} of the relation and the
%   property that whenever the evaluation of \AF{right} \AB{z} yields a
%   \AI{just}\AS{}\AB{z₁} then \mbox{\AB{z₁}\AS{}\AD{<}\AS{}\AB{z}}, we will be
%   able to define \AF{rightmost} by structural recursion on the accessibility
%   predicate of \AD{\_<\_}.

%   \InsertCode{Proposal/Tree/Base.tex}{Skeleton}

%   The purpose of the following subsections is to show how we can fill
%   the open holes and the definition of \AD{\_<\_}.

% \subsection{Defining the relation}

%   The relation we need shall consider positions on the left subtree of a
%   \AI{Node} bigger than the \AI{Node} itself which at the same time is bigger
%   than any position in its right subtree.

%   Following Huet's idea, we regard the \AD{Stack} type as a path going
%   \textit{backwards} from the position of the subtree up to the root. The
%   relation has to be inductively defined on the \AD{Stack} part of the
%   \AD{Zipper}.  Removing a constructor from the \AD{Stack} means moving up a
%   position on the tree.

%   For any two arbitrary positions on the tree, it is unknown a priori what is
%   the order of removing constructors from the stack, that has to be followed to
%   reach one of the base cases.
%   Because of this, the relation has to be able to handle all possible situations
%   which effectively will lead to a relation that allows us to prove that any two
%   elements are related in both directions. Needless to say that such relation
%   is just useless for our mission: a change of representation is needed.

%   As an alternative, we can consider the \AD{Stack} as the \textit{forward} path
%   from the root to the position where the subtree is located. A \emph{plug} operator
%   that reconstruct the tree from the root can also be defined.

%   \InsertCode{Proposal/Tree/Base.tex}{TDPlug}

%   The new representation for positions is better suited for defining the
%   relation where positions to the right are considered smaller than positions to
%   the left. However, for our purpose of traversing the tree tail recursively,
%   the \textit{backward} representation is a more natural fit.

%   For this reason it is convenient to keep both representations and have a means
%   of converting from one to the other. The conversion amounts to reverse the
%   \AD{Stack}. To be sure that both representations are equivalent we can prove
%   that plugging in one should yield the same tree as converting and plugging in
%   the other.

%   \InsertCode{Proposal/Tree/Base.tex}{Convert}

%   We are ready to define the relation between elements of type \AD{Zipper}. The
%   main idea of the relation is to look in the \AD{Stack} part of the \AD{Zipper}
%   for the point where both \AD{Stack}s diverge.

%   Once this happens, the \AD{Stack} that has a \AI{Left} constructor on top
%   indicates that its position is located in the left subtree of the \AI{Node} and
%   therefore should be always considered smaller than the \AI{Node} itself and
%   than any position that is in the right subtree.

%   When the topmost constructor of the \AD{Stack} is \AI{Right} this means that
%   the location is in the right subtree. This position is smaller than the
%   \AI{Node} itself and any other position on the left subtree.

%   The relation we defined is formalized in \Agda~as follows.

%   \InsertCode{Proposal/Tree/Base.tex}{TDRel}

%   Two values of type \AD{Zipper} related by \AD{\_<\_} should represent
%   positions in the same tree. By including the information of how the subtrees
%   are reconstructed from the \AD{Tree} and \AD{Stack} on the other side of the
%   relation this invariant is enforced in the type level.
%   We can indeed prove that any two related elements when \emph{plugged} yield
%   the same tree.

%   \InsertCode{Proposal/Tree/Base.tex}{Related}

% \subsection{Proving \textit{well foundedness}}

%   The relation itself would be useless if we cannot prove that it is \emph{well
%   founded}. As it was explained in \cref{subsec:wf}, the \emph{well foundedness}
%   property for a relation requires us to exploit the recursive structure of either
%   the input, in the base cases, or the proof, in the inductive cases. If
%   we are not able to show \Agda's termination checker that the argument is
%   --obviously-- structurally smaller then we would not be able to use recursion
%   to prove \emph{well foundedness}.

%   The naive approach to the proof fails because in general pattern matching on
%   the \AD{\_<\_} proof does not reveal any information about the structure of
%   the tree of which the two \AD{Zipper}s are a decomposition.

%   In the base cases, the structure we need to perform recursion is exactly the
%   subtrees of the original tree, however this is not explicit in the proof.

%   This realisation motivates us to define a new relation over \AD{Zipper} that
%   makes the tree explicit. Even though we proved that related \AD{Zipper} values
%   are positions of the same tree we include the proofs that both trees
%   reconstruct to the same tree in the relation so during the proof we can refine
%   the structure of the tree by pattern matching. This is the crucial step that
%   allows the proof of \emph{well foundedness} to succeed.

%   \InsertCode{Proposal/Tree/Base.tex}{TDRelIx}

%   Because the new relation is indexed by a \AD{Tree} the definition of what it
%   means for this relation to be \emph{well founded} has to change accordingly. The
%   relation is \emph{well founded} if for any \AD{Tree} any position of it,
%   \AD{Zipper}, is accessible.

%   \InsertCode{Proposal/Tree/Base.tex}{WF}

%   The full proof is omitted but can be found in the accompanying code. It works
%   by induction on the \AD{\_<\_} structure as before, but it uses the equality
%   proofs to discover the smaller structure on which perform recursion.

% \subsection{Navigating through the tree}

%   Finally we have developed the necessary machinery to fill the holes of the
%   program we proposed in \cref{subsec:preparing}. The definition of \AF{rightmost}
%   is more complex than we originally devised due to the change of representation
%   that we use. Moreover, the full proof that \AF{right} yields a smaller element
%   involves a lot of auxiliary lemmas and a lot of rewriting regarding the
%   properties of list concatenation and reversal.

%   \InsertCode{Proposal/Tree/Base.tex}{Right-preserves}
%   \vspace*{-0.5cm}
%   \InsertCode{Proposal/Tree/Base.tex}{to-right}
%   \vspace*{-0.5cm}
%   \InsertCode{Proposal/Tree/Base.tex}{Rightmost}

% \subsection{From traverse to fold}\label{subsec:traverse-to-fold}

%   Once we have shown how it is possible to prove in \Agda~ that the traversal of
%   a tree from left to right in a tail recursive fashion terminates we are ready
%   to extend the work to show that the tail recursive counterpart of a fold also
%   terminates.

%   In this subsection we build the basis for the work on the thesis that will
%   allow us to prove the termination of a tail recursive fold. As a more interesting
%   example we will use the type of binary trees with natural numbers in the
%   leaves which resemble arithmetic expressions.

%   \InsertCode{Proposal/Tree/Fold.tex}{Tree}

%   The fold requires that the stack records both the subtrees that still need to
%   be traversed and the intermediate results that have not yet been consumed.  For
%   this reason, the \AD{Stack} datatype now becomes:

%   \InsertCode{Proposal/Tree/Fold.tex}{Stack}

%   In the case of the trees we are using, we can define an analogous
%   \emph{plugging} operator for both the \textit{backwards} and \textit{forwards}
%   view of the \AD{Stack}. Because the \AD{Stack} does not represent a path on
%   the original tree but is just a partial image of how the evaluation proceeds, we
%   embed the intermediate results as leaves to be able to output a full tree.

%   \InsertCode{Proposal/Tree/Fold.tex}{Plug}

%   As opposed to McBride's example as explained in \cref{subsec:problem} we
%   will not consider the tail recursive version of a fold as a pair of functions,
%   \AF{load} and \AF{unload}. Instead we will define a function that performs
%   only one step of the computation at a time. This will be needed to prove that
%   each step of the computation decreases regarding the relation thus it is
%   possible to define the tail recursive fold using \emph{well founded} recursion.

%   \InsertCode{Proposal/Tree/Fold.tex}{load-unload}

%   If we define a suitable relation over \AD{Zipper} we should be able to define
%   fold by iterating \AF{load/unload} until it yields a natural number.

%   \InsertCode{Proposal/Tree/Fold.tex}{fold}

%   The relation is not as straightforward to define as it was in the case of
%   traversing the tree with a \AD{Zipper} because now the structure of the tree
%   changes during the folding process.

%   Two related elements by \AD{\_<\_} need not to reconstruct to the same tree
%   but instead they reconstruct to a \textbf{partial image} of the original tree
%   where some full subtrees have been replaced by the values they denote.
