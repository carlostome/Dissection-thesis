%include expression.fmt

\chapter{A verified tail-recursive evaluator}
\label{chap:expression}

 In this \namecref{chap:expression}, we present the termination and correctness proof of a
 tail-recursive fold equivalent to the evaluation function |eval|, introduced in
 \cref{sec:intro:descr}. As a starting point, \cref{sec:expression:stage}, we
 take the definitions of the functions |load| and |unload1| and reformulate them:
 the problem of termination is reduced into finding a suitable well-founded
 relation. In the next \namecref{sec:expression:wellfounded}, \cref{sec:expression:wellfounded}, we show how
 to step-by-step construct such relation and prove its well-foundedness.
 \Cref{sec:expression:tailrec}, presents the terminating tail-recursive
 evaluator, and finally, in \cref{sec:expression:correctness}, we prove its
 correctness with regard to the |eval| function. We conclude in
 \cref{sec:expression:discuss} with a discussion about the pros and cons of our
 evaluator and point out other possible solutions in the design space.
 
\section{Setting the stage}
\label{sec:expression:stage}

  In the first place, we recapitulate the definitions of |load| and |unload1|
  from the introduction (\Cref{sec:intro:descr}):
  %
  \begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload1 v   Top             = v
    unload1 v   (Right v' stk)  = unloadN (v' + v) stk
    unload1 v   (Left r stk)    = loadN r (Right v stk)
  \end{code}
  % 
  The problematic call for \Agda's termination checker is the last clause of the
  |unload1| function, that calls |load| on the expression stored on the top of the
  stack. From the definition of |load|, it is clear that we only ever push
  subtrees of the input on the stack. However, the termination checker has no
  reason to believe that the expression at the top of the stack is structurally
  smaller in any way. Indeed, if we were to redefine |load| as follows:
  \begin{code}
      load (Add e1 e2)  stk = load e1 (Left (f e2) stk)
  \end{code}
  we might use some function |f : Expr -> Expr| to push \emph{arbitrary}
  expressions on the stack, potentially leading to non termination.

  The functions |load| and |unload1| use the stack to store subtrees and partial
  results while folding the input expression. Thus, every node in the original
  tree is visited twice during the execution: first when the function |load|
  traverses the tree, until it finds the leftmost leaf; second when |unload1|
  inspects the stack in searching of an unevaluated subtree. This process is
  depicted in \cref{fig:load-unload}.

 \begin{figure}[h]
   \centering
   \input{figures/figure1}
   \caption{Traversing a tree with {\color{blue}load} and {\color{red}unload}}
   \label{fig:load-unload}
 \end{figure}

As there are finitely many nodes on a tree, the depicted traversal
using |load| and |unload1| must terminate---but how can we convince
\Agda's termination checker of this?

As a first approximation, we revise the definitions of |load| and |unload1|.
Rather than consuming the entire input in one go with a pair of mutually
recursive functions, we rewrite them to perform one `step' of the tail-recursive
fold.

The function |unload1| is defined by recursion over the stack as before, but with
one crucial difference. Instead of always returning the final result, it may
also\footnote{|U+| is \Agda's type of disjoint union.} return a new configuration
of our abstract machine, that is, a pair |Nat * Stack|:
\begin{code}
  unload1 : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload1 v   Top             = inj2 v
  unload1 v   (Right v' stk)  = unload1 (v' + v) stk
  unload1 v   (Left r stk)    = load r (Right v stk)
\end{code}
%
The other key difference arises in the definition of |load|:
%
\begin{code}
  load : Expr -> Stack -> (Nat * Stack) U+ Nat
  load (Val n)      stk = inj1 (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)
\end{code}
Rather than calling |unload1| upon reaching a value, it returns the current stack
and the value of the leftmost leaf. Even though the function never returns an
|inj2|, its type is aligned with the type of |unload1| so the definition of the 
functions resembles an abstract machine more closely.

Both these functions are now accepted by \Agda's termination checker as
they are clearly structurally recursive. We can use the functions 
to define the following evaluator:

%{
%format nrec   = "\nonterm{" rec "}"
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e with load e Top
  ... | inj1 (n , stk)  = rec (n , stk)
    where
      nrec : (Nat * Stack) -> Nat
      rec (n , stk) with unload1 n stk
      ... | inj1 (n' , stk' )  = nrec (n' , stk')
      ... | inj2 r             = r
\end{code}
%}
Here we use |load| to compute the initial configuration of our machine---that is, it finds the leftmost leaf in our initial expression and its associated stack.
We proceed by
repeatedly calling |unload1| until it returns a value.  This version of
our evaluator, however, does not pass the termination checker. The new
state |(n' , stk')| is not structurally smaller than the initial
state |(n , stk)|. If we work under the assumption that we have a
relation between the states |Nat * Stack| that decreases after every
call to |unload1| and a proof that the relation is well-founded---we know
this function will terminate eventually, we define the following version of the tail-recursive evaluator:
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e with load e Top
  ... | inj1 (n , stk)  = rec (n , stk) ??1
    where
      rec : (c : Nat * Stack) -> Acc ltOp c -> Nat
      rec (n , stk) (acc rs) with unload1 n stk
      ... | inj1 (n' , stk')  = rec (n' , stk') (rs ??2)
      ... | inj2 r            = r
\end{code}
To complete this definition, we still need to define a suitable
relation |ltOp| between configurations of type |Nat *
Stack|, prove the relation to be well-founded (|??1 : Acc ltOp (n , stk)|)
and show that the calls to |unload1| produce `smaller'
states (|??2 : (n' , stk') < (n , stk)|).
In the next sections, we define such a relation and prove it is
well-founded.

\section{Well-founded tree traversals}
\label{sec:expression:wellfounded}

The type of configurations of our abstract machine can be seen as a variation
of Huet's \emph{zippers}~\citeyearpar{Huet97thezipper}. The zipper associated
with an expression |e : Expr| is pair of a (sub)expression of |e| and
its \emph{context}. As demonstrated by \cite{McBride:2008:CLM:1328438.1328474}, the zippers
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
expression in a left-to-right fashion. The leftmost leaf---i.e. the first
leaf found after the initial call to |load|---is the greatest element; the
rightmost leaf is the smallest. In our example expression, 
\cref{fig:load-unload}, we would number the leaves as follows:

\begin{figure}[ht]
  \centering
  \input{figures/figure2}
  \caption{Numbered leaves of the tree}
  \label{fig:numbered}
\end{figure}

This section aims to formalize the relation that \emph{orders} elements of
the |ZipperType| type (that is, the configurations of the abstract machine) and
prove it is \emph{well-founded}. However, before doing so there are
two central problems with our choice of |ZipperType| datatype:

\begin{enumerate}
\item The |ZipperType| datatype is too liberal. As we evaluate our input expression
  the configuration of our abstract machine changes constantly, but satisfies
  one important \emph{invariant}: each configuration is a decomposition of the
  original input. Unless we make explicit this invariant, we will be hard-pressed
  to prove the well-foundedness of any relation defined on configurations.

\item The choice of the |Stack| datatype, as a path from the leaf to the
  root is convenient to define the tail-recursive machine, but impractical
  when defining the desired order relation. The top of a stack stores information about
  neighbouring nodes, but to compare two leaves we need \emph{global} information
  about their positions relative to the root.
\end{enumerate}

We will now address these limitations one by one. Firstly, by refining
the type of |ZipperType|, we will show how to capture the desired
invariant (\Cref{subsec:expression:invariant}). Secondly, we
explore a different representation of stacks, as paths from the root, that facilitates
the definition of the desired order relation (\Cref{subsec:expression:topdown}).
Subsequently, we will define the relation over configurations,
\cref{subsec:expression:ordering}, and sketch the proof that it is well-founded.

\subsection{Invariant preserving configurations}
\label{subsec:expression:invariant}

A value of type |ZipperType| denotes a leaf in our input expression. In the
previous example, the following |ZipperType| corresponds to the third leaf:

\begin{figure}[ht]
   \centering
  \input{figures/figure3}
  \caption{\emph{Configuration} of leaf number 3}
  \label{fig:examplezipper}
\end{figure}

\newpage

As we observed previously, we would like to refine the type |ZipperType| to
capture the invariant that execution preserves: every |ZipperType| denotes a
unique leaf in our input expression, or equivalently, a state of the abstract
machine computing the fold.
There is one problem still: the |Stack| datatype stores the values of the subtrees that have
been evaluated, but does not store the subtrees themselves.
In the example in \cref{fig:examplezipper}, 
when the traversal has reached the third leaf, all the
subexpressions to its left have been evaluated.

In order to record the necessary information, we redefine the |Stack| type as follows:
%
\begin{code}
  data Stack2 : Set where
    Left   : Expr -> Stack2 -> Stack2
    Right  : (n : Nat) -> (e : Expr) -> eval e == n -> Stack2 -> Stack2
    Top    : Stack2
\end{code}
%
The |Right| constructor now not only stores the value |n|, but also
records the subexpression |e| and the proof that |e| evaluates to
|n|. Although we are modifying the definition of the |Stack| data
type, we claim that the expression |e| and equality are not necessary
at runtime, but only required for the proof of well-foundedness---a
point we will return to in our discussion (\Cref{sec:expression:discuss}).
From now onwards, the type |ZipperType| uses |Stack2| as its right 
component:
\begin{code}
ZipperType = Nat * Stack2
\end{code}

The function |unload| was previously defined by induction over the stack
(\Cref{sec:expression:stage}), thus, it needs to be modified to work over the new type of
stacks, |Stack2|:
%
\begin{code}
  unload  : (n : Nat) -> (e : Expr) -> eval e == n -> Stack2 
          -> ZipperType U+ Nat
  unload n e eq Top                   = inj2 n
  unload n e eq (Left e' stk)         = load e' (Right n e eq stk)
  unload n e eq (Right n' e' eq' stk) 
    = unload  (n' + n) (Add e' e) (cong2 plusOp eq' eq) stk
\end{code}
%

A value of type |ZipperType| contains enough information to recover the input
expression. This is analogous to the |plug| operation on zippers:
\begin{code}
  plugup : Expr -> Stack2 -> Expr
  plugup e Top                    = e
  plugup e (Left t       stk)  = plugup (Add e t) stk
  plugup e (Right _ t _  stk)  = plugup (Add t e) stk

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
\label{subsec:expression:topdown}

Next, we would like to formalize the left-to-right order on the configurations
of our abstract machine.
The |Stack| in the |ZipperType| represents a path upwards, from the leaf to the
root of the input expression.
This is useful when navigating to neighbouring nodes, but makes it harder
to compare the relative positions of two configurations.
We now consider the value of |ZipperType| corresponding to
leaves with numbers 3 and 4 in our running example:

\begin{figure}[ht]
   \centering
  \input{figures/figure4}
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

Instead, we would like to compare the \emph{bottom} elements of both
stacks.  The common suffix of the stacks shows that both positions are
in the left subtree of the root. Once these paths---read from right
to left---diverge, we have found the exact node |Add| where one of the
positions is in the left subtree and the other in the right.

When comparing two |Stack|s, we therefore want to consider them as paths
\emph{from the root} to the leaf. In \cref{fig:comparison}, this corresponds
with reading the \emph{stack}s from right to left---as opposed to their
current order from left to right.  Fortunately, this observation does not
require us to change our definition of the |Stack| type; instead, we can define
a variant of the |plugup| function that interprets our contexts top-down rather
than bottom-up:
\begin{code}
  plugdown : Expr -> Stack2 -> Expr
  plugdown e Top                    = e
  plugdown e (Left t       stk)  = Add (plugdown e stk) t
  plugdown e (Right _ t _  stk)  = Add t (plugdown e stk)

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
                      -> plugZdown z ==  plugZup (convert z)
\end{code}
As before, we can create a wrapper around |ZipperType| that enforces
the |ZipperType| type to denote a leaf in the input expression |e|:
\begin{code}
  data Zipperdown (e : Expr) : Set where
    prodOp : (z : ZipperType) -> plugZdown z == e -> Zipperdown e
\end{code}
As a corollary of the |plugdown-to-plugup| property, we can define a
pair of functions to switch between |Zipperup| and |Zipperdown|:

\begin{code}
 Zipperdown-to-Zipperup : (e : Expr) -> Zipperdown e -> Zipperup e

 Zipperup-to-Zipperdown : (e : Expr) -> Zipperup e -> Zipperdown e
\end{code}

\subsection{Ordering configurations}
\label{subsec:expression:ordering}

Finally, we can define the ordering relation over values of type
|Zipperdown|. Even if the |Zipperup| is still used during execution of our
tail-recursive evaluator, the |Zipperdown| type will be used to prove
its termination.

The |IxLtOp| type defined below relates two configurations of type
|Zipperdown e|, that is, two states of the abstract machine evaluating
the input expression |e|:
%
\begin{code}
  data IxLtOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set where
    <-StepR  : llcorner r lrcorner ((t1 , s1) , ...) < ((t2 , s2) , ...)
      ->  llcorner Add l r lrcorner ((t1 , Right l n eq s1) , eq1) < ((t2 , Right l n eq s2) , eq2)
    <-StepL  : llcorner l lrcorner ((t1 , s1) , ...) < ((t2 , s2) , ...)
      ->  llcorner Add l r lrcorner ((t1 , Left r s1) , eq1) < ((t2 , Left r s2) , eq2)

    <-Base  :   (eq1 : Add e1 e2 == Add e1 (plugZdown t1 s1)) 
      ->        (eq2 : Add e1 e2 == Add (plugZdown t2 s2) e2)
      ->  llcorner Add e1 e2 lrcorner ((t1 , Right n e1 eq s1) , eq1) < ((t2 , Left e2 s2) , eq2)
\end{code}
%
Despite the apparent complexity, the relation is straightforward.  The
constructors |<-StepR| and |<-StepL| cover the inductive cases, consuming the
shared path from the root. When the paths diverge, the |<-Base| constructor
states that the positions in the right subtree are `smaller than' those in the
left subtree. To ensure that both configurations represent positions in the same
expression, the |<-Base| constructor takes as a parameter a pair of equalities
such that: the leaf pointed by the tail of the stack, |(t1 , s1)|, coincides,
|e2 == plugZdown t1 s1|, with the subtree stored in the top of the stack of the
other configuration |(t2 , Left e2 s2)|.

\subsection{Well-founded relation}
\label{subsec:expression:wellfounded}

Now we turn out attention into showing that the relation is \emph{well-founded}.
We sketch the proof below:
%
\begin{code}
    <-WF : forall (e : Expr) -> Well-founded (llcorner e lrcornerLtOp)
    <-WF e x = acc (aux e x)
          where
            aux : forall (e : Expr)  (x y : Zipperdown e)
                -> llcorner e lrcorner y < x -> Acc (llcorner e lrcornerLtOp) y
            aux = ...
\end{code}
%
The proof follows the standard schema of most proofs of well-foundedness. It
uses an auxiliary function, |aux|, that proves every configuration smaller than
|x| is accessible.

The proof proceeds initially by induction over the relation. The inductive
cases, corresponding to the |<-StepR| and |<-StepL| constructors, recurse on the
relation. In the base case, |<-Base|, we cannot recurse further on the relation.
We then proceed by recursing over the original expression |e|; without the type
index, the subexpressions to the left |e1| and right |e2| are not syntactically
related thus a recursive call is not possible. This step in the proof relies on
only comparing configurations arising from traversing the same initial
expression |e|.

Following the same layout of \cref{example:background:wellfounded-qs}, the proof
uses two lemmas that propagate the property of well-foundedness from
structurally smaller configurations, i.e. with less elements in the stack: 
%
\begin{code}
  accR  : forall (l : Expr) (r : Expr) (x : Nat) (s : Stack2) (n : Nat) (eq : eval l == n) 
        -> Acc (llcorner r lrcornerLtOp) (x , s) 
        -> forall (y : Zipperdown (Add l r))   -> llcorner Add l r lrcorner y < (x , Right l n eq s) 
                                               -> Acc (llcorner Add l r lrcornerLtOp) y

  accL  : forall (l : Expr) (r : Expr)  (x : Nat) (s : Stack2) 
        -> Well-founded (llcorner r lrcornerLtOp)
        -> Acc (llcorner l lrcornerLtOp) (x , s) 
        -> forall (y : Zipperdown (Add l r))  -> llcorner Add l r lrcornerLtOp y < (x , Left r s)
                                              -> Acc (llcorner Add l r lrcornerLtOp) y

\end{code}
%
The first lemma, |accR|, follows directly from induction over the accessibility
predicate. In the second lemma, |accL|, the proof is done by induction over the
argument |y|. There are two cases to consider: the inductive case, |<-StepL|,
proceeds by recursion over the accessibility predicate on the left subexpression
|Acc (llcorner l lrcornerLtOp) (x , s)|. However, the non-inductive case,
constructor |<-Base|, poses a technical challenge: for the relation to be
well-founded on the expression |Add l r| depends on itself being well-founded on the
right subtree |r|.  The former lemma, |accR|, handles this case if we can supply
a proof that the right subtree is accessible |Acc (llcorner r lrcornerLtOp) (x ,
s)|, which indeed, |accL| can produce using its argument of type |Well-founded
(llcorner r lrcornerLtOp)|.  This is only only possible because in the auxiliary
function, |aux|, the initial call to |accL|, can recursively use the
well-foundedness proof |<-WF|. Pattern matching reveals that the input expression
|e| is a node |Add l r|, thus the recursive call is done on a structurally
smaller input. Acceptance by the termination checker certifies it.

The type |IxLtOp|, more than being a single relation over configurations, is a
family of relations, one for every possible value of type |Expr|. Although
indexing the relation, and the configurations, is \emph{necessary} to prove that
it is well-founded, it is not amenable to prove properties of functions regarding
the relation. For instance, a proof that the function |unload| returns a smaller
configuration would require a lot of bookkeeping for the type index.

Instead of working directly with |IxLtOp|, we define another auxiliary relation
over non type-indexed configurations, and prove that there is an injection
between both under suitable assumptions:
%
\begin{code}
  data LtOp :  ZipperType -> ZipperType -> Set where
    <-StepR  : (t1 , s1) < (t2 , s2) 
             ->  (t1 , Right l n eq s1) < (t2 , Right l n eq s2)
    <-StepL  : (t1 , s1) < (t2 , s2) 
             ->  (t1 , Left r s1)  < (t2 , Left r s2)
    <-Base   :   (e1 == plugZdown t2 s2) ->  (e2 == plugZdown t1 s1)
             ->  (t1 , Right n e1 eq s1) < (t2 , Left e2 s2)

  to  :  (e : Expr) (z1 z2 : ZipperType)
      -> (eq1 : plugZdown z1 == e) (eq2 : plugZdown z2 == e)
      -> z1 < z2 -> llcorner e lrcorner (z1 , eq1) < (z2 , eq2)
\end{code}
%
The definition of |LtOp| is an exact blueprint of its type-indexed counterpart.
The only difference is that all the refined type indices stripped off the
constructors.

\section{A terminating tail-recursive evaluator}
\label{sec:expression:tailrec}

We now have almost all the definitions in place to revise our tail-recursive
evaluator, |tail-rec-eval|. However, we are missing one essential ingredient: we still
need to show that the configuration decreases after a call to the |unload|
function.

Unfortunately, the function |unload| and the relation that we have
defined work on `different' versions of the |Stack2|: the relation
compares stacks top-down; the |unload| function manipulates stacks
bottom-up. Furthermore, the function |unload| as defined previously
manipulates elements of the |ZipperType| type directly, with no further type-level
constraints relating these to the original input expression.

In the remainder of this section, we will reconcile these differences and complete
the definition of our tail-recursive evaluator.

\paragraph{Decreasing recursive calls}

To define our tail-recursive evaluator, we will begin by defining an
auxiliary |step| function that performs a single step of the
computation. We will define the desired evaluator by iterating the
|step| function, proving that it decreases in each iteration.

The |step| function calls |unload| to produce a new configuration, if
it exists.  If the |unload| function returns a natural number, |inj2
v|, the entire input tree has been processed and the function
terminates:
%
\begin{code}
  step : (e : Expr) -> Zipperup e -> Zipperup e U+ Nat
  step e ((n , stk) , eq)
    with unload n (Val n) refl stk
    ... | inj1 (n' , stk')  = inj1 ((n' , stk' ) , ...)
    ... | inj2 v            = inj2 v
\end{code}
%
We have omitted the second component of the result returned in the
first branch, corresponding to a proof that |plugZup (n' , stk') ==
e|. The crucial lemma, which we need to complete this proof,
states that the |unload| function respects our invariant:
%
\begin{code}
  unload-preserves-plugup  :
    forall (n : Nat) (e : Expr) (eq : eval e == x) (s : Stack2) (z : ZipperType)
    -> unload n e eq s == inj1 z
    -> forall (e' : Expr) -> plugup e s == e' -> plugZup z == e'
\end{code}
%
The proof proceeds by induction over the stack part of the configuration. In the
case the stack is empty, there is nothing to show, |unload| returns a natural
number wrapped in |inj2|. In case the stack is not empty, depending on the
element in the top, either |Right| or |Left|, it calls itself recursively or
uses a lemma showing that the function |load| honors the
invariant too:
%
\begin{code}
  load-preserves-plugup : forall (e : Expr) (s : Stack2) (z : ZipperType)
                        -> load e s ≡ inj1 z 
                        -> forall (t : Expr) -> plugup e s == t -> plugZup z == t
\end{code}
%
The lemma is proven by induction on the expression |e|.

Lastly, we can define the theorem stating that the |step| function always
returns a smaller configuration:
%
\begin{code}
  step-<  : forall (e : Expr) -> (z z' : Zipperup e) -> step e z == inj1 z'
          -> llcorner e lrcorner Zipperup-to-Zipperdown z' < Zipperup-to-Zipperdown z
\end{code}

Proving this statement directly is tedious, as there are many cases to cover and
the expression |e| occurring in the types makes it difficult to identify and
prove lemmas covering the individual cases.  We can simplify things by appealing
to the non type-indexed relation |LtOp| and the lemma |unload-preserves-plugup|.
Thus to complete the theorem, it is sufficient to show that the function
|unload| delivers a smaller |ZipperType| with the stacks reversed:
%
\begin{code}
  unload-<  : forall (n : Nat) (s : Stack2) (e : Expr) (s' : Stack2)
            -> unload n (Val n) refl s == inj1 (t' , s')
            -> (t' , reverse s') < (n , reverse s)
\end{code}
%
The proof is done by induction over the stack supported; the complete
proof requires some bookkeeping, covering around 200 lines of code,
but is conceptually not complicated.

The function |tail-rec-eval| is now completed as follows:\footnote{|inspect| is
an \Agda~idiom needed to remember that |z'| is the result of the call |step e z|.}
%
\begin{code}
  rec  : (e : Expr) -> (z : Zipperup e)
       -> Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z) -> Zipperup e U+ Nat
  rec e z (acc rs) = with step e z | inspect (step e) z
  ...  | inj2 n   | _       = inj2 n
  ...  | inj1 z'  | [ Is ]  = rec e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))
\end{code}
%
The auxiliary recursor |rec| is defined by structural recursion over the
accessibility predicate, thus, it provably terminates. Using the ancillary lemma
|step-<|, we demonstrate that repeated invocations of the function |step| are 
done on strictly smaller configurations. Therefore, \Agda's termination checker
accepts the function as terminating.

The tail-recursive evaluator, |tail-rec-eval|, is then defined as a wrapper over
|rec|: it uses the fact that the relation is well-founded to feed the initial
input and a proof that is accessible:
%
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e with load e Top
  ... | inj1 z = rec e (z , ...) (<-WF e z)
\end{code}

\section{Correctness}
\label{sec:expression:correctness}

Indexing the datatype of configurations is useful when proving correctness
of the tail-recursive evaluator. The type of the function |step| guarantees by
construction that the input expression never changes during the fold: the
invariant consistently holds. Because the input expression remains constant
across invocations, the result of |eval| does so also.

Proving the function |tail-rec-eval| correct amounts to showing that the auxiliary
function, |rec|, iterated until a value is produced, behaves as |eval|.
The auxiliary function |rec| is defined by recursion over the accessibility
predicate, thus the proof is done by induction over the same argument:
%
\begin{code}
  rec-correct  : forall (e : Expr) -> (z : Zipperup e)
               -> (ac : Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z))
               -> eval e == rec e z ac
  rec-correct e z (acc rs)
    with step e z | inspect (step e) z
  ...  | inj1 z'  | [ Is ]
       = rec-correct e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))
  ...  | inj2 n   | [ Is ] = step-correct e z n Is
\end{code}
%
While the proof by induction covers the recursion, we still have to prove the
base case: when there are no more subexpressions left to fold, the resulting
natural number is equal to evaluating the input expression using |eval|. The lemma
|step-correct| precisely states that:
%
\begin{code}
    step-correct  : forall (e : Expr) -> (z : Zipperup e) 
                  -> forall (n : Nat) -> step e z ≡ inj2 n -> eval e ≡ n
\end{code}
%
As |step| is a wrapper around the function |unload|, it
suffices to prove the following property of |unload|:
%
\begin{code}
  unload-correct  : forall (n : Nat) (e : Expr)  (eq : eval e == n) (s : Stack2)
                  -> forall (m : Nat) -> unload n e eq s == inj2 m -> eval (plugup e s) == m
  unload-correct e n eq Top .. n refl              = sym eq
  unload-correct e n eq (Left x s) r p             = bot-elim ...
  unload-correct e n eq (Right r' e' eq' s) r p    
    = unload-correct  (r' + r) (Add e' e) (cong2 plusOp eq' eq) s r p
\end{code}
%
The proof follows immediately by induction over |s : Stack2| using the fact
that equality is congruent.

The main correctness theorem now shows that |eval| and
|tail-rec-eval| are equal for all inputs:
%
\begin{code}
  correctness : forall (e : Expr) -> eval e == tail-rec-eval e
  correctness e with load e Top
  ... | inj1 z = rec-correct e (z , ...) (<-WF e z)
  ... | inj2 _ = bot-elim ...
\end{code}
%
The definition and verification of a tail-recursive evaluator is completed. 

\section{Discussion}
\label{sec:expression:discuss}

In this \namecref{chap:expression}, we have seen how to define and verify a
tail-recursive evaluator for the type of expressions |Expr|. Before wrapping up
the evaluator, we address some open questions and issues:

\begin{itemize}
  \item
Our construction relies on two key points: type-indexed configurations and a
well-founded relation. The former is essential for the latter, without the
type-index in the configuration type, |Zipperdown|, is not possible to prove
well-foundedness.  However, enlarging the type of the stacks to prove the
required properties comes at a cost: the runtime impact of the function
|tail-rec-eval| is larger than the pair of mutually recursive functions |load|
and |unload1|, \cref{sec:intro:descr}, that we took as starting point. 

\item
Our tail-recursive evaluator is tied to a concrete algebra composed of
the functions |plusOp| and |id|, however, a tail-recursive machine capable 
of computing the fold for any algebra over any |Expr| would be preferable. 

\item
Alternatively, we can formulate a provably terminating tail-recursive fold using
    continuations. The idea consists in storing a partially applied recursive
    call---the continuation---at the point where the argument is known to be
    structurally smaller than the input. In such approach, however, the execution
    stack is no longer a first-order object, thus, the tail-recursive function
    cannot be longer understood as the formalization of an abstract machine.

\item 
The tail-recursive evaluator we developed exchanges space in the execution stack
    for space in the heap. The runtime environment where the function is
    executed has to explicitly allocate space in the heap to hold the |Stack|
    argument of |tail-rec-eval|. On the practical level, it is not clear what
    we gain from the transformation.
    
\item
Previous work by \cite{Danvy2009} has focused on constructing abstract machines
    from a one step reduction function. Our tail-recursive evaluator is an
    example of an abstract machine that uses a reduction function, the algebra.
    Both machines are definitely related.

\item
The |step| function, which our evaluator iterates, performs several reductions
    each time it is applied. However, the interpretation of a tail-recursive
    function as an abstract machine fits more naturally when the function it
    iterates reduces at most one redex at a time.
\end{itemize}

In the next paragraphs we discuss each of these points.

\paragraph{Irrelevant arguments}

\Agda~allows the programmer to identify the arguments of a function or the
parameters of a constructor as \emph{computationally irrelevant}. Code marked as
irrelevant is erased, or interpreted as the unit type, when extracted into a
\Haskell~executable. The typechecker has ensured that evaluation does not depend
on irrelevant code.

If we compare the type of stacks, |Stack| and |Stack2|, the constructor |Right|
in the latter additionally stores the already evaluated subexpressions and the
associated proofs:
%
\begin{code}
  data Stack : Set where
    Right  : (n : Nat) -> Stack -> Stack
    ...

  data Stack2 : Set where
    Right  : (n : Nat) -> (e : Expr) -> (eval e == n) -> Stack2 -> Stack2
    ...
\end{code}
%
The purpose of the expression and the proof is only to aid proving termination
and correctness, and they should not produce any runtime overhead if we compare
it with the naive tail-recursive function. We can address the issue and remove
the extra cost, by marking both parameters as irrelevant in the type of
of |Stack2|:
%
\begin{code}
  data Stack3 : Set where  -- does not typecheck!
    Right  : (n : Nat) -> ..(e : Expr) -> ..(eval e == n) -> Stack3 -> Stack3
    ...
\end{code}
%
In the above definition, the expression |e : Expr| and the proof |eval e == n|
are irrelevant---marked with a preceding |..| (dot). Unfortunately, the
datatype |Stack3| does not typecheck, the function |eval| expects a non
irrelevant argument, which is necessary since we defined it by pattern matching
on its argument. We can tackle this obstacle by reifiying the graph of the function
|eval| as a datatype:
%
\begin{code}
  data Eval : .. Expr -> Nat -> Set where
    eval-Val  : (n : Nat)      -> Eval (Val n) n
    eval-Add  : (e1 e2 : Expr) -> (n n' : Nat) 
              -> Eval e1 n -> Eval e2 n' -> Eval (Add e1 e2) (n + n')
\end{code}
%
Because we marked the first index of |Eval|, of type |Expr|, as irrelevant, we can 
define the type of irrelevant stacks as follows:
%
\begin{code}
  data Stack3 : Set where
    Right  : (n : Nat) -> ..(e : Expr) -> ..(Eval e n) -> Stack3 -> Stack3
    ...
\end{code}
%
If we assume that we can adapt the rest of the facilities, such as auxiliary
datatypes, functions, etc, to use |Stack3| then the tail-recursive evaluator
would have the same runtime impact as the pair of mutually recursive functions
|load| and |unload1| from the introduction (\Cref{sec:intro:descr}).

\paragraph{Tail-recursive fold}

We constructed a tail-recursive evaluator equivalent to a fold over expressions
for a concrete algebra composed of |plusOp|, for the constructor |Add|, and |id|
for |Val|. The presentation in this simple terms is meant to reduce the overall
clutter and let the reader focus on the ideas driving the construction.
Nonetheless, we can easily generalize |tail-rec-eval| to a tail-recursive fold
equivalent to |foldExpr| (\Cref{sec:intro:descr}) that works for any algebra and
for any |Expr|. First, we define an algebra over |Expr| as the following triple:
%
\begin{code}
  record ExprAlg : Set1 where
    field
      a     : Set
      ValA  : Nat -> a
      AddA  : a -> a -> a
\end{code}
%
The folding function |foldExpr| takes the
algebra as a parameter rather than a pair of functions:
%
\begin{code}
  foldExpr : (alg : ExprAlg) -> Expr -> a alg
  foldExpr alg (Val n)      = ValA alg n
  foldExpr alg (Add e1 e2)  = AddA alg (foldExpr alg e1) (foldExpr alg e2)
\end{code}
%
The rest of the construction accounts for the algebra by augmenting every
datatype and function with a new parameter, the algebra. We can, instead,
use a module parametrized by the algebra:
%
\begin{code}
  module _ (alg : ExprAlg) where
    ... 
\end{code}
%
Using this approach, the definitions become more simple and clear; we do not
have to keep track of the algebra in every type signature. However, at the formal 
level the formalizations are equivalent.

The reader can find the formalization of the tail-recursive fold that uses
|ExprAlg| in the repository under the file \path{src/Tree/Indexed.agda}.

\paragraph{Continuations}

We can write a tail-recursive version of the evaluator from the introduction
(\Cref{sec:intro:descr}) using continuations. In order to do so, we define an 
auxiliary function, |go|, by structural recursion over the expression passing
the continuation as a parameter:
%
\begin{code}
  tail-rec-cont : Expr -> Nat
  tail-rec-cont = go id
    where  go : (Nat -> Nat) -> Expr -> Nat
           go k (Add e1 e2)  = go (lambda n -> go (k . (n +)) e2) e1
           go k (Val n)      = k n 
\end{code}
% 
In the first clause of the definition of |go|, the continuation passed as an
argument to the recursive call uses the result of left subexpression, |e1|, to
recurse over the right subexpression, |e2|. \Agda's termination checker
classifies the function as terminating because the recursive call is done at a
point where the argument is structurally smaller.

As an alternative design, we could redefine the type of stacks to explicitly
store the continuation. In the |Left| constructor instead of saving the right
subexpression for later processing, we cache the continuation corresponding to a
call of |unload1| over such expression. The type of stacks with continuations
would be as follows:
%
\begin{code}
  data StackKP : Set where
    Rightk  : Nat                      -> StackK -> StackK
    Leftk   : (Nat -> StackKP -> Nat)  -> StackK -> StackK
    Topk    : StackK
\end{code}

Accordingly, the pair of functions |load| and |unload1| have to change to
account for the continuations. The new |load| function, |loadk|, creates a
continuation on the right subexpression, and saves it on the stack, before it
proceeds by recursion over the left subexpression. The replacement of the
|unload1| function, |unloadk|, applies the continuation once it finds a |Left|
constructor in the stack. The definition of both functions is the following:
%
\begin{code}
    unloadk : Nat -> StackK -> Nat
    unloadk n Topk             = n
    unloadk n (Rightk n' stk)  = unloadk (n + n') stk
    unloadk n (Leftk k stk)    = k n stk

    loadk : Expr -> StackK -> Nat
    loadk (Add e1 e2) stk   = loadk e1 (Left (lambda n -> loadk e2 . (Right n)) stk)
    loadk (Val n) stk       = unloadk x stk

    evalk : Expr -> Nat
    evalk e = loadk e Topk
\end{code}

There is a problem, though, with this last approach. The |StackK| datatype is
not strictly positive, indeed, \Agda's positivity checker highlights the non
strictly positive occurrences in \nonpos{pink}: the type |StackK| appears as an
argument to the continuation in its own constructor |Leftk|.

Using continuations explicitly, the evaluators are obviously terminating: they
are solely defined by structural recursion over their input.  Nonetheless, we
cannot understand the tail-recursive functions |tail-rec-cont| and |evalk| as
first-order stack-based abstract machines anymore. The function |tail-rec-cont|
does not manipulate explicitly a stack but rather uses functions in the host
language, in this case \Agda, to implement tail-recursion. On the other hand,
the function |evalk| does use a stack, but \emph{again} relies on using
functions from the host language to do tail-recursion. We have traded a
first-order formulation in exchange for tail-recursion and termination.

\paragraph{Space trade-off}

Our tail-recursive evaluator uses a |Stack| argument as the reification of the
underlying execution stack. The evaluator, indeed, is tail-recursive because it
uses such argument to perform the tail calls. A explicit |Stack|, however, is not
for free; the runtime system still has to allocate and manage the stack.

For instance, in a functional language such as \Haskell,
GHC~\citep{marlow2004glasgow}---the \emph{de facto} \Haskell~implementation---
uses the same memory region for the allocation of the heap and the stack; the
former grows upwards while the latter grows downwards. Then, what do we gain by
transforming a fold into its tail-recursive counterpart?

We can mark the values saved in the stack with
strictness~\citep{wadler1987projections} annotations. At the point where the
function |unload| stores a term |n : Nat| in the stack, such term is a fully
evaluated value. The runtime system can reclaim the space that otherwise would
occupy as a thunk.

In a language like \Haskell, however, we have to take some extra care because of
its non-strict semantics. Our tail-recursive evaluator is not exactly equivalent
to a fold associated with a non inductive, possibly infinite, datatype. For
instance, if we pass to the |fold| function on |Expr| a function |const x y = x|
and the right subtree is an infinite value, then, our tail-recursive function
does not terminate while the original |fold| does.

\paragraph{Decompose, contract, recompose}

Danvy~\citeyearpar{Danvy2009} has previously shown how to derive a
reduction-free evaluation function beginning from a small step reduction
semantics. Given a term language, a specification of redexes in the language
---i.e. terms the can be immediately reduced in one step, and a one-step
contraction function, Danvy shows how to construct an abstract machine to
evaluate terms, that later turns into a reduction-free evaluation function.

The high level idea of his construction consists of applying a series of
functions: \textit{decompose} a term into potential redex and its evaluation
context, \textit{contract} the redex, and \textit{recompose} the term by
plugging back the result into the context. He then obtains the abstract machine
by finding a fixed point of the composition of the three functions. He later
observes~\citep{danvy2004refocusing} that the decomposition step always happens
right after a recomposition, thus, he further optimizes the machine by
deforesting the intermediate terms. He dubs the fusion of both functions, recompose
and decompose, \textit{refocusing}.

This concept of a machine is not very dissimilar to how our tail-recursive
evaluator, |tail-rec-eval|, operates. Danvy's abstract machine iterates the
one-step reduction function---decompose, contract, recompose---until the term
is fully evaluated, while, our tail-recursive evaluator iterates the function
|step|. A question is to wonder: how are both machines related for the type of
expressions, |Expr|? 

The first problem that arises, when formalizing Danvy's machine in a total
language such as \Agda, is that the decomposition step essentially corresponds
to the pair of mutually recursive functions |load| and |unload1|. As we
previously saw in \cref{sec:intro:descr}, the termination checker classifies them
as possibly non terminating. As we did for our tail-recursive machine, we could
define a well-founded relation to show that traversing an expression to find its
leftmost redex terminates. 

In Danvy's machine, once \emph{decompose} finds a redex, \emph{contract} reduces
it to a value. Our machine, on the other hand, uses the algebra, passed as a
parameter to |unload1|, to combine the results of previously evaluated
subexpressions. 

After Danvy's machine contracts the redex, it recomposes expression by plugging
the value into the context. Our function |unload1|, instead, recursively
traverses the stack looking for the next subexpression to |load|. 

We proved that our tail-recursive evaluator finds the fixed point of the one-step
function, |step|, because we carefully engineered such function to deliver a
smaller value by the well-founded relation over configurations. However, to
iterate \emph{decompose-contract-recompose} we would need to define a
well-founded relation over elements of type |Expr| and prove it decreases with
each invocation. 

Up to this point, we need to have two different relations just to construct
Danvy's machine in \Agda: one to prove that decomposition terminates, one to
prove that iterating the one step function terminates. Surprisingly, the
optimization that Danvy applies to the machine, \emph{refocusing}, which removes
any intermediate expression by fusing the decomposition and recomposition steps,
makes its more amenable to construct in \Agda. Indeed, it is a variation of our
tail-recursive evaluator with one difference: our one step function contracts
several redexes at once while Danvy's contracts only one at a time. In the next paragraph,
we explore the ramifications of modifying our one-step function to match Danvy's
abstract machine.

\paragraph{Fine-grained reduction}

Our tail-recursive evaluator, |tail-rec-eval|, iterates the function |unload1|
until it completely consumes the input expression and returns the result of the
fold. We can argue that |unload1| completes an excessive amount of work: while
traversing the stack in search for the next subexpression, it might perform
\emph{several reductions} before dispatching a call to |load| or returning a
value. \Cref{fig:spine} shows an example; the function |unload1|, starting
from the configuration corresponding to the leaf |Val 1|, traverses the
\emph{spine} at once while accumulating and reducing all partial results.

\begin{figure}[h]
  \centering
  \input{figures/figure5}
  \caption{{\color{red}unload} traverses the spine of an expression}
  \label{fig:spine}
\end{figure}

We should be able to rewrite the tail-recursive evaluator, such that iterates a
function that performs at most one reduction at a time. The evaluator would
match more closely the concept of an abstract machine designed as single step
transition system, but, as we will see, it would also increase the complexity of
the construction.

There is one fundamental idea in the definition of our tail-recursive evaluator:
the intermediate states, or configurations of the abstract machine, always
represent locations of leaves in the input expression. If |unload1| is
implemented not to consume the spine at once, we will have to reconsider what
constitute a valid configuration; aside from leaves, a not yet contracted redex
will also be a possible internal state:
%
\begin{code}
  data Config1 : Set where
    Leaf   : Nat -> Stack2 -> Config1

    Redex  :   (n   : Nat) -> (e1 : Expr) -> eval e1 == n 
           ->  (n'  : Nat) -> (e2 : Expr) -> eval e2 == n' 
           -> Stack2 -> Config1
\end{code}
%
The leaves of the input expression remain the same as before: a natural number and
the stack pointing to its position. The new constructor, |Redex|, represents
a \emph{redex} that is ready to be reduced. The definition of the function
|unload1| clarifies its purpose:
%
\begin{code}
  unload1 : (n : Nat) -> (e : Expr) -> eval e ≡ n -> Stack2 -> Config1 U+ Nat
  unload1 n e1 eq (Left e2 stk)           = load e2 (Right n e1 eq stk)
  unload1 n e1 eq1 (Right n' e2 eq2 stk)  = inj1 (Redex n' e2 eq2 n e1 eq1 stk)
  unload1 n _ _ Top                       = inj2 n
\end{code}
%
In the second clause, instead of recursing over the stack and applying |plusOp|
to |n| and |n'|, the function |unload1| returns the |Redex| immediately. The
function |step1| will be, in this case, the responsible of triggering the
reduction: 
%
\begin{code}
  step1 : Config1 -> Config1 U+ Nat
  step1 (Leaf n stk)                    
    = unload1 n (Val n) refl stk 
  step1 (Redex n e1 eq1 n' e2 eq2 stk)  
    = unload1 (n + n') (Add e1 e2) (cong2 plusOp eq1 eq2) stk
\end{code}

The key ingredient to build our tail-recursive evaluator was a well-founded
relation that decreases with every invocation of |step|.  Accordingly, we will
have to find a suitable relation over elements of type |Config1| (we omit the
type-indexed relation for the sake of the argument), prove it is
well-founded, and show it decreases with |step1|. For most of it, the
relation can be defined as |LtOp|: comparing two leaves or redexes in a common
subexpression is done inductively; comparing them if one is located on the left
subexpression and the other on the right constitutes the base case. However,
two more situations will need to be considered:

  \begin{itemize}
    \item Between two redexes, how do we determine which one is smaller if both
      belong to the same spine?
    \item Between a redex and a leaf, how do we encode that the leaf is bigger,
      if it is located at the end of the spine where the redex stands?
  \end{itemize}

The definition of the type |Config1|, increases the diversity of possibilities
that have to be dealt with, thus the complexity of functions and proofs. In
overall, we are trading a simple formulation that takes advantage of the fact
that the function |unload| provably terminates---it is defined by structural
recursion over the stack---for a more complicated one that demands explicit 
evidence of the termination.

In this part of the thesis, the main objective is not just to develop a
tail-recursive evaluator for binary trees, but, to prepare the stage for the
generic solution that we further present in \cref{chap:generic}. The simplicity
of our approach pays off, as it later will become clear that it has a
straightforward generalization.  However, it is not clear how changing the
function |unload| to one, that reduces at most one redex at a time, fits in the
construction as a whole, nor how it scales to the generic case. Certainly, it
should be possible but we have not explored such direction any further.
