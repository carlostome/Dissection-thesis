\documentclass[sigplan,review,10pt]{acmart}

%include preamble.tex
%include paper.fmt

% fontsize of code snippets
\renewcommand\hscodestyle{%
   \setlength\leftskip{0.1cm}%
   \footnotesize
}

\begin{document}

\title{From algebra to abstract machine: a verified generic construction}

\author{Carlos Tom\'e Corti\~nas}
\affiliation{
  \department{Department of Information and Computing Sciences}
  \institution{Utrecht University}
  \country{The Netherlands}
}
\email{c.tomecortinas@@students.uu.nl}

\author{Wouter Swierstra}
\affiliation{
  \department{Department of Information and Computing Sciences}
  \institution{Utrecht University}
  \country{The Netherlands}
}
\email{w.s.swierstra@@uu.nl}

\begin{abstract}
  Many functions over algebraic datatypes can be expressed in terms of
  a fold. Doing so, however, has one notable drawback: folds are not
  tail-recursive. As a result, a function defined in terms of a fold
  may raise a stack overflow when executed. This paper defines a
  datatype generic, tail-recursive higher-order function
  that is guaranteed to
  produce the same result as the fold. Doing so combines the
  compositional nature of folds and the performance benefits of
  a hand-written tail-recursive function in a single setting.
\end{abstract}

\include{ccs}

\keywords{datatype generic programming, catamorphisms, dissection,
  dependent types, Agda, well-founded recursion \fixme{Check keywords}}

\maketitle

\section{Introduction}
\label{sec:intro}
%{ begining of intro.fmt
%include intro.fmt

Folds, or \emph{catamorphisms}, are a pervasive programming
pattern. Folds generalize many simple traversals over algebraic data
types. Functions implemented by means of a fold are both compositional
and structurally recursive. Consider, for instance, the following
expression datatype, written in the programming
language Agda~\cite{norell}:

\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}
%
We can write a simple evaluator, mapping expressions to
natural numbers, as follows:
%
\begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
\end{code}
%
In the case for |Add e1 e2|, the |eval| function makes two recursive
calls and sums their results. Such a function can be implemented using a
fold, passing the addition and identity functions as the argument
algebra.
%
\begin{code}
  foldExpr : (Nat -> X) -> (X -> X -> X) -> Expr -> X
  foldExpr alg1 alg2 (Val n)      = alg1 n
  foldExpr alg1 alg2 (Add e1 e2)  = alg2 (foldExpr alg1 alg2 e1) (foldExpr alg1 alg2 e2)

  eval : Expr -> Nat
  eval = foldExpr id plusOp
\end{code}

Unfortunately, not everything in the garden is rosy. The operator |plusOp|
needs both of its parameters to be fully evaluated before it can
reduce further. As a result, the size of the
stack used during execution grows linearly with the size of the input,
potentially leading to a stack overflow on large inputs.

To address this problem, we can manually rewrite the evaluator to be
\emph{tail-recursive}. Modern compilers typically map tail-recursive
functions to machine code that runs in constant memory. To write such
a tail-recursive function, we need to introduce an explicit stack
storing both intermediate results and the subtrees that have not yet
been evaluated.

\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

We can define a tail-recursive evaluation function by means of a
pair of mutually recursive functions, |load| and |unload1|. The |load|
function traverses the expressions, pushing subtrees on the
stack; the |unload1| function unloads the stack, while accumulating a
(partial) result.

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

We can now define a tail-recursive version of |eval| by
calling |load| with an initially empty stack:

\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = load e Top
\end{code}

Implementing this tail-recursive evaluator comes at a price: Agda's
termination checker flags the |load| and |unload1| functions as
potentially non-terminating by highlighting them
\nonterm{orange}. Indeed, in the very last clause of the |unload1|
function a recursive call is made to arguments that are not
syntactically smaller. Furthermore, it is not clear at all that the
tail-recursive evaluator produces the same result as our original
one. It is precisely these issues that this paper tackles
by making the following novel contributions:
\begin{itemize}
\item We give a verified proof of termination of |tail-rec-eval| using
  a carefully chosen \emph{well-founded relation}
  (\Cref{sec:basics,sec:wf-example}). After redefining |tail-rec-eval| using
  this relation, we can prove the two evaluators equal in Agda.
\item We generalize this relation and its corresponding proof of
  well-foundedness, inspired by
  \citeauthor{dissection}'s~ work on
  \emph{dissections}~\cite{dissection}, to show how to calculate an abstract machine
  from an algebra. To do so, we define a universe of algebraic data
  types and a generic fold operation
  (\Cref{sec:generic}). Subsequently we show how to turn any
  structurally recursive function defined using a fold into its tail-recursive
  counterpart.
\item Finally, we present how our proofs of termination and semantics
  preservation from our example are generalized to the generic fold
  (\Cref{sec:genmachine,sec:correct-gen}).
\end{itemize}
Together these results give a verified function that computes a tail-recursive 
traversal from any algebra for any algebraic datatype.
All the constructions and proofs presented in this paper have been
implemented in and checked by Agda. The corresponding code is freely
available online.\footnote{\url{https://github.com/carlostome/Dissection-thesis}}

\section{Termination and tail-recursion}
\label{sec:basics}
Before tackling the generic case, we will present the termination
and correctness proof for the tail-recursive evaluator presented in
the introduction in some detail.

The problematic call for Agda's termination checker is the last clause of the
|unload1| function, that calls |load| on the expression stored on the top of the
stack. From the definition of |load|, it is clear that we only ever push
subtrees of the input on the stack. However, the termination checker has no
reason to believe that the expression at the top of the stack is structurally
smaller in any way. Indeed, if we were to redefine |load| as follows:
\begin{code}
    load (Add e1 e2)  stk = load e1 (Left (f e2) stk)
\end{code}
we might use some function |f : Expr -> Expr| to push \emph{arbitrary}
expressions on the stack, potentially leading to non-termination.

The functions |load| and |unload1| use the stack to store subtrees and partial
results while folding the input expression. Thus, every node in the original
tree is visited twice during the execution: first when the function |load|
traverses the tree, until it finds the leftmost leaf; second when |unload1|
inspects the stack in searching of an unevaluated subtree. This process is
depicted in \Cref{fig:load-unload}.

\begin{figure}
  \input{figures/figure1}
  \caption{Traversing a tree with {\color{blue}load} and {\color{red}unload}}
  \label{fig:load-unload}
\end{figure}

As there are finitely many nodes on a tree, the depicted traversal
using |load| and |unload1| must terminate -- but how can we convince
Agda's termination checker of this?

As a first approximation, we revise the definitions of |load| and
|unload1|. Rather than consuming the entire input in one go with a pair
of mutually recursive functions, we rewrite them to compute one `step' of the
fold.

The function |unload1| is defined by recursion over the stack as before, but with
one crucial difference. Instead of always returning the final result, it may
also\footnote{|U+| is Agda's type of disjoint union.} return a new configuration
of our abstract machine, that is, a pair |Nat * Stack|:
\begin{code}
  unload1 : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload1 v   Top             = inj2 v
  unload1 v   (Right v' stk)  = unload1 (v' + v) stk
  unload1 v   (Left r stk)    = load r (Right v stk)
\end{code}

The other key difference arises in the definition of |load|:
\begin{code}
  load : Expr -> Stack -> (Nat * Stack) U+ Nat
  load (Val n)      stk = inj1 (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)
\end{code}
Rather than calling |unload1| upon reaching a value, it returns the current stack
and the value of the leftmost leaf. Even though the function never returns an
|inj2|, its type is aligned with the type of |unload1| so the definition of both
functions resembles an an abstract machine more closely.

Both these functions are now accepted by Agda's termination checker as
they are clearly structurally recursive. We can use both these functions 
to define the following evaluator\footnote{We ignore |load|'s impossible case, it
can always be discharged with \hbox{|bot-elim : forall {X : Set} -> Bot -> X|}.}:
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
Here we use |load| to compute the initial configuration of our machine
-- that is, it finds the leftmost leaf in our initial expression and its associated stack.
We proceed by
repeatedly calling |unload1| until it returns a value.  This version of
our evaluator, however, does not pass the termination checker. The new
state, |(n' , stk')|, is not structurally smaller than the initial
state |(n , stk)|. If we work under the assumption that we have a
relation between the states |Nat * Stack| that decreases after every
call to |unload1| and a proof that the relation is well-founded -- we know
this function will terminate eventually.
We now define the following version of the tail-recursive evaluator:
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
In the next section, we will define such a relation and prove it is
well-founded.

\section{Well-founded tree traversals}
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
  \input{figures/figure2}
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
  \input{figures/figure3}
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
at run-time, but only required for the proof of well-foundedness -- a
point we will return to in our discussion (\Cref{sec:discussion}).
From now onwards, the type |ZipperType| uses |Stack2| as its right 
component:
%
\begin{code}
ZipperType = Nat * Stack2
\end{code}

The function |unload1| was previously defined by induction over the stack
(\Cref{sec:basics}), thus, it needs to be modified to work over the new type of
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

A value of type |ZipperType| contains enough information to recover the input
expression. This is analogous to the |plug| operation on zippers:
\begin{code}
  plugup : Expr -> Stack2 -> Expr
  plugup e Top                 = e
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
  plugdown e Top                 = e
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
that our |ZipperType| denotes a leaf in the input expression |e|:
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
    <-StepR  : llcorner r lrcorner ((t1 , s1) , ...) < ((t2 , s2) , ...)
      ->  llcorner Add l r lrcorner ((t1 , Right l n eq s1) , eq1) < ((t2 , Right l n eq s2) , eq2)
    <-StepL  : llcorner l lrcorner ((t1 , s1) , ...) < ((t2 , s2) , ...)
      ->  llcorner Add l r lrcorner ((t1 , Left r s1) , eq1) < ((t2 , Left r s2) , eq2)

    <-Base  :   (eq1 : Add e1 e2 == Add e1 (plugZdown t1 s1)) 
      ->        (eq2 : Add e1 e2 == Add (plugZdown t2 s2) e2)
      ->  llcorner Add e1 e2 lrcorner ((t1 , Right n e1 eq s1) , eq1) < ((t2 , Left e2 s2) , eq2)
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
                -> llcorner e lrcorner y < x -> Acc (llcorner e lrcornerLtOp) y
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
    with unload n (Val n) refl stk
    ... | inj1 (n' , stk')  = inj1 ((n' , stk' ) , ...)
    ... | inj2 v            = inj2 v
\end{code}
We have omitted the second component of the result returned in the
first branch, corresponding to a proof that |plugZup (n' , stk') ==
e|. The crucial lemma that we need to show to complete this proof,
demonstrates that the |unload| function respects our invariant:
\begin{code}
  unload-preserves-plugup  :
    forall (n : Nat) (e : Expr) (eq : eval e == x) (s : Stack2) (z : ZipperType)
    -> unload n e eq s == inj1 z
    -> forall (e' : Expr) -> plugup e s == e' -> plugZup z == e'
\end{code}

Finally, we can define the theorem stating that the |step| function always
returns a smaller configuration:
%
\begin{code}
  step-<  : forall (e : Expr) -> (z z' : Zipperup e) -> step e z == inj1 z'
          -> llcorner e lrcorner Zipperup-to-Zipperdown z' < Zipperup-to-Zipperdown z
\end{code}
%
Proving this statement directly is tedious, as there are many cases to cover and
the expression |e| occurring in the types makes it difficult to identify and
prove lemmas covering the individual cases. Therefore, we instead define another
relation over non type-indexed configurations directly, and prove that there
is an injection between both relations under suitable assumptions:

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

Thus to complete the previous theorem, it is sufficient to show that the function
|unload| delivers a smaller |ZipperType|:

\begin{code}
  unload-<  : forall (n : Nat) (s : Stack2) (e : Expr) (s' : Stack2)
            -> unload n (Val n) refl s == inj1 (t' , s')
            -> (t' , reverse s') < (n , reverse s)
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
       = rec e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))

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
  rec-correct  : forall (e : Expr) -> (z : Zipperup e)
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
  unload-correct  :  forall (n : Nat) (e : Expr) (eq : eval e == n) (s : Stack2)
                       forall (m : Nat) -> unload n e eq s == inj2 m 
                       -> eval (plugup e s) == m
\end{code}
This proof follows immediately by induction over |s : Stack2|.

The main correctness theorem now states that |eval| and
|tail-rec-eval| are equal for all inputs:
\begin{code}
  correctness : forall (e : Expr) -> eval e == tail-rec-eval e
  correctness e with load e Top
  ... | inj1 z = rec-correct e (z , ...) (<-WF e z)
  ... | inj2 _ = bot-elim ...
\end{code}
This finally completes the definition and verification of a
tail-recursive evaluator. 
%} end of intro.fmt

\section{A generic tail-recursive traversal}
\label{sec:generic}
%{ begining of generic.fmt
The previous section showed how to prove that our hand-written tail-recursive
evaluation function was both terminating and equal to our original evaluator.
In this section, we will show how we can generalize this construction to compute
a tail-recursive equivalent of \emph{any} function that can be written as a fold
over a simple algebraic datatype.
In particular, we generalize the following:
\begin{itemize}
  \item The kind of datatypes, and their associated fold, that our tail-recursive
    evaluator supports, \Cref{sec:universe}.
  \item The type of configurations of the abstract machine that computes the
    generic fold, \Cref{sec:dissection,sec:genconf}.
  \item The functions |load| and |unload| such that they work over our choice of generic
    representation, \Cref{subsec:onestep}.
  \item The `smaller than' relation to handle generic configurations, and
    its well-foundedness proof, \Cref{subsec:rel-gen}.
  \item The tail-recursive evaluator, \Cref{sec:genmachine}.
  \item The proof that the generic tail-recursive function is correct, \Cref{sec:correct-gen}.
\end{itemize}
%include generic.fmt
Before we can define any such datatype generic constructions, however, we need
to fix our universe of discourse.

\subsection{The \emph{regular} universe}
\label{sec:universe}

In a dependently typed programming language such as Agda, we can
represent a collection of types closed under certain operations as a
\emph{universe}~\cite{altenkirch-mcbride,martin-loef}, that is, a data
type |U : Set| describing the inhabitants of our universe together
with its semantics, |el : U -> Set|, mapping each element of |U| to
its corresponding type. We have chosen the following universe of
\emph{regular} types~\cite{morris-regular, noort-regular}:
\begin{code}
  data Reg : Set1 where
    Zero  : Reg
    One   : Reg
    I     : Reg
    K     : (A : Set) -> Reg
    O+Op  : (R Q : Reg)  -> Reg
    O*Op  : (R Q : Reg) -> Reg
\end{code}
Types in this universe are formed from the empty type (|Zero|), unit type
(|One|), and constant types (|K A|); the |I| constructor is used to refer to
recursive subtrees. Finally, the universe is closed under both coproducts
(|O+Op|) and products (|O*Op|). We could represent the \emph{pattern} functor
corresponding to the \AD{Expr} type in this universe as follows:
\begin{code}
  expr : Reg
  expr = K Nat O+ (I O* I)
\end{code}
Note that as the constant functor |K| takes an arbitrary type |A| as its
argument, the entire datatype lives in |Set1|. This could easily be remedied by
stratifying this universe explicitly and parametrising our development by a base
universe.
  
We can interpret the inhabitants of |Reg| as a functor of type |Set -> Set|:
\begin{code}
  interp : Reg -> Set -> Set
  interpl Zero interpr X       = Bot
  interpl One interpr X        = Top
  interpl I interpr X          = X
  interpl (K A) interpr X      = A
  interpl (R O+ Q) interpr X   = interpl R interpr X U+ interpl Q interpr X
  interpl (R O* Q) interpr X   = interpl R interpr X * interpl Q interpr X
\end{code}
To show that this interpretation is indeed functorial, we define the
following |fmap| operation:
\begin{code}
  fmap : (R : Reg) -> (X -> Y) -> interpl R interpr X -> interpl R interpr Y
  fmap Zero f Empty
  fmap One  f tt            = tt
  fmap I f x                = f x
  fmap (K A) f x            = x
  fmap (R O+ Q) f (inj1 x)  = inj1 (fmap R f x)
  fmap (R O+ Q) f (inj2 y)  = inj2 (fmap Q f y)
  fmap (R O* Q) f (x , y)   = fmap R f x , fmap Q f y
\end{code}
Finally, we can tie the recursive knot, taking the least fixpoint of the functor
associated with the elements of our universe:
\begin{code}
  data mu (R : Reg) : Set where
    In : interpl R interpr (mu R) -> mu R
\end{code}
Next, we can define a \emph{generic} fold, or \emph{catamorphism}, to
work on the inhabitants of the regular universe. For each code |R :
Reg|, the |cata R| function takes an \emph{algebra} of type |interpl R
interpr X -> X| as argument. This algebra assigns semantics to the
`constructors' of |R|. Folding over a tree of type |mu R| corresponds
to recursively folding over each subtree and assembling the results
using the argument algebra:
\begin{spec}
  cataNT : (R : Reg) -> (interpl R interpr X -> X) -> mu R -> X
  cata R alg (In r) = alg (fmap R cataN R alg) r)
\end{spec}
Unfortunately, Agda's termination checker does not accept this definition. The
problem, once again, is that the recursive calls to |cata| are not made to
structurally smaller trees, but rather |cata| is passed as an argument to the
higher-order function |fmap|.

To address this, we fuse the |fmap| and |cata| functions into a single
|mapFold| function~\cite{norell-notes}:
\begin{code}
  mapFold : (R Q : Reg) -> (interpl Q interpr X -> X) -> interpl R interpr (mu Q) -> interpl R interpr X
  mapFold Zero     Q alg Empty
  mapFold One      Q alg tt        = tt
  mapFold I        Q alg (In x)    = alg (mapFold Q Q alg x)
  mapFold (K A)    Q alg x         = x
  mapFold (R O+ Q) P alg (inj1 x)  = inj2 (mapFold R P alg x)
  mapFold (R O+ Q) P alg (inj2 y)  = inj2 (mapFold Q P alg y)
  mapFold (R O* Q) P alg (x , y)   = mapFold R P alg x , mapFold Q P alg y
\end{code}
We can now define |cata| in terms of |mapFold| as follows:
\begin{code}
  cata : (R : Reg) (interpl R interpr X -> X) -> mu R -> X
  cata R alg (In r) = mapFold R R alg r
\end{code}
This definition is indeed accepted by Agda's termination checker.

\paragraph{Example}
We can now revisit our example evaluator from the introduction. To
define the evaluator using the generic |cata| function, we instantiate
the catamorphism to work on the expressions and pass the desired algebra:
\begin{code}
  eval : mu expr -> Nat
  eval = cata expr phi
    where  phi : interpl expr interpr Nat -> Nat
           phi (inj1 n)         = n         
           phi (inj2 (n , n'))  = n + n'
\end{code}

In the remainder of this paper, we will develop an alternative
traversal that maps any algebra to a tail-recursive function that is
guaranteed to terminate and produce the same result as
the corresponding call to |cata|.

\subsection{Dissection}
\label{sec:dissection}

As we mentioned in the previous section, the configurations of our
abstract machine from the introduction are instances of McBride's
dissections~\citeyearpar{dissection}. We briefly recap this
construction, showing how to calculate the type of abstract machine
configurations for any type in our universe. The key definition,
|nabla|, computes a bifunctor for each element of our universe:
\begin{code}
  nabla : (R : Reg) -> (Set -> Set -> Set)
  nabla Zero      X Y  = Bot
  nabla One       X Y  = Bot
  nabla I         X Y  = Top
  nabla (K A)     X Y  = Bot
  nabla (R O+ Q)  X Y  = nabla R X Y U+ nabla Q X Y
  nabla (R O* Q)  X Y   =            (nabla R X Y           * interpl Q interpr Y   )
                        {-"\ "-} U+  (interpl R interpr X   * nabla Q X Y           )
\end{code}
This operation generalizes the zippers, by defining a bifunctor |nabla
R X Y|. You may find it useful to think of the special case, |nabla R
X (mu R)| as a configuration of an abstract machine traversing a tree
of type |mu R| to produce a result of type |X|. The last clause of the
definition of |nabla| is of particular interest: to \emph{dissect} a
product, we either \emph{dissect} the left component pairing it with
the second component interpreted over the second variable |Y|; or we
\emph{dissect} the second component and pair it with the first
interpreted over |X|.

A \emph{dissection} is formally defined as the pair of the one-hole context and
the missing value that can fill the context.
\begin{code}
  Dissection : (R : Reg) -> (X Y : Set) -> Set
  Dissection R X Y = nabla R X Y * Y
\end{code}
We can reconstruct Huet's zipper for generic trees of type |mu R| by
instantiating both |X| and |Y| to |mu R|.

Given a \emph{dissection}, we can define a |plug| operation that
assembles the context and current value in focus to
produce a value of type |interpl R interpr Y|:
\begin{code}
  plug : (R : Reg) -> (X -> Y) -> Dissection R X Y -> interpl R interpr Y
  plug Zero      eta  (Empty , x)
  plug One       eta  (Empty , x)
  plug I         eta  (tt , x)             = x
  plug (K A)     eta  (Empty , x)
  plug (R O+ Q)  eta  (inj1 r , x)         = inj1 (plug R eta (r , x))
  plug (R O+ Q)  eta  (inj2 q , x)         = inj2 (plug Q eta (q , x))
  plug (R O* Q)  eta  (inj1 (dr , q) , x)  = (plug R eta (dr , x) , q)
  plug (R O* Q)  eta  (inj2 (r , dq) , x)  = (fmap R eta r , plug Q eta (dq , x))
\end{code}
In the last clause of the definition, the \emph{dissection} is over the right
component of the pair leaving a value |r : interpl R interpr X| to the left. In
that case, it is only possible to reconstruct a value of type |interpl R interpr Y|, 
if we have a function |eta| to recover |Y|s from |X|s.

In order to ease things later, we bundle a \emph{dissection} together with the
functor to which it \emph{plug}s as a type-indexed type.

\begin{code}
  data IxDissection (R : Reg) (X Y : Set) (eta : X -> Y) (tx : interpl R interpr Y) : Set where
    prodOp : (d : Dissection R X Y) -> plug R eta d == tx -> IxDissection R X Y eta tx 
\end{code}

\subsection{Generic configurations}
\label{sec:genconf}

While the \emph{dissection} computes the bifunctor \emph{underlying}
our configurations, we still need to take a fixpoint of this
bifunctor.  Each configuration consists of a list of
\emph{dissections} and the current subtree in focus. To the left of
the current subtree in focus, we store the partial results arising
from the subtrees that we have already processed; on the right, we
store the subtrees that still need to be visited.

%{
%format Stack2 = "\AD{Stack\ensuremath{^{+}}}"
As we did for the |Stack2| datatype from the introduction, we also
choose to store the original subtrees that have been visited and their
corresponding correctness proofs:
\begin{code}
 record Computed (R : Reg) (X : Set) (alg : interpl R interpr X -> X) : Set where
    constructor _,_,_
    field
      Tree   : mu R
      Value  : X
      Proof  : catamorphism R alg Tree == Value

\end{code}
\begin{code}
  Stack : (R : Reg) -> (X : Set) -> (alg : interpl R interpr X -> X) -> Set
  Stack R X alg = List (nabla R (Computed R X alg) (mu R))
\end{code}
A \emph{stack} is a list of \emph{dissections}. To the left we have
the |Computed| results; to the right, we have the subtrees of type |mu
R|. Note that the |Stack| datatype is parametrised by the algebra
|alg|, as the |Proof| field of the |Computed| record refers to it.
%}

As we saw in \Cref{sec:basic-correctness}, we can define two
different \emph{plug} operations on these stacks:
\begin{code}
  plug-mudown  : (R : Reg) -> {alg : interpl R interpr X -> X}
               -> mu R -> Stack R X alg -> mu R
  plug-mudown R t []         = t
  plug-mudown R t (h :: hs)  = In (plug R Computed.Tree h (plug-mudown R t hs))

  plug-muup  : (R : Reg) -> {alg : interpl R interpr X -> X}
             -> mu R -> Stack R X alg -> mu R
  plug-muup R t []         = t
  plug-muup R t (h :: hs)  = plug-muup R (In (plug R Computed.Tree h t)) hs
\end{code}
Both functions use the projection, |Computed.Tree|, as an argument to
|plug| to extract the subtrees that have already been processed.

To define the configurations of our abstract machine, we are
interested in \emph{any} path through our initial input, but want to
restrict ourselves to those paths that lead to a leaf. But what
constitutes a leaf in this generic setting?

To describe leaves, we introduce the following predicate |NonRec|,
stating when a tree of type |interpl R interpr X| does not refer to
the variable |X|, that will be used to represent recursive subtrees:
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
As an example, in the pattern functor for the \AD{Expr} type, |K Nat O+ (I O* I)|,
terms built using the left injection are non-recursive: 
\begin{code}
Val-NonRec : forall (n : Nat) -> NonRec (K Nat O+ (I O* I)) (inj1 n)
Val-NonRec : n = NonRec-+1 (K Nat) (I O* I) n (NonRec-K Nat n)
\end{code}
This corresponds to the idea that the constructor |Val| is a leaf in a tree of
type |Expr|. 

On the other hand, we cannot prove the predicate |NonRec| for terms using the
right injection. The occurences of recursive positions disallow us from framing 
the proof (The type |NonRec| does not have a constructor such as |NonRec-I : (x : X) -> NonRec I x|).

This example also shows how `generic` leaves can be recursive. As long as the
recursion only happens in the functor layer (code |O+|) and not in the fixpoint
level (code |I|).

Crucially, any non-recursive subtree is independent of |X| -- as is
exhibited by the following coercion function:
%
\begin{code}
  coerce : (R : Reg) -> (x : interpl R interpr X) -> NonRec R x -> interpl R interpr Y  
\end{code}
%
Whose definition is not worth including as it follows directly by induction over
the predicate.

We can now define the notion of leaf generically, as a substructure
without recursive subtrees:
\begin{code}
  Leaf : Reg -> Set -> Set
  Leaf R X = Sigma (interpl R interpr X) (NonRec R)
\end{code}

Just as we saw previously, a configuration is now given by the current
leaf in focus and the stack, given by a dissection, storing partial
results and unprocessed subtrees:
\begin{code}
  Zipper : (R : Reg) -> (X : Set) -> (alg : interpl R interpr X -> X) -> Set
  Zipper R X alg = Leaf R X * Stack R X alg
\end{code}

Finally, we can recompute the original tree using a |plug| function as before:
\begin{code}
  plugZ-mudown  : (R : Reg) {alg : interpl R interpr X -> X} 
                -> Zipper R X alg -> mu R ->  Set
  plugZ-mudown R ((l , isl) , s) t = plug-mudown R (In (coerce l isl)) s t
\end{code}
Note that the |coerce| function is used to embed a leaf into a larger
tree. A similar function can be defined for the `bottom-up' zippers,
that work on a reversed stack.

\subsection{One step of a catamorphism}
\label{subsec:onestep}

%{
%format load = "\AF{load}"
%format unload = "\AF{unload}"
In order to write a tail-recursive catamorphism, we start by defining the
generic operations that correspond to the functions |load| and |unload| given in
the introduction (\Cref{sec:basics}).
%}
\paragraph{Load}
The function |load| traverses the input term to find its
leftmost leaf. Any other subtrees the |load| function encounters are stored
on the stack. Once the |load| function encounters a constructor without subtrees,
it is has found the desired leaf.

We write |load| by appealing to an ancillary definition |first-cps|, that uses
continuation-passing style
to keep the definition tail-recursive and obviously structurally recursive.
If we were to try to define |load| by recursion directly, 
we would need to find the leftmost subtree and recurse on it --
but this subtree may not be obviously syntactically smaller.

The type of our |first-cps| function is daunting at first:
\begin{code}
first-cps : (R Q : Reg) {alg : interpl Q interpr X -> X}
          ->  interpl R interpr (mu Q)
          ->  (nabla R (Computed Q X alg) (mu Q) -> (nabla Q (Computed Q X alg) (mu Q)))
          ->  (Leaf R X -> Stack Q X alg -> Zipper Q X alg U+ X)
          ->  Stack Q X alg
          ->  Zipper Q X alg U+ X
\end{code}
The first two arguments are codes of type |Reg|. The code |Q|
represents the datatype for which we are defining a traversal; the
code |R| is the code on which we pattern match. In the initial call to
|first-cps| these two codes will be equal. As we define our function,
we pattern match on |R|, recursing over the codes in (nested) pairs or
sums -- yet we still want to remember the original code for our data
type, |Q|.

The next argument of type |interpl R interpr (mu Q)| is the data we
aim to traverse. Note that the `outermost' layer is of type |R|, but
the recursive subtrees are of type |mu Q|. The next two arguments are
two continuations: the first is used to gradually build the
\emph{dissection} of |R|; the second continues on another branch once
one of the leaves have been reached. The last argument of type |Stack
Q X alg| is the current stack. The entire function will compute the
initial configuration of our machine of type |Zipper Q X alg| \footnote{As in the introduction, we use a sum type |U+| to align its type with that of |unload|.}:

\begin{code}
load  : (R : Reg) {alg : interpl R interpr X -> X} -> mu R
      -> Stack R X alg -> Zipper R X alg U+ X
load R (In t) s = first-cps R R t id (lambda l -> inj1 . prodOp l) s
\end{code}

We shall fill the definition of |first-cps| by cases.  The clauses for the base
cases are as expected. In |Zero| there is nothing to be done. The |One| and
|K A| codes consist of applying the second continuation to the tree and the \emph{stack}.
\begin{code}
  first-cps Zero Q Empty _
  first-cps One  Q x k f s    = f (tt , NonRec-One) s
  first-cps (K A) Q x k f s   = f (x , NonRec-K A x) s
\end{code}
The recursive case, constructor |I|, corresponds to the occurrence of a subtree.
The function |first-cps| is recursively called over that subtree with the stack
incremented by a new element that corresponds to the \emph{dissection} of the
functor layer up to that point. The second continuation is replaced with the
initial one.
\begin{code}
  first-cps I Q (In x) k f s  = first-cps Q Q x id (lambda z  -> inj1 . prodOp z) (k tt :: s)
\end{code}
In the coproduct, both cases are similar, just having to account for the
use of different constructors in the continuations.
\begin{code}
  first-cps (R O+ Q) P (inj1 x) k f s = first-cps R P x  (k . inj1) cont s
    where cont (l , isl) = f ((inj1 l) , NonRec-+1 R Q l isl)
  first-cps (R O+ Q) P (inj2 y) k f s = first-cps Q P y  (k . inj2) cont s
    where cont (l , isl) = f ((inj1 l) , NonRec-+2 R Q l isl)
\end{code}
The interesting clause is the one that deals with the product. First the
function |first-cps| is recursively called on the left component  of the pair
trying to find a subtree to recurse over. However, it may be the case that there
are no subtrees at all, thus it is passed as the first continuation a call to
|first-cps| over the right component of the product.  In case the
continuation fails to to find a subtree, it returns the leaf as it is.
\begin{code}
  first-cps (R O* Q) P (r , q) k f s  = first-cps R P r  (k . inj1 . (_, q)) cont s
    where cont (l , isl) = first-cps Q P q (k . inj2 . prodOp (coerce l isl)) cont'
      where cont' (l' , isl') = f (l , l') (NonRec-* R Q l l' isl isl')
\end{code}

\paragraph{Unload}

Armed with |load| we turn our attention to |unload|. First of all, it is
necessary to define an auxiliary function, |right|, that given a
\emph{dissection} and a value (of the type of the left variables), either finds
a dissection |Dissection R X Y| or it shows that  there are no occurrences of
the variable left. In the latter case, it returns the functor interpreted over
|Y|, | interpl R interpr Y|.

\begin{code}
  right  : (R : Reg) -> nabla R X Y -> X -> interpl R interpr X U+ Dissection R X Y
\end{code}

Its definition is simply by induction over the code |R|, with the special case
of the product that needs to use another ancillary definition to look for the
leftmost occurrence of the variable position within |interpl R interpr X|.

The function |unload| is defined by induction over the \emph{stack}. If the
\emph{stack} is empty the job is done and a final value is returned. In case the
\emph{stack} has at least one \emph{dissection} in its head, the function
|right| is called to check whether there are any more holes left. If there are
none, a recursive call to |unload| is dispatched, otherwise, if there is still a subtree to be
processed the function |load| is called.

\begin{code}
  unload : (R : Reg)
         -> (alg : interpl R interpr X -> X)
         -> (t : mu R) -> (x : X) -> catamorphism R alg t == x
         -> Stack R X alg
         -> Zipper R X alg U+ X
  unload R alg t x eq []        = inj2 x
  unload R alg t x eq (h :: hs) with right R h (t , x , eq)
  unload R alg t x eq (h :: hs) | inj1 r with compute R R r
  ... | (rx , rr) , eq'  = unload R alg (In rp) (alg rx) (cong alg eq') hs
  unload R alg t x eq (h :: hs) | inj2 (dr , q) = load R q (dr :: hs)
\end{code}

When the function |right| returns a |inj1| it means that there are not any
subtrees left in the \emph{dissection}. If we take a closer look, the type of
the |r| in |inj1 r| is | interpl R interpr (Computed R X alg) |. The functor
|interpl R interpr| is storing at its variable positions both values, subtrees and proofs.

However, what is needed for the recursive call is: first, the functor
interpreted over values, | interpl R interpr X|, in order to apply the algebra;
second, the functor interpreted over subtrees, | interpl R interpr (mu R)|, to
keep the original subtree where the value came from; Third, the proof that the
value equals to applying a |catamorphism| over the subtree.  The function
|compute| massages |r| to adapt the arguments for the recursive call to |unload|.

\subsection{Relation over generic configurations}
\label{subsec:rel-gen}

We can engineer a \emph{well-founded} relation over elements of type |Zipperdown
t|, for some concrete tree |t : mu R|, by explicitly separating the functorial layer
from the recursive layer induced by the fixed point. At the functor level, we
impose the order over \emph{dissection}s of |R|, while at the fixed point level
we define the order by induction over the \emph{stack}s.

To reduce clutter in the definition, we give a non type-indexed
relation over terms of type |Zipper|. We can later use the same technique as in
\Cref{sec:basic-assembling} to recover a fully type-indexed relation over
elements of type |Zipperdown t| by requiring that the \emph{zipper}s respect the
invariant, |plugZ-mudown z == t|. The relation is defined by induction over the
|Stack| part of the |zipper|s as follows.
\begin{code}
  data <ZOp : Zipper R X alg -> Zipper R X alg -> Set where
    Step  :  (t1 , s1) <Z (t2 ,  s2) -> (t1 , h :: s1) <Z (t2 , h  :: s2)

    Base  : plugZ-mudown R (t1 , s1) == e1 -> plugZ-mudown R (t2 , s2) == e1
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
by the configuration denotes different subtrees of the same node. In that case, the
relation we are defining relies on an auxiliary relation |<NablaOp| that orders
\emph{dissections} of type |Dissection R (Computed R X alg) (mu R)|.
\end{itemize}

We can define this relation on dissections directly, without having to
consider the recursive nature of our datatypes. We define the
required relation over dissections interpreted on \emph{any} sets |X|
and |Y| as follows:
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
The idea is that we order the elements of a \emph{dissection} in a
left-to-right fashion.  All the constructors except for |base-*|
simply follow the structure of the dissection. To define the base case,
|base-*|, recall that
the \emph{dissection} of the product of two functors, |R O* Q|, has two possible
values. It is either a term of type |nabla R X Y * interpl Q interpr Y|, such as
|inj1 (dr , q)| or a term of type |interpl R interpr X * nabla Q X Y| like |inj2
(r , dq)|. The former denotes a position  in the left component of the
pair while the latter denotes a position in the right component.
The |base-*| constructor states that positions in right are smaller than
those in the left.

This completes the order relation on configurations; we still need to prove
our relation is \emph{well-founded}.
To prove this, we write a type-indexed version of each
relation. The first relation, |<ZOp|, has to be type-indexed by the tree of
type |mu R| to which both \emph{zipper} recursively plug through
|plugZ-mudown|. The auxiliary relation, |<NablaOp|, needs to be type-indexed by
the functor of type | interpl R interpr X | to which both \emph{dissections}
|plug|:

\begin{code}
  data IxLt {X Y : Set} {eta : X -> Y} :  (R : Reg) -> (tx : interpl R interpr Y) 
             -> IxDissection R X Y eta tx -> IxDissection R X Y eta tx -> Set where


  data IxLtdown {X : Set} (R : Reg) {alg : interpl R interpr X -> X}  : (t : mu R) 
             -> Zipperdown R X alg t -> Zipperdown R X alg t -> Set where
\end{code}

The proof of \emph{well-foundedness} of |IxLtdown| is a straightforward generalization
of proof given for the example in \Cref{subsec:relation}. 
The full proof of the following statement can found in the accompanying code:
\begin{code}
  <Z-WF : (R : Reg)  -> (t : mu R) -> Well-founded (llcorner R lrcornerllcorner t lrcornerIxLtdown)
\end{code}

\subsection{A generic tail-recursive machine}
\label{sec:genmachine}

We are now ready to define a generic tail-recursive machine. To do so we
now assemble the generic machinery we have defined so far. We follow the 
same outline as in \Cref{sec:basic-assembling}.

The first point is to build a wrapper around the function |unload| that performs
one step of the \emph{catamorphism}. The function |step| statically enforces
that the input tree remains the same both in its argument and in its result.

\begin{code}
  step  : (R : Reg) -> (alg : interpl R interpr X -> X) -> (t : mu R)
        -> Zipperup R X alg t -> Zipperup R X alg t U+ X
\end{code}
We omit the full definition. The function |step| performs a call to |unload|,
coercing the leaf of type |interpl R interpr X| in the |Zipperdown| argument to
a generic tree of type |interpl R interpr (mu R)|.

We show that |unload| preserves the invariant, by proving the following lemma:
\begin{code}
  unload-preserves  : forall (R : Reg) {alg : interpl R interpr X -> X}
                    -> (t : mu R) (x : X) (eq : catamorphism R alg t == x) (s : Stack R X alg)
                    -> (z : Zipper R X alg)
                    -> forall  (e : mu R) -> plug-muup R t s == e 
                              -> unload R alg t x eq s == inj1 z -> plug-muup R z == e
\end{code}

Next, we show that applying the function |step| to a
configuration of the abstract machine produces a smaller configuration.
As the function |step| is a wrapper over the |unload| function, we only have
to prove that the property holds for |unload|.

The |unload| function does two things. First, it calls the function
|right| to check whether the \emph{dissection} has any more recursive subtrees
to the right that still have to be processed.
It then dispatches to either |load|, if there is, or recurses if case there is
not.  When there is a hole left, a new \emph{dissection} is returned by |right|.
Thus showing that the new configuration is smaller amounts to show that the
\emph{dissection} returned by |right| is smaller by |<NablaOp|.  This amounts to
proving the following lemma:
\begin{code}
  right-<  : right R dr (t , y , eq) == inj2 (dr' , t')
           -> llcorner R lrcorner ((dr' , t')) <Nabla ((dr , t)) 
\end{code}
We have simplified the type signature, leaving out the universally
quantified variables and their types. 

Extending this result to show that the function |unload|
delivers a smaller value are straightforward. By
induction over the input stack we check if the
traversal is done or not. If it is not yet done, there is
at least one dissection in the top of the stack.  The
function |right| applied to that element returns either a smaller
dissection or a tree with all values on the leaves. If we obtain a new dissection,
we use the |right-<| lemma; in the latter case, we continue by induction
over the stack.
In this fashion, we can prove the following statement that
our traversal decreases:
\begin{code}
  step-<  : (R : Reg) (alg : interpl R interpr X -> X) -> (t : mu R)
          -> (z1 z2 : Zipperup R X alg t)
          -> step R alg t z1 == inj1 z2 -> llcorner R lrcornerllcorner t lrcorner z2 <ZOp z1
\end{code}

Finally, we can write the \emph{tail-recursive machine}, |tail-rec-cata|, as the
combination of an auxiliary recursor over the accessibility predicate and a top-level
function that initiates the computation with suitable arguments:
\begin{code}
  rec  : (R : Reg) (alg : interpl R interpr X -> X) (t : mu R) 
       -> (z : Zipperup R X alg t) 
       -> Acc (llcorner R lrcornerllcorner t lrcornerIxLtdown ) (Zipperup-to-Zipperdown z) -> X
  rec R alg t z (acc rs) with step R alg t z | inspect (step R alg t) z
  ... | inj1 z' |  [ Is  ] = rec R alg t z' (rs z' (step-< R alg t z z' Is))
  ... | inj2 x  |  [ _   ] = x

  tail-rec-cata : (R : Reg) -> (alg : interpl R interpr X -> X) -> mu R -> X
  tail-rec-cata R alg x  with load R alg x []
  ... | inj1 z = rec R alg (z , ...) (<Z-WF R z)
\end{code}

\subsection{Correctness, generically}
\label{sec:correct-gen}
%{
%format tail-rec-eval = "\AF{tail-rec-eval}"
To prove our tail-recursive evaluator produces the same output as the catamorphism
is straight-forward. As we did in the |tail-rec-eval| example
(\Cref{sec:basic-correctness}), we perform induction over the accessibility
predicate in the auxiliary recursor. In the base case, when the function |step|
returns a ground value of type |X|, we have to show that such value is is the
result of applying the \emph{catamorphism} to the input. Recall that |step| is a
wrapper around |unload|, hence it suffices to prove the following lemma:
\begin{code}
  unload-correct  : forall  (R : Reg) (alg : interpl R interpr X -> X)
                            (t : mu R) (x : X) (eq : catamorphism R alg t == x)
                            (s : Stack R X alg) (y : X)  
                  -> unload R alg t x eq s == inj2 y
                  -> ∀ (e : mu R) -> plug-muup R t s == e -> catamorphism R alg e == y
\end{code}
Our generic correctness result is an immediate consequence:
\begin{code}
  correctness  : forall (R : Reg) (alg : interpl R interpr X -> X) (t : mu R)
               -> catamorphism R alg t == tail-rec-cata R alg t
\end{code}

\subsection{Example}
\label{subsec:example-gen}

To conclude, we show how to generically implement the example from the
introduction (\Cref{sec:intro}), and how the generic construction gives us a
\emph{correct} tail-recursive machine for free. First, we recap the \emph{pattern} 
functor underlying the type |Expr|:
\begin{code}
  expr : Reg
  expr = K Nat O+ (I O* I)
\end{code}
The |Expr| type is then isomorphic to tying the knot over |expr|:
\begin{code}
  ExprG : Set
  ExprG = mu expr
\end{code}
The function |eval| is equivalent to instantiating the
\emph{catamorphism} with an appropriate algebra:
\begin{code}
  alg : expr Nat -> Nat
  alg (inj1 n)          = n
  alg (inj2 (e1 , e2))  = e1 + e2

  eval : ExprG -> Nat
  eval = cata expr alg
\end{code}
Finally, a tail-recursive machine \emph{equivalent} to the one we derived in \Cref{sec:basic-assembling},
|tail-rec-eval|, is given by:
\begin{code}
  tail-rec-evalG : ExprG -> Nat
  tail-rec-evalG = tail-rec-cata expr alg
\end{code}
%} end of generic.fmt

\section{Discussion}
\label{sec:discussion}


There is a long tradition of calculating abstract machines from an evaluator,
dating back as far as early work on the abstract machines for the evaluation of
lambda calculus terms~\cite{landin}. In particular, Danvy\cite{danvy-II,
danvy-I} has published many examples showing how abstract machines arise from
defunctionalizing an interpreter written in continuation-passing style. This
work in turn, inspired McBride's work on dissections~\citeyearpar{dissection},
that defines the key constructions on which this paper builds. McBride's work,
however, does not give a proof of termination or correctness.

The universe of regular types used in this paper is somewhat restricted: we
cannot represent mutually recursive types~\cite{mutual}, nested data
types~\cite{nested}, indexed families~\cite{dybjer-inductive}, or
inductive-recursive types~\cite{induction-recursion}. Fortunately, there is a
long tradition of generic programming with universes in Agda, arguably dating
back to~\citet{martin-loef}. It would be worthwhile exploring how to extend our
construction to more general universes, such as the context-free
types~\cite{morris}, containers~\cite{containers,indexed-containers}, or the
`sigma-of-sigma' universe~\cite{power-of-pi,levitation}. Doing so would allow us
to exploit dependent types further in the definition of our evaluators. For
example, we might then define an interpreter for the well-typed lambda terms and
derive a tail recursive evaluator automatically, rather than verifying the
construction by hand~\cite{krivine}.

The termination proof we have given defines a well-founded relation and shows
that this decreases during execution. There are other techniques for writing
functions that are not obviously structurally recursive, such as the
Bove-Capretta method~\cite{bove}, partiality monad~\cite{partiality}, or
coinductive traces~\cite{nakata}. In contrast to the well-founded recursion used
in this paper, however, these methods do not yield an evaluator that is directly
executable, but instead defer the termination proof. Given that we can -- and
indeed have -- shown termination of our tail-recursive abstract machines, the
abstract machines are executable directly in Agda.

One drawback of our construction is that the stacks now not only store the value
of evaluating previously visited subtrees, but also records the subtrees
themselves. Clearly this is undesirable for an efficient implementation. It
would be worth exploring if these subtrees may be made computationally
irrelevant -- as they are not needed during execution, but only used to show
termination and correctness. One viable approach might be porting the
development to Coq, where it is possible to make a clearer distinction between
values used during execution and the propositions that may be erased.


%% Acknowledgments
%\begin{acks}                            %% acks environment is optional
\fixme{Thank reviewers in acks in final version}
%\end{acks}

%% Bibliography
\bibliography{main}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End:


