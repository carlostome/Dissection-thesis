\documentclass[sigplan,10pt]{acmart}

%include preamble.tex
%include paper.fmt

% fontsize of code snippets
\renewcommand\hscodestyle{%
   \setlength\leftskip{0.1cm}%
   \footnotesize
}

\begin{document}

\title{Dissection: terminating and correct}

\author{Carlos Tom\'e Corti\~nas}
\affiliation{
  \department{Department of Information and Computing Sciences}
  \institution{University of Utrecht}
  \country{The Netherlands}
}
\email{c.tomecortinas@@students.uu.nl}

\author{Wouter Swierstra}
\affiliation{
  \department{Department of Information and Computing Sciences}
  \institution{University of Utrecht}
  \country{The Netherlands}
}
\email{w.s.swierstra@@uu.nl}


\begin{abstract}
  Folds are a useful abstraction. Yet they are not tail recursive. Writing tail
  recursive functions by hand is boring/hard. This paper attempts to nail down
  the generic construction that produces the tail recursive counterpart of any
  recursive function defined as a fold. This allows programmers to work at a
  high-level of abstraction (folds) without sacrificing performance (tail
  recursion). \fixme{Polish abstract}
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
expression data type, written in the programming
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

Unfortunately, not all in the garden is rosy. The operator |plusOp|
needs both of its parameters to be fully evaluated before it can
reduce further. As a result, the size of the
stack used during execution grows linearly with the size of the input,
potentially leading to a stack overflow on large inputs.

To address this problem, we can manually rewrite the evaluator to be
\emph{tail recursive}. Modern compilers typically map tail recursive
functions to machine code that runs in constant memory. To write such
a tail recursive function, we need to introduce an explicit stack
storing both intemediate results and the subtrees that have not yet
been evaluated.

\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

We can define a tail-recursive evaluation function by means of a
pair of mutually recursive functions, |load| and |unload|. The |load|
function traverses the expressions, pushing subtrees on the
stack; the |unload| function unloads the stack, while accumulating a
(partial) result.

\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unloadN (v' + v) stk
    unload v   (Left r stk)    = loadN r (Right v stk)
\end{code}

We can now define a tail recursive version of |eval| by
calling |load| with an initially empty stack:

\begin{code}
  tail-rec-eval : Expr → Nat
  tail-rec-eval e = load e Top
\end{code}

Implementing this tail recursive evaluator has come at a price: Agda's
termination checker flags the |load| and |unload| functions as
potentially non-terminating by highlighting them
\nonterm{orange}. Indeed, in the very last clause of the |unload|
function a recursive call is made to arguments that are not
syntactically smaller. Furthermore, it is not clear at all that the
tail recursive evaluator produces the same result as our original
one. It is precisely these issues that this paper tackles
by making the following novel contributions:
\fixme{be consistent naming tail recursive}
\begin{itemize}
\item We give a verified proof of termination of |tail-rec-eval| using
  a carefully chosen \emph{well-founded relation}
  (Section~\ref{sec:basics}--\ref{sec:wf-example}). After redefining |tail-rec-eval| using
  this relation, we can prove the two evaluators equal in Agda.
\item We generalize this relation and its corresponding proof of
  well-foundedness, inspired by
  \citeauthor{dissection}'s~ work on
  \emph{dissections}~\cite{dissection}, to show how to calculate an abstract machine
  from an algebra. To do so, we define a universe of algebraic data
  types and a generic fold operation
  (Section~\ref{sec:universe}). Subsequently we show how to turn any
  structurally recursive function defined using a fold into its tail
  recursive counterpart.
\item Finally, we present how our proofs of termination and semantics
  preservation from our example are generalized to the generic fold
  (Section~\ref{sec:correctness}).
\end{itemize}
Together these results give a verified function that computes a tail
recursive traversal from any algebra for any algebraic data type.
All the constructions and proofs presented in this paper have been
implemented in and checked by Agda. The corresponding code is freely
available online.\footnote{\url{https://github.com/carlostome/Dissection-thesis}}


\section{Termination and tail-recursion}
\label{sec:basics}
Before tackling the generic case, we will present the termination
and correctness proof for the tail recursive evaluator presented in
the introduction in some detail.

The problematic call for Agda's termination checker is the last clause
of the |unload| function, that calls |load| on the expression stored
on the top of the stack. At this point, there is no reason to believe
that the expression on the top of the stack is structurally smaller in
any way. Indeed, if we were to redefine |load| as follows:
\begin{code}
    load (Add e1 e2)  stk = load e1 (Left (f e2) stk)
\end{code}
we might use some function |f : Expr -> Expr| to push \emph{arbitrary}
expressions on the stack, potentially leading to non-termination.

From the definition of |load|, however, it is clear that we only ever
push subtrees of the input on the stack. As a result, every node in
the original tree is visited at twice during the execution: first when
the function |load| traverses the tree, until it finds the leftmost
leaf; second when |unload| inspects the stack in searching of an
unevaluated subtree. This process is depicted in
Figure~\ref{fig:load-unload}.

\begin{figure}
  \centering
  \input{figures/figure1}
  \caption{Traversing a tree with |load| and |unload|}
  \label{fig:load-unload}
\end{figure}

As there are finitely many nodes on a tree, the depicted traversal
using |load| and |unload| must terminate -- but how can we convince
Agda's termination checker of this?

As a first approximation, we will revise the definitions of |load| and
|unload|. Rather than consuming the entire input in one go with a pair
of mutually recursive functions, we begin by defining |load| as follows:
\begin{code}
  load : Expr -> Stack -> Nat * Stack
  load (Val n)      stk = (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)
\end{code}
Rather than call |unload| upon reaching a value, we return the current
stack and the value of the leftmost leaf.

The |unload| function is defined by recursion over the stack as
before, but with one crucial difference. Instead of always returning the
final result, it may also return a new configuration of our abstract
machine, that is, a pair |Nat * Stack|:
\begin{code}
  unload : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload v   Top             = inj2 v
  unload v   (Right v' stk)  = unload (v' + v) stk
  unload v   (Left r stk)    = inj1 (load r (Right v stk))
\end{code}
Both these functions are now accepted by Agda's termination checker as
they are clearly structurally recursive.

We can use both these functions to define the following evaluator:
%{
%format nrec   = "\nonterm{" rec "}"
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top)
    where
      nrec : (Nat * Stack) -> Nat
      rec (n , stk) with unload n stk
      ... | inj1 (n' , stk' ) = nrec (n' , stk')
      ... | inj2 r = r
\end{code}\todo{fix formatting of |stk'|}
%}
Here we use |load| to compute the initial configuration of our machine
-- that is, it finds the leftmost leaf in our initial expression and its associated stack.
We proceed by
repeatedly calling |unload| until it returns a value.  This version of
our evaluator, however, does not pass the termination checker. The new
state, |(n' , stk')|, is not structurally smaller than the initial
state |(n , stk)|. If we work under the assumption that we have a
relation between the states |Nat * Stack| that decreases after every
call to |unload|, and a proof that the relation is well-founded, we
can define the following version of the tail recursive evaluator:
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top) ??1
    where
      rec : (c : Nat * Stack) -> Acc ltOp c -> Nat
      rec (n , stk) (acc rs) with unload n stk
      ... | inj1 (n' , stk') = rec (n' , stk') (rs ??2)
      ... | inj2 v = v
\end{code}
To complete this definition, we still need to define a suitable
well-founded relation |ltOp| between configurations of type |Nat *
Stack| and prove that the calls to |unload| produce `smaller'
states. Finding an appropriate relation and proving its
well-foundedness is the topic of the next section.

\section{Well-founded tree traversals }
\label{sec:wf-example}
The configurations of our abstract machine can be seen as a variation
of Huet's \emph{zippers}~\citeyearpar{huet}. The zipper associated
with an expression |e : Expr| is pair of a (sub)expression of |e| and
its \emph{context}. As demonstrated by~\citet{dissection}, the zippers
can be generalized further to \emph{dissections}, where the values to
the left and right of the current subtree may have different types. It
is precisely this observation that we will exploit when considering
the generic tail recursive traversals in the later sections; for now,
however, we will only rely on the intuition that the configurations of
our abstract machine, given by the type |Nat * Stack|, are an instance
of \emph{dissections}, corresponding to a partially evaluated
expression. These configurations, are more restrictive than
dissections in general. In particular, the configurations presented in
the previous section \emph{only} ever denote a \emph{leaf} in the input
  expression:
%format ZipperType = Config
\begin{code}
  ZipperType : Set
  ZipperType = Nat * Stack
\end{code}
\todo{Zipper is a bad name -- it's not really a zipper. Configuration?
  AbstractMachineState? I've introduced a formatting directive that we
  can change.}

The tail recursive evaluator, |tail-rec-eval| processes the leaves of the input
expression in a left-to-right fashion. The leftmost leaf -- that is the first
leaf found after the initial call to |load| -- is the greatest element; the
rightmost leaf is the smallest. In our example expression from
Section~\ref{sec:intro}, we would number the leaves as follows:

\begin{figure}[h]
  \includegraphics[angle=90]{figure2}
  \caption{Numbered leaves of the tree}
  \label{fig:numbered}
\end{figure}


This section aims to formalize the relation that orders elements of
the |ZipperType| type (that is, the configurations of the abstract machine) and
prove it is \emph{well-founded}. However, before doing so there are
two central problems with our choice of |ZipperType| data type:

\begin{enumerate}
\item The |ZipperType| data type is too liberal. As we evaluate our input expression
  the configuration of our abstract machine changes constantly, but satisfies
  one important \emph{invariant}: each configuration is a decomposition of the
  original input. Unless this invariant is captured, we will be hard pressed
  to prove the well-foundedness of any relation defined on configurations.

\item The choice of the |Stack| data type, as a path from the leaf to the
  root is convenient to define the tail recursive machine, but inpractical
  when defining the desired order relation. The top of a stack stores information about
    neighbouring nodes, but to compare two leaves we need \emph{global} information
    about their positions relative to the root.
\end{enumerate}

We will now address these limitations one by one. Firstly, by refining
the type of |ZipperType|, we will show how to capture the desired
invariant (Section~\ref{subsec:stack}). Secondly, we
explore a different representation of stacks, as paths from the root, that facilitates
the definition of the desired order relation (Section~\ref{subsec:topdown}).
Finally we will define the relation over configurations,
Section~\ref{subsec:relation}, and sketch the proof of that it is well-founded.

\subsection{Invariant preserving |ZipperType|}
\label{subsec:stack}

The |ZipperType| denotes a leaf in our input expression. In the
previous example, the following |ZipperType| corresponds to third leaf:

\begin{figure}[h]
  \includegraphics{figure3}
  \caption{Example of \emph{zipper} for leaf number 3}
  \label{fig:example_zipper}
\end{figure}

As we observed previously, we would like to refine the type |ZipperType| to capture
the invariant that execution preserves: every |ZipperType| denotes a unique leaf
in our input expression.
There is one problem: the |Stack| data type stores the values of the subtrees that have
been evaluated, but does not store the subtrees themselves.
In the example in Figure~\ref{fig:example_zipper}, 
when the traversal has reached the third leaf, all the
subexpressions to its left have been evaluated.

In order to record the necessary information, we redefine the |Stack| type as follows:
\begin{code}
  data Stack2 : Set where
    Left   : Expr -> Stack2 -> Stack2
    Right  : (n : Nat) -> (e : Expr) -> eval e == n -> Stack2 -> Stack2
    Top    : Stack
\end{code}
The |Right| constructor now not only stores the value |n|, but also
records the subexpression |e| and the proof that |e| evaluates to |n|.
\wouter{Couldn't we have the same definition of stacks, but introduce
  a \emph{predicate} |Valid : Stack -> Expr -> Set| capturing the
  invariant? And then show that our tail-recursive evaluator preserves validity?}

We can now recover the input expression from our |ZipperType|. This is
analogous to the |plug| operation on zippers:
\begin{code}
  plugup : Expr -> Stack2 -> Expr
  plugup e []                      = e
  plugup e (Left t        :: stk)  = plugup (Add e t) stk
  plugup e (Right n t eq  :: stk)  = plugup (Add t e) stk

  plugZup : ZipperType -> Expr
  plugZup (n , stk) = plugup (Val n) stk
\end{code}

Any two terms of type |ZipperType| may still represent states of a fold
over two entirely different expressions. As we aim to define an order relation,
comparing positions during the traversal of the input expression, we need to ensure
that we only ever compare two positions in the same tree. We can \emph{statically} enforce
such requirement by
defining a new wrapper data type over |ZipperType| that records the 
original input expression:

\begin{code}
  data Zipperup (e : Expr) : Set where
    prodOp : (z : ZipperType) -> plugZup z == e -> Zipperup e
\end{code}

For a given expression |e : Expr|, any two terms of type |Zipperup e| are
configurations of the same abstract machine during the tail recursive fold over
the expression |e|.

\subsection{Up-down |ZipperType|}
\label{subsec:topdown}

The interpretation of the |Stack| in the |ZipperType| as a path from the leaf of the
up to the root of the input expression is not well suited for defining an
ordering relation. The problem arises because the stack only stores local
information about the direct neighbours but fails to show the global position of
the leaf with respect to the expression and other leaves. Continuing with with
the example expression, let us consider the value of |ZipperType| corresponding to
leaves with numbers 3 and 4.

\begin{figure}[h]
  \includegraphics{figure4}
  \caption[angle=90]{Comparison of \emph{zipper} for leaves 4 and 3}
  \label{fig:example_zipper}
\end{figure}

The natural way to define a relation is by induction over the stack, indeed
there is not really much other option. We can start by comparing the first
element of both stacks, then decide if we continue peeling layers or maybe we
reached in the case where one is obviously smaller.

However, there is a problem. Just the head of both stacks does not contains
enough information to determine which is smaller. The head of the stack only
knows about the location of the leaf with respect to the immediate |Add| fro
where it is hanging. This kind of local information cannot be used to decide
globally which one of the leaves is located in a position more to the right.

From the two zipper examples, we can see that the part of the stack holding the
global information about the position of the leaves is its tail.  The common
part of the tail that both stacks share indicates that both leaves belong to the
same subtree with regard to the input expression. In the example, both stacks
point to the left subtree of the root node. Once the stacks differ, we found the
exact node |Add| where one of the leaves, in our example number 3, belong to the
left subexpression and the other, number 4, to the right.

This motivates for a new definition of the type |Stack| as a path from the root
of the stack down to the leaf. However, we don't have to change the type at all!
A reversed |Stack| is a |Stack| itself. The difference resides in how we interpret
the stack rather than how it is defined. As such, we can define the new
interpretation as another kind of \emph{plugging} function:

\begin{code}
  plugdown : Expr -> Stack2 -> Expr
  plugdown e []                     = e
  plugdown e (Left t       :: stk)  = Add (plugdown e stk) t
  plugdown e (Right n _ _  :: stk)  = Add t (plugdown e stk)

  plugZdown : ZipperType -> Expr
  plugZdown (n , stk) = plugdown (Val n) stk
\end{code}

We can convert from one interpretation of the |Stack2| to the other by reversing
the stack. Both interpretations are equivalent in the sense that if one
\emph{plug}s to an expression, its conversion \emph{plug}'s (in a different way)
to the same expression.

\begin{code}
  convert : ZipperType -> ZipperType
  convert (n , s) = (n , reverse s)

  plugdown-to-plugup  : forall (z : ZipperType)
                      → plugZdown z ==  plugZup (convert z)
\end{code}

Finally, we can create a new wrapper around |ZipperType| that enforces at the type
level that the |ZipperType| plugs, or is a leaf, of a concrete expression.

\begin{code}
  data Zipperdown (e : Expr) : Set where
    prodOp : (z : ZipperType) -> plugZup z == e -> Zipperdown e
\end{code}

As a corollary of the property\todo{ref somehow}, we can switch back and forward
between |Zipperup| and |Zipperdown|.

\begin{code}
 Zipperdown-to-Zipperup : (e : Expr) → Zipperdown e -> Zipperup e
 Zipperdown-to-Zipperup t (z , eq)
    = (convert z) , (trans (sym (plugup-to-plugdown z)) eq)

 Zipperup-to-Zipperdown : (e : Expr) -> Zipperup e -> Zipperdown e
   = ...
\end{code}

\subsection{Relation over \emph{ZipperType}}
\label{subsec:relation}

Finally, we write the ordering relation over over values of type |Zipperdown|.
Nevertheless, we shall keep both interpretation of the \emph{zipper} around: the
type |Zipperup| will be used for computing the fold; the type |Zipperdown|
will be used to prove termination.

The relation is type indexed by a concrete expression that indexes both values,
thus it is not a single relation but a family of relations one for every element
of type |Expr|. By indexing both |Zipperdown| arguments with the same expression
we ensure the relation imposes an order over configurations of the same abstract
machine. The relation is encoded as follows.

\begin{code}
  data IxLtOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set where
    <-StepR  : llcorner r lrcorner (t1 , s1) < (t2 , s2)
             ->  llcorner Add l r lrcorner (t1 , Right l n eq :: s1) < (t2 , Right l n eq :: s2)
    <-StepL  : llcorner l lrcorner (t1 , s1) < (t2 , s2)
             ->  llcorner Add l r lrcorner (t1 , Left r :: s1)       < (t2 , Left r :: s2)

    <-Base  :   (e1 == plugZdown t2 s2)
            ->  (e2 == plugZdown t1 s1)
            ->  llcorner Add e1 e2 lrcorner (t1 , Right n e1 eq :: s1) < (t2 , Left e2 :: s2)
\end{code}

The constructors |<-StepR| and |<-StepL| cover the inductive cases. The idea is
that they are used to traverse the common spine of the expression that is shared
by both |Zipperdown|. When the head of both stacks are equal, both zippers are
positioned in the same subexpression of a node |Add|. Thus the proof of which
one is small, is computed by forgetting the common part of the expression and
focusing on the relevant subtree |l| or |r|.

The base case of the relation is given by the constructor |<-Base|. It
describes the situation where the head of both stacks are different. This means
that one of the |Zipperdown| is pointing to a leaf in the left subexpression
while the other is located in the right. Thus determining which one is smaller
is simple, it is the one on the right subtree, i.e. constructor |Right|.

Now we turn into showing that the relation is \emph{well-founded}. A sketch of
the proof is.

\begin{code}
    <-WF : forall (e : Expr) -> Well-founded (llcorner e lrcornerLtOp)
    <-WF e x = acc (aux e x)
          where
            aux : forall (e : Expr)  (x : Zipperdown e)
                                     (y : Zipperdown e) → llcorner t lrcorner y < x → Acc (llcorner e lrcornerLtOp) y
            aux = ...
\end{code}


\carlos{after studying the standard library almost all the proofs about well
foundedness of relations have this kind of
shape}.

The proof follows the standard schema of many well-foundeness proofs as found in
Agda's standard library~\todo{ref} It uses an auxiliary function that quantifies
over the type of elements of the relation and returns a proof that the
accessibility predicate is true for every smaller element.

Because the relation we we defined is not just one relation, but a family of
them, the ancillary function |aux| quantifies over elements of type |Expr|.

Why to go through the hassle of defining a type indexed relation and a
parametrized proof of well-foundedness? The fact is that if the type index was
not present, thus the relation would be defined over terms of type |ZipperType|,
then it is not possible to complete the well founded proof.

A well foundedness proof works by appealing either to the recursive structure of
the smaller than proof, for example in the inductive cases, or to the recursive
structure of the input. The base case, constructor |<-Base|, has no recursive
structure in the proof because there is no recursive parameter. In such case,
the auxiliary function should recurse over some substructure of the input.
Without the type index, the subexpressions to the left |e1| and right |e2| are
not syntactically related thus a recursive call is not possible.  By the end of
the day, proving that a relation is well founded amounts to show Agda's
termination checker that something syntactically decreases.

\subsection{Assembling the pieces together}
\label{sec:basic-assembling}

Almost all the prerequisites to write the tail recursive fold, |tail-rec-eval|,
are in place. However, we are missing one crucial element, a proof that
applying the function |unload| to a configuration of the abstract machine
delivers a smaller configuration by the relation.

There are a couple of minor mismatches on how the function |unload| works that
we need to fix before proceeding with the proof. The function is defined to
treat the |Stack2| part of the |ZipperType| as a \emph{stack} pushing and popping
elements from the top. This corresponds with the view of the stack as
a path from the leaf up to the root. Moreover, the function |unload| is defined
over elements of type |ZipperType| with no type level information attached.

We can solve the first problem by proving that |unload| preserves the overall
input expression of the |ZipperType| it takes as an argument.

\begin{code}
  unload-preserves-plugup  : forall (e : Expr) (x : Nat) (eq : eval e == x) (s : Stack2) (z' : ZipperType)
                           -> unload e x eq s == inj1 z'
                           -> forall (t : Expr) -> plugup e s == t -> plugZup z' == t
  unload-preserves-plugup = ...
\end{code}

In the remainder of this section, we will sketch the proofs of
well-foundedness of our relation and correctness of the tail-recursive
evaluator. Both these proofs have been formalized in Agda and we refer
to our development for the full details.

\paragraph{Proof of well-foundedness}
The new version of the relation is suitable for proving well
foundedness because we can pattern match on the equality included in
the |Zipperdown| type to show how the overall structure
decreases. This allows us to use the recursion we need to complete the
proof.  In particular, the case we were not able to prove before, now
can be proven by learning that |(t2 , s2)| is a position on the left
subtree while |(t1 , s1)| is on the right subtree of a common |Add|
node.

Using such definition we can write a new type-indexed function that performs one
step of the fold. It unwraps a element of type |Zipperup| calls |unload| (whose
type has suffered some changes to account for the new type of |Stack|
(Section~\ref{todo}) and returns either a value of the same type or a natural
number if the computation is done.

\begin{code}
  step : (e : Expr) -> Zipperup e -> Zipperup e U+ Nat
  step e ((n , s) , eq)
    with unload (Val n) n refl | inspect (unload (Val n) n refl) s
    ... | inj1 z' | [ Is ]  = (z' , unload-preserves-plugup (Val n) n refl s z' Is e eq)
    ... | inj2 x            = inj2 x
\end{code}

Finally, we define the theorem that proofs that applying |step| over a configuration
delivers a smaller configuration.

\begin{code}
  step-< : (e : Expr) -> (z z' : Zipperup e) -> step e z == inj1 z'
         -> llcorner e lrcorner Zipperup-to-Zipperdown z' < Zipperup-to-Zipperdown z
  step-< = ...
\end{code}

The proof of such theorem is very tedious because the type index has to be
preserved makes difficult to articulate auxiliary lemmas that help with the
distinct cases. Instead, a much easier approach is to define another relation
over plain elements of type |ZipperType| and prove that with enough evidence there
exists an injection between both.

\begin{code}
  data LtOp :  ZipperType -> ZipperType -> Set where
    ...

  to  : forall (e : Expr) (z1 z2 : ZipperType)
      -> (eq1 : plugZdown z1 == e) (eq2 : plugZdown z2 == e)
      -> z1 ltOp z2 -> llcorner e lrcorner (z1 , eq1) < (z2 , eq2)
  to = ...
\end{code}

Thus to complete the previous theorem is sufficient to show that the function
|unload| delivers a smaller |ZipperType| by the plain relation (because we have
already proven that |unload| preserves the input expression).

\begin{code}
  unload-<  : forall (n : Nat) (s : Stack2) (e : Expr) (s' : Stack2)
            -> unload (Val n) n refl s ≡ inj1 (t' , s')
            -> (t' , reverse s') ltOp (n , reverse s)
  unload-< = ...
\end{code}

The proof is done by induction over the stack supported by an ancillary
definition that captures how the function affects the shape of the stack. It is
a long proof (around 200 lines of code) thus we decided not to include it here.
It can be found in the online repository.

The function |tail-rec-eval| is completed as follows.

\begin{code}
  rec : (e : Expr) -> (z : Zipperup e)
      -> Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z) -> Zipperup e U+ Nat
  rec e z (acc rs) = with step e z | inspect (step e) z
  ... | inj2 n  | _       = inj2 n
  ... | inj1 z' | [ Is ]  = rec e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is)

  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec e (load e stk) (<-WF e)
\end{code}

\paragraph*{Correctness}
\label{sec:basic-correctness}

Indexing the data type \emph{zipper} with the input expression allow us to prove
correctness of the transformation easily. The type of the function |step|
enforces at the type level that the tail recursive fold is constantly executed
over the same input expression.

Proving the function |tail-rec-eval| to be correct amounts to show that the
recursor, |rec|, is correct w.r.t. the evaluation function |eval|. We can prove
the lemma by exploiting induction over the accessibility predicate. Thus we only
remain to fulfill the base case, when the function |step| returns a natural
number.

\begin{code}
  rec-correct  : (e : Expr) → (z : Zipperup e)
               -> (ac : Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z))
               -> eval e == rec e z ac
  rec-correct e z (acc rs)
    with step e z | inspect (step e) z
  ...  | inj1 z'  | [ Is ]
       = rec-correct e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))
  ...  | inj2 n   | [ Is ] = step-correct n e eq z
\end{code}

Because |step| is defined as a wrapper over |unload| to prove |step-correct|
suffices to show that such property holds for the function |unload|. The proof
stored in the |Stack2| along with induction is enough to prove it.

\begin{code}
  unload-correct  : forall (e : Expr) (n : Nat) (eq : eval e == n) (s : Stack2)
                  -> unload t n eq s ≡ inj2 n -> eval (plugup t s) == n
  unload-correct t n eq [] .n refl  = eq
  unload-correct t n eq (Left x :: s) ()
  unload-correct t n eq (Right n' t' eq' :: s) pr
    = unload-correct (Add t' t) (n' + n) (cong2 plusOp eq' eq) s a p
\end{code}

The main theorem is proven by making a direct use of the ancillary lemma
|rec-correct|.  The accessibility predicate for the input expression is given by
the \emph{well-foundedness} proof.

\begin{code}
  correctness : forall (e : Expr) -> eval e == tail-rec-eval e
  correctness e = rec-correct e (load e [] , _) (<-WF e (load e []))
\end{code}

\carlos{maybe add some phrase here saying how cool this is!}
%} end of intro.fmt

\section{A generic tail recursive traversal}
%{ begining of generic.fmt
%include generic.fmt
The previous section showed how to prove how our hand-written tail
recursive evaluation function was both terminating and equal to our
original evaluator.  In this section, we will show how we can
generalize this construction to compute a tail-recursive equivalent of
\emph{any} function that can be written as a fold over a simple
algebraic datatype.

Before we can define any such data type generic constructions, however, we need
to fix our universe of discourse.

\subsection*{The regular universe}
\label{sec:universe}


In a dependently typed programming language such as Agda, we can
represent a collection of types closed under certain operations as a
\emph{universe}~\cite{altenkirch-mcbride,martin-loef}, that is, a data
type |U : Set| describing the inhabitants of our universe together
with its semantics, |el : U -> Set|, mapping each element of |U| to
its corresponding type. We have chosen the following universe of
\emph{regular} types\cite{morris-regular, noort-regular}:
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
(|O+Op|) and products (|O*Op|). We could represent our expression data type from
the introduction in this universe as follows:
\begin{code}
  expr : Reg
  expr = K Nat O+ (I O* I)
\end{code}
Note that as the constant functor |K| takes an arbitrary type |A| as its
argument, the entire data type lives in |Set1|. This could easily be remedied by
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
To show that this interpretation is indeed functorial, we can define the
following |fmap| operation:
\begin{code}
  fmap : (R : Reg) -> (X -> Y) -> interpl R interpr X -> interpl R interpr Y
  fmap Zero f ()
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
  cataN : forall {X : Set} (R : Reg) (interpl R interpr X -> X) -> mu R -> X
  cata R alg (In r) = alg (fmap R (cataN R alg) r)
\end{spec}
Unfortunately, Agda's termination checker does not accept this definition. The
problem, once again, is that the recursive calls to |cata| are not made to
structurally smaller trees, but rather |cata| is passed as an argument to the
higher-order function |fmap|.

To address this, we can fuse the |fmap| and |cata| functions into a single
|mapFold| function~\cite{norell-notes}:
\begin{code}
  mapFold : (R Q : Reg) -> (interpl Q interpr X -> X) -> interpl R interpr (mu Q) -> interpl R interpr A
  mapFold Zero     Q alg ()
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
\fixme{what is the notation for cross?}
\begin{code}
  eval : mu expr -> Nat
  eval = cata expr [ id , plusOp ]
\end{code}

In the remainder of this paper, we will develop an alternative
traversal that maps any algebra to a tail-recursive function that is
guaranteed to terminate and produce the same result as
the corresponding catamorphism.

\subsection*{Dissection}
\label{sec:dissection}

Given a generic representation of a type, we can automatically calculate the
type of its one hole context by a method dubbed \emph{dissection} that resembles
to the rules of derivative calculus as devised by Leibniz.

In a |mu R| type there are two recursive structures, the explicit one induced by
taking the fixed point of interpreting |R| over itself and the implicit
recursion given by the fact that the functor layer can be recursive due to the
possibility of combining functors as products, |O*Op|, or coproducts |O+Op|.

Dissection takes the functorial layer and allow us to programatically derive all
the possible ways of distinguishing exactly a occurrence of the variable such
that the variables to its left may take a different type from the variables to
the right.

By using the analogy of a functor |F| as a container of things of a base type
|A|, then if we take a representation\footnote{Representations are not unique}
for the expression type |Expr|, |One O+ (I O* I)|, we dissect it as depicted in
the following picture.

\todo{PIC HERE}

We shall now define in Agda the dissection operation by induction over |Reg|.

\begin{code}
  nabla : (R : Reg) → (Set → Set → Set)
  nabla Zero  X Y  = Bot
  nabla One   X Y  = Bot
  nabla I     X Y  = Top
  nabla (K A) X Y  = Bot
  nabla (R O+ Q) X Y = nabla R X Y U+ nabla Q X Y
  nabla (R O* Q) X Y = nabla R X Y * interpl Q interpr Y U+ interpl R interpr X * nabla Q X Y
\end{code}

The last clause of |nabla| definition's is the interesting one. To
\emph{dissect} a product of things we either \emph{dissect} the left component
pairing it with the second component interpreted over the second variable |Y|;
or we \emph{dissect} the second component and pair it with the first interpreted
over |X|. This \emph{or} is what will give us all the possible combinations.

A \emph{dissection} is formally defined as the pair of the one-hole context and
the missing value that can fill the context.

\begin{code}
  Dissection : (R : Reg) -> (X Y : Set) -> Set
  Dissection R X Y = nabla R Y X * X
\end{code}

Given a \emph{dissection} we can show how to reconstruct the original structure
by means of a \emph{plugging} operation.  The type of variables to the left,
|X|, does not need to agree with |Y| as long as we can recover |X|s from |Y|s.

\begin{code}
  plug : (R : Reg) -> (Y -> X) -> Dissection R Y X -> interpl R interpr X
  plug Zero   eta (() , x)
  plug One    eta (() , x)
  plug I eta (tt , x)  = x
  plug (K A)  eta (() , x)
  plug (R O+ Q) eta (inj1 r , x)  = inj1 (plug R eta (r , x))
  plug (R O+ Q) eta (inj2 q , x)  = inj2 (plug Q eta (q , x))
  plug (R O* Q) eta (inj1 (dr , q) , x) = plug R eta (dr , x)  , q
  plug (R O* Q) eta (inj2 (r , dq) , x) = fmap R eta r           , plug Q eta (dq , x)
\end{code}
\subsection{Generic Zippers}

Calculating the \emph{dissection} of a code gives us the type of the one hole context
of the functorial layer of a from given
representation without taking into account the recursive structure introduced by
|mu|.

A path within a tree is a list of \emph{dissections} and a subtree. On the left
part of the \emph{dissection} we store the results of the subtrees that we have
already processed while on the right the subtrees that are still to be consumed.
We do not only want the partial results but also the subtree from which they
come and a proof of the fact.

\begin{code}
 record Computed (R : Reg) (X : Set) (alg : interpl R interpr X → X) : Set where
    constructor _,_,_
    field
      Tree  : mu R
      Value : X
      Proof : catamorphism R alg Tree == Value
\end{code}

A \emph{stack} in the generic case is then a list of \emph{dissections} over
|Computed| and subtrees of type |mu R|. We have to embed the algebra in the
\emph{stack} because we store the proofs.

\begin{code}
  Stack : (R : Reg) → (X : Set) → (alg : interpl R interpr X → X) → Set
  Stack R X alg = List (nabla R (Computed R X alg) (mu R))
\end{code}

The path, as in the |Expr| example, can be understood either as going from the
root down to the subtree or from the subtree up to the root. We account for both
cases:

\begin{code}
  plug-mudown  : (R : Reg) -> {alg : interpl R interpr X -> X}
               -> mu R -> Stack R X alg → mu R
  plug-mudown R t []         = t
  plug-mudown R t (h :: hs)  = In (plug R Computed.Tree h (plug-mudown R t hs))

  plug-muup  : (R : Reg) -> {alg : interpl R interpr X -> X}
             -> mu R → Stack R X alg → mu R
  plug-muup R t []         = t
  plug-muup R t (h :: hs)  = plug-muup R (In (plug R Computed.Tree h t)) hs
\end{code}


We are not interested in any path but only those that point directly to one of
the leaves of the tree. But first, we should ask ourselves, what is a leaf in a
generic structure?

The |I| constructor of the type |Reg| flags the occurrence of the type variable.
If it is not present in some part of the type, such as in the left side of the
coproduct |One O+ (I O* I)|, then it is possible to build a term of that type
does not mention elements of the type variable at all.

Generically, we can encode a predicate that checks whether a value of type |
interpl R interpr X| uses the variable |X|. In case the predicate is true, we
are able to replace the type |X| for any other type |Y|.

\begin{code}
  data NonRec : (R : Reg) → interpl R interpr X → Set where
    NonRec-One  : NonRec One tt
    NonRec-K    : (B : Set) → (b : B) → NonRec (K B) b
    NonRec-+1   : (R Q : Reg) → (r : interpl R interpr X)
                → NonRec R r → NonRec (R O+ Q) (inj1 r)
    NonRec-+2   : (R Q : Reg) → (q : interpl Q interpr X)
                → NonRec Q q → NonRec (R O+ Q) (inj2 q)
    NonRec-*    : (R Q : Reg) → (r : interpl R interpr X) → (q : interpl Q interpr X)
                → NonRec R r → NonRec Q q → NonRec (R O* Q) (r , q)

  coerce : (R : Reg) -> (x : interpl R interpr X) → NonRec R x -> interpl R interpr Y
    ...
\end{code}

In the fixed point structure given by |mu|, the constructor |I| marks the
occurrences of subtrees, thus if the type variable is not part of the term, i.e.
|NonRec| holds, the term is a leaf of the tree.

\begin{code}
  Leaf : Reg -> Set -> Set
  Leaf R X = Sigma (interpl R interpr X) (NonRec R)
\end{code}

Now, we are ready to give the type of \emph{Zipper} in the generic construction.

\begin{code}
  Zipper : (R : Reg) → (X : Set) → (alg : interpl R interpr X → X) → Set
  Zipper R X alg = Leaf R X * Stack R X alg
\end{code}

Equally important is that we are able to \emph{plug} back together the full
tree. We can do so by embedding the leaf part into a tree using |coerce| and
then just \emph{plug}\footnote{It works analogously for the bottom-up
\emph{Zipper}.}

\begin{code}
  plugZ-mudown : (R : Reg) {alg : interpl R interpr X → X} → Zipper R X alg → μ R →  Set
  plugZ-mudown R ((l , isl) , s) t = plug-mudown R (In (coerce l isl)) s t
\end{code}

\todo{define Zipper up and down or just mention}

\subsection*{One step of a fold}

We need a means to perform one step of the computation at a time. We can rescue
the ideas of the pair of functions, |load| and |unload| and adapt them to work
over a generic representation. First, we will focus our attention in the |load|
part.

The function |load| traverses the input term to find the occurrence of the
leftmost subtree, it loads the \emph{dissection} of the one hole context after
popping out the subtree and stores it in the \emph{stack}. We write |load| by
appealing to an ancillary definition |first-cps|, that uses continuation-passing
style to keep the definition tail recursive. This is a direct consequence of the
implicit recursive structure at the functorial level.

\begin{code}
first-cps : (R Q : Reg) {alg : interpl Q interpr X -> X}
          -> interpl R interpr (mu Q)
          -> (nabla R (Computed Q X alg) (mu Q) -> (nabla Q (Computed Q X alg) (mu Q))) -- 1
          -> (Leaf R X -> Stack Q X alg -> Zipper Q X alg U+ X) -- 2
          -> Stack Q X alg
          -> Zipper Q X alg U+ X
first-cps = ...

load  : (R : Reg) {alg : interpl R interpr X → X} -> mu R
      -> Stack R X alg -> Zipper R X alg U+ X
load R (In t) s = first-cps R R t id (lambda l -> inj1 . prodOp l) s
\end{code}

There are two continuations as arguments of |first-cps|. The first, |-- 1| , is used
to gradually build the \emph{dissection} corresponding to the functorial layer
we are traversing. The second, |-- 2|, serves to continue on another branch in case
one of the non-recursive base cases is reached.

We shall fill the definition of |first-cps| by cases.  The clauses for the bases
cases are as expected. In |Zero| there is nothing to be done. |One| and |K A|
consists of applying the continuation to the tree and the \emph{stack}.

\begin{code}
  first-cps Zero Q () _
  first-cps One  Q x k f s    = f (tt , NonRec-One) s
  first-cps (K A) Q x k f s   = f (x , NonRec-K A x) s
\end{code}

In case we find an occurrence of a recursive subtree, we discard the current
continuation for when we do not find subtrees, and use plain recursion. The
\emph{stack} passed in the recursive call is incremented with a new element that
corresponds to the \emph{dissection} of the functor layer up to
that point.

\begin{code}
  first-cps I Q (In x) k f s  = first-cps Q Q x id (lambda z  → inj1 . prodOp z) (k tt :: s)
\end{code}

For the coproduct, both cases are very similar, just having to account for the
use of different constructors in the continuations.

\begin{code}
  first-cps (R O+ Q) P (inj1 x) k f s = first-cps R P x  (k . inj1) cont s
    where cont (l , isl) = f ((inj1 l) , NonRec-+1 R Q l isl)
  first-cps (R O+ Q) P (inj2 y) k f s = first-cps Q P y  (k . inj2) (lambda -> ...) s
\end{code}

The interesting clause is the one that deals with the product. First we recurse
on the left part of it trying to find a subtree to recurse over. However, it may
be the case that on the left component there are not subtrees at all, thus we
pass as a continuation a call to |first-cps| over the right part of the product.
This might fail as well to find a subtree in which case we have to give up
and return the leaf as is.

\begin{code}
  first-cps (R O* Q) P (r , q) k f s  = first-cps R P r  (k . inj1 . (_, q)) cont s
    where cont (l , isl) = first-cps Q P q (k . inj2 . prodOp (coerce l isl)) cont'
      where cont' (l' , isl') = f (l , l') (NonRec-* R Q l l' isl isl')
\end{code}

%% WOUTER: Read up to this point

Armed with |load| we turn our attention to |unload|. First of all, it is necessary
to define an auxiliary function, |right|, that given dissection and an element
to fill the hole finds either a new one hole context and the value inhabiting it
or it realizes there no occurrences of the variable left thus returning the full
structure.

\begin{code}
  right  : (R : Reg) -> nabla R X Y -> X -> (interpl R interpr X) U+ (nabla R X Y * Y)
\end{code}
\todo{Should we give the definition?}

Its definition is simply by induction over the code |R|, with the special case
of the product that needs to use another ancillary definition to look for the
leftmost occurence of the variable position within |interpl R interpr X|.

The function |unload| is defined by induction over the \emph{stack}. If the
\emph{stack} is empty the job is done and a final value is returned. In case the
\emph{stack} has at least one \emph{dissection} in its head, the function
|right| is called to check whether there are any more holes left. If there are
none, a recursive call to |unload|, otherwise, if there is still a subtree to be
processed, it a call to the function |load| is made to traverse it to its leftmost leaf.

\begin{code}
  unload : (R : Reg)
         -> (alg : interpl R interpr X → X)
         -> (t : μ R) -> (x : X) -> catamorphism R alg t == x
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
|interpl R interpr| is storing at its leaves both values, subtrees and proofs.

However, what is needed for the recursive call is: First, the functor
intrepreted over values, | interpl R interpr X|, in order to apply the algebra;
Second, the functor interpreted over subtrees, | interpl R interpr (mu R)|, to
keep the original subtree where the value came from; Third, the proof that the
value equals to applying a |catamorphism| over the subtree.  The function
|compute| massages |r| to adapt the arguments for the recursive call to |unload|.

\todo{unload preserves}

\todo{STOP HERE}

\subsection*{Relation over Generic \emph{Zipper}s}

We can engineer a \emph{well-founded} relation over elements of type |Zipperdown
t|, for some concrete tree |t : mu R|, by explicity separating the functorial layer
from the recursive layer induced by the fixed point. At the functor level, we
impose the order over \emph{dissection}s of |R|, while at the fixed point level
we define an order inductively over the \emph{stack}s.

Towards reducing the clutter of the definition, we give a non type-indexed
relation over terms of type |Zipper|. We can later use the same technique as in
Section~\ref{sec:basic-assembling} to recover a fully type-indexed relation over
elements of type |Zipperdown t| by requiring that the \emph{zipper}s respect the
invariant, |plugZ-mudown z == t|.

The relation is defined by induction over the |Stack| part of the |zipper|s
as follows.

\begin{code}
  data <ZOp : Zipper R X alg -> Zipper R X alg -> Set where
    Step  :  (t1 , s1) <Z (t2 ,  s2) -> (t1 , h :: s1) <Z (t2 , h  :: s2)

    Base  : plugZ-mudown R (t1 , s1) == e1 -> plugZ-mudown R (t2 , s2) == e1
          -> (h1 , e1) <Nabla (h2 , e2) -> (t1 , h1 :: s1) <Z (t2 , h2 :: s2)
\end{code}

The relation has only two constructors:

\begin{itemize}
\item The constructor |Step| covers the
inductive case. When the head of both \emph{stack}s is the same, i.e. both
|Zipper| point to leaves in the same subtree, it forgets about the shared
structure and focuses on the specific subtree. Thus it expects a proof on the
\emph{zipper}s with the head removed from the \emph{stack}s.
\item The constructor |Base| accounts for the case
when the head of the \emph{stack}s is different. This means that the \emph{zipper}s
are located on different subtrees of the same internal node. In such case, the
relation we are defining relies on an auxiliary relation |<NablaOp| that orders
\emph{dissection}s of type |Dissection R (Computed R X alg) (mu R)|.
\end{itemize}

The ancillary relation does not neccesitate to be aware of the recursive nature
of its input. It can be written in a more general form over \emph{dissection}s
interpreted on any sets |X| and |Y|. Its definition is the following.

\begin{code}
  data <NablaOp : (R : Reg) → Dissection R X Y → Dissection R X Y → Set where
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

The idea is that we order elements of a \emph{dissection} in such a way
that the more the hole is to the right, the smallest that element should be.

All the constructors but the last one are defined by induction over the code of
the \emph{dissection}. The base case, constructor |base-*|, is the responsible for
determining which \emph{dissection} is smaller.

The \emph{dissection} of the product of two functors, |R O* Q|, has two possible
values. It is either a term of type |nabla R X Y * interpl Q interpr Y|, such as
|inj1 (dr , q)| or a term of type |interpl R interpr X * nabla Q X Y| like |inj2
(r , dq)|. The former indicates that the hole inhabits the left component of the
pair while the latter reveals that the hole is in the right component.  Thus by
the criteria we explained before, the latter is defined as being smaller to the
former.

Both relations we just defined are opportune to order terms of type |Zipper|, or
configurations of the abstract machine, but not strong enough to allow us to
prove that they are \emph{well-founded}.

In order to prove such property, we write a type-indexed version of each
relation. The first relation, |<ZOp|, has to be type-indexed by the tree of
type |mu R| to which both \emph{zipper} recursively plug through
|plugZ-mudown|. And the auxiliary relation, |<NablaOp|, needs to be
type-indexed by the functor of type | interpl R interpr X | to which both
\emph{dissections} |plug|. The signature of both relations is as follows.

\begin{code}
  data IxLt  :  (R : Reg) -> (tx : interpl R interpr X) 
             -> IxDissection R X Y eta tx -> IxDissection R X Y eta tx → Set where


  data IxLtdown  (R : Reg)  : (t : μ R) 
             -> Zipperdown R X alg t -> Zipperdown R X alg t -> Set where
\end{code}

The proof of \emph{well-foundedness} of |IxLtdown| adopts the same ideas as the
proof for the non generic example given in Section~\ref{subsec:relation}. Because of the
dependency bewteen the two relations, the proof relies on the relation |IxLt| being
also \emph{well-founded}. The full proof can be found in the accompanying code,
therefore here we only spell its signature.

\begin{code}
  IxLtdown-WF : (R : Reg)  -> (t : μ R) 
                           -> Well-founded (llcorner R lrcornerllcorner t lrcornerIxLtdown)
\end{code}

\subsection*{Putting the pieces together}

+ unload to a smaller position by the relation
	+ right to smaller on the dissection layer

+ type indexed step => uses equivalence between the zippers

+ tail recursive fold

\subsection{Correctness generically}
+ correctness for free by indexed
+ The proof holds

%} end of generic.fmt

\section{Discussion}
\label{sec:discussion}

+ Regular universe kind of limited
+ Generalize to other universes
+ Discuss why not to use other techniques

\subsection*{Related work}
Danvy and dissection

Generics in Agda

\subsection*{Future work}

\subsection*{Conclusion}


%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This material is based upon work supported by the
  \grantsponsor{GS100000001}{National Science
    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
  conclusions or recommendations expressed in this material are those
  of the author and do not necessarily reflect the views of the
  National Science Foundation.
\end{acks}



%% Acknowledgments
% \begin{acks}
% \end{acks}


%% Bibliography
\bibliography{main}


\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End:


