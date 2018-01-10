%include polycode.fmt
%include proposal.fmt

\newcommand{\regular}[0]{\emph{Regular}~}

\section{Generic programming and dissection}\label{sec:generic}

Before exploring McBride's \textit{Dissection}, we present a bit of background
on datatype generic programming. The aim of datatype generic programming is to
abstract over the concrete representation of types to express them as the
combination of a set of primitives. Functions defined over this set of
primitives can then be lifted to work on the original type. The set of
primitives is often called the \emph{universe} and its choice determines the
collection of types over which generic functions may be defined.

In this section, we give an overview of generic programming within the realm of
dependent types and how to defined McBride's \textit{dissection} in this style.
We start, in \cref{subsec:universe}, by introducing a \emph{universe} for
\regular tree types, followed in \cref{subsec:differentiation} by an
explanation of what means to \textit{differentiate} a type. In
\cref{subsec:dissection} we explain how dissection generalizes the idea of
differentiation and finally in \cref{subsec:fold-dissection}, we explain the
relation between a fold and its tail recursive counterpart using dissection.

%{
%format Reg = "\AD{Reg}"
%format V   = "\AI{V}"
%format A   = "\AD{A}"

\subsection{A universe for \regular types}
\label{subsec:universe}

It is a common approach in a dependently typed setting such as \Agda~to use a
universe construction for generic programming. Such construction consists of a
type of \emph{Codes} and an interpretation function that maps a given code to an
\Agda~type. This is possible because dependent types allow for large eliminations,
i.e. functions returning |Set| can dispatch on elements of some |A : Set|.

We define a universe for expressing \regular tree types. The intuition is that a
\regular tree is a datastructure that has a tree-like shape and is both finitely
branching and finitely deep. As a starting point we will only consider a
universe with empty element, unit, a variable, product and coproduct.

\InsertCode{Proposal/Regular.tex}{R}

While |Reg| defines the type of \emph{codes} of our universe the construction
it will be incomplete unless we give an interpretation function. For this matter
we choose to interpret a \emph{code} as an \Agda~functor, type |Set -> Set|,
because |Reg| allows for one variable through the |V| constructor.

\InsertCode{Proposal/Regular.tex}{Interpretation}

%{
%format true  = "\AI{true}"
%format false = "\AI{false}"
%format Bool  = "\AD{Bool}"
%format top   = "\AD{\ensuremath{\top}}"
\begin{example}
  As a first example, we show how |Reg| can be used to encode the type of
  booleans. This type has only two constructors that take no arguments,
  |true| and |false|.
  \InsertCode{Proposal/Regular.tex}{Bool-Ind}
  The code for |Bool| requires to differentiate between both constructors.
  Because it does not use the variable constructor |V|, so we can freely
  interpret it over any |Set|. We choose |top| for convenience.
  \InsertCode{Proposal/Regular.tex}{Bool-Reg}
  Both representations are equivalent which can be witnessed by a pair of
  functions converting between them. In fact there is an isomorphism, but its
  proof is left as an exercise for the reader.
  \InsertCode{Proposal/Regular.tex}{Bool-from-to}
\end{example}
%}

\vspace{0.25cm}
We mentioned before that the interpretation of a code in |Reg| is an \Agda~
functor still we have not define the corresponding fmap operation to lift
functions. Moreover, we could use \Agda~'s logical fragment to prove that it
obeys (extensionally) the functor laws.

\InsertCode{Proposal/Regular.tex}{R-Fmap}

%{
%format Maybe = "\AD{Maybe}"
%format just = "\AI{just}"
%format nothing = "\AI{nothing}"

\begin{example}
  The |Maybe| type for computations that may not succeed is a good example of
  a functorial type that can be encoded using |Reg|.  The \emph{code} for
  |Maybe| has to account for two constructors, |just|, that uses the
  variable and |nothing| that does not.
  \InsertCode{Proposal/Regular.tex}{Maybe-Type}
  For any set \AD{A} we can convert from both definitions and prove (left again
  as an exercise) that there is a natural isomorphism between them.
  \InsertCode{Proposal/Regular.tex}{Maybe-from-to}
\end{example}
%}
\vspace{0.25cm}

Until now we have been somewhat limited in the kind of types that |Reg| can
represent because recursion can not be encoded yet. In order to do so, we need
to introduce the fixed point of a |Reg| \emph{code}. Fixed points in general do
not need to terminate so its encoding in \Agda~uses a datatype that serves both
as its syntax and semantics.

  \InsertCode{Proposal/Regular.tex}{Mu}

The idea is that the type variable in |Reg| is used to mark the recursive
positions and |μ| ties the knot by interpreting |Reg| over itself. Our
presentation of a regular universe differs from Morris et al
\cite{Morris2004ExploringTR} because we only allow for one variable and the
fixpoint is fixed over the full expression.

\begin{example}
  As an example of a recursive datatype we can use the type of natural numbers.

  \InsertCode{Proposal/Regular.tex}{Nat-Ind}

  The variable in the code represents the recursive positions, in this
  case the argument to \AD{suc}. Using the fixed point we can tie the knot over
  it to deliver the natural numbers.

  \InsertCode{Proposal/Regular.tex}{Nat-Reg}

  Again witnessing that both constructions are equivalent we can define
  conversion functions and prove that there is an isomorphism.

  \InsertCode{Proposal/Regular.tex}{Nat-from-to}
\end{example}

%{
%format right = "\AF{right}"
%format plug  = "\AF{plug}"
%format first = "\AF{first}"

\subsection{Differentiation of a \regular tree
type}\label{subsec:differentiation}

A functor can be seen as container of elements. The elements are drawn from the
type that the functor uses as a parameter. The \regular universe
construction defines containers whose relevant information is stored in the
positions occupied by a |V| constructor.
McBride\cite{Mcbride01thederivative} discovered that by applying Lebniz's rules
of differential calculus to the \emph{code} of a \regular tree type we can
automatically calculate the type of its one hole context. The one hole context
of \regular functor is the type of values where \mbox{\textbf{exactly one}} of
the |V| constructors is replaced by a hole.

Differentiation is defined as a syntactic function over values of type
\AD{Reg}:

\InsertCode{Proposal/Regular.tex}{Differentiation}

The most basic operation we can perform on contexts is to fill the hole if we
have at our disposal a value of the required type. By plugging the value into
the hole we reconstruct the full structure. This function is defined by
induction over the \emph{code}.

\InsertCode{Proposal/Regular.tex}{Plug}

Recursively defined \emph{codes} through the \AD{μ} type, use the variable
position to mark the occurrences of recursive subtrees. A concrete subtree that
appears deeply within the structure can be pointed by a list of one hole
contexts that lead from the root of the tree until its position. Given such list
and the subtree we can recover the original tree.

\InsertCode{Proposal/Regular.tex}{Plug-Mu}


Given a one hole context and a value to fill the hole can move to the next hole
to the right (or left). In order to do so, we define a function |right| that
either finds a value to the right returning it along the one hole context
resulting from picking out the value or it finds that there are not values left
and the full structure is returned. The function is defined by induction over
|Reg|.

\InsertCode{Proposal/Regular.tex}{Right}

From a \regular tree functor we can distinguish the "first" hole to the left
(or to the right, it does not matter). The container may be empty of values
which we account for by wrapping the result in the \AD{Maybe} type. This
function is defined by induction on the code and it works by iterating
leftwards until it reaches the base case \AI{V}.

\InsertCode{Proposal/Regular.tex}{First}

In a recursive container the "first" element is the leftmost subtree if it
exists accompanied by the list of one hole contexts that led to it. The
definition of this function follows an similar structure to the non recursive
one.

\InsertCode{Proposal/Regular.tex}{First-Mu}

%{
%format J = "\AI{J}"
%format C = "\AI{C}"
%format F = "\AI{F}"
%format S = "\AI{S}"
%format Reg2 = "\AD{\ensuremath{Reg_2}}"

\subsection{Dissection of a \regular tree type}\label{subsec:dissection}

The one hole context of a datatype distinguishes a position in the middle of the
structure. We have defined three functions manipulating contexts: |first| , that
finds the leftmost element; |right| that moves to the next element; and |plug|,
that given a context and a subtree fills the hole.

McBride goes a step further and notices\cite{McBride:2008:CLM:1328438.1328474}
that during the traversal it is not necessary that the type of values that
occupy positions to the left coincide with the type of values on the positions
to the right. Dissection materializes this idea.

A functor as in the \regular universe has only one possible variable with the
|V| constructor. Now that we need to distinguish between two different kind of
positions we need to be able to talk about two variables. We do so by defining a
universe for \regular bifunctors. The universe for bifunctorial types extends
the \regular universe, \cref{subsec:universe}, by having a constructor for each
variable, |F| and |S|, and two new constructors, |C| (Clowns following McBride's
terminology),and , |J| (Jokers), that are used to lift a normal functor into
the bifunctor selecting over which variable they should be interpreted.

\InsertCode{Proposal/Regular.tex}{R2}

Because a bifunctor has two different variables, we interpret |Reg2|
with \Agda's type for bifunctors, |Set -> Set -> Set|.

\InsertCode{Proposal/Regular.tex}{R2-Interpretation}

Dissecting a \regular code amounts to select a distinguished variable as before.
However, in the product case we both sides do not need to hold the same
variable.

\InsertCode{Proposal/Regular.tex}{Dissection}

As we did before, we can write a first operation that given a structure returns
the leftmost hole if it exists. We can be more precise and state in the type
that the one hole context does not have any more positions to the left by using
the empty type to replace the first variable. Because of this, instead of
wrapping the result with \AD{Maybe} we either return the one-hole context and
the value on the position or a proof that the structure does not have any
variable positions. Again this function can be defined by induction on the code.

\InsertCode{Proposal/Regular.tex}{R2-first}

Moving to the right in a structure that differentiates between the type of
elements to the right and to the left of some distinguished position amounts to
have an element of the right type that can be plugged in the hole. Two
situations have to be considered, either all variables have the same type
because the traversal has not started or it has started and we are stuck in the
middle and have an element of the hole type. The return type accounts for both
cases where there is a position left to explore to the right and the element
that is filling it or there are not positions to the right in which case all the
positions are of the same type.

\InsertCode{Proposal/Regular.tex}{R2-right}

A |right| function defined in this style summarizes both finding the first
position and moving to the right.

%}

\subsection{Fold and Dissection}
\label{subsec:fold-dissection}
%{
%format R = "\AB{R}"
%format cata = "\AF{cata}"
%format fmap = "\AF{fmap}"
%format mu   = "\AD{μ}"
%format phi  = "\AB{ϕ}"
%format tcata = "\AF{tcata}"
%format eval = "\AF{eval}"
%format load = "\AF{load}"
%format unload = "\AF{unload}"

A \regular tree type comes equipped with a fold\footnote{In the
literature\cite{Meijer91functionalprogramming} the fold is usually called
catamorphism, from the Greek κατά which means down.} for computing a value by
using recursion over the input structure.  Given an |R|-algebra, i.e.  a
function that indicates how to compute a value for every different constructor
in |R|, we can define a fold for \regular tree types |mu R|.

\InsertCode{Proposal/Regular.tex}{Cata-nt}
\colored

Defining |cata| like this causes \Agda's termination checker to complain because
it cannot verify that |fmap| does not increment the size of its input. In order
to define |cata| we can use an auxiliary function that fuses the fold with the
map.

\InsertCode{Proposal/Regular.tex}{Cata}

The catamorphism defined like this not tail recursive, the |R| -algebra |phi|
expects the result of the function applied to smaller subtrees before it can
compute the final result.

With dissection we can write a generic version of a fold that its tail
recursive. We use a list of \textit{dissections} of the input type to record the
one hole contexts that are still to be processed to the right but that already
have values, not subtrees, on the left. Because neither the stack nor the
structure is evidently smaller as in the case of the binary tree
(\cref{subsec:problem}) \Agda's termination checker classifies the function as
non-terminating.

\InsertCode{Proposal/Regular.tex}{tcata}
\colored

The code is analogous to the |load|/|unload| functions used to define a
tail-recursive |eval| function as we explained in \cref{subsec:problem}. Now
the right function is used to move gradually to the right while the result is
being computed.

Showing that |cata| and |tcata| are equivalent means proving the following
theorem:

\InsertCode{Proposal/Regular.tex}{theorem}
