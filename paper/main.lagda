\documentclass[sigplan,10pt,review]{acmart}

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
\email{first1.last1@@inst1.edu}

\author{Wouter Swierstra}
\affiliation{
  \department{Department of Information and Computing Sciences}
  \institution{University of Utrecht}
  \country{The Netherlands}
}
\email{w.s.swierstra@@uu.nl}


\begin{abstract}
  Lorem ipsum sic dolor amet.  Lorem ipsum sic dolor amet.  Lorem
  ipsum sic dolor amet.  Lorem ipsum sic dolor amet.  Lorem ipsum sic
  dolor amet.  Lorem ipsum sic dolor amet.  Lorem ipsum sic dolor
  amet.
  \todo{Write abstract}
\end{abstract}

\include{ccs}

\keywords{datatype generic programming, catamorphisms, dissection,
  dependent types, Agda, well-founded recursion \todo{Keywords?}}

\maketitle

\section{Introduction}
\label{sec:intro}
%{ begining of intro.fmt
%include intro.fmt

Folds, or \emph{catamorphisms}, are a pervasive programming
pattern. Folds generalize many simple traversals over algebraic data
types. Functions implemented by means of a fold are both compositional
and structurally recursive. Consider, for instance, the following
expression data type, written in the dependently typed programming
language Agda\cite{norell}:

\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}
%
We can write a write a simple evaluator, mapping expressions to
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
one. Writing such tail recursive functions by hand is both tedious and
error-prone. It is precisely these issues that this paper tackles
by making the following novel contributions:

\begin{itemize}
\item We give a verified proof of termination of |tail-rec-eval| using
  a carefully chosen \emph{well-founded relation}
  (Section~\ref{sec:basics}). After redefining |tail-rec-eval| using
  this relation, we can prove the evaluators equal in Agda.
\item We generalize this relation and its corresponding proof of
  well-foundedness, inspired by
  \citeauthor{dissection}'s~ work on
  \emph{dissections}~\cite{dissection}, to show how to calculate an abstract machine
  from an algebra. To do so, we define a universe of algebraic data
  types and a generic fold operation
  (Section~\ref{sec:universe}). Subsequently we show how to turn any
  structurally recursive function defined using a fold into its tail
  recursive counterpart (Section~\ref{sec:dissection}).
\item Finally, we sketch how the proofs of termination and semantics
  preservation from our example are generalized to the generic fold
  over arbitrary types in our universe
  (Section~\ref{sec:correctness}). 
\end{itemize}
Together these results give a verified function that computes a tail
recursive traversal from any algebra for any algebraic data type.
All the constructions and proofs presented in this paper have been
implemented in and checked by Agda. The corresponding code is freely
available online.\footnote{\todo{url}}


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
leaf; second when |unload| is inspects the stack in searching of an
unevaluated subtree. This process is depicted in
Figure~\ref{fig:load-unload}.

\begin{figure}
  \centering
  \includegraphics[scale=0.25]{figure1}  
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
      ... | inj1 (n' , stk') = nrec (n' , stk')
      ... | inj2 r = r
\end{code}
%}
Here we use |load| to compute the initial configuration of our machine
-- that is the leftmost leaf in our initial expression. We proceed by
repeatedly calling |unload| until it returns a value.  This version of
our evaluator, however, does not pass the termination checker. The new
state, |(n' , stk')|, is not structurally smaller than the initial
state |(n , stk)|. If we work under the assumption that we have a
well-founded relation between the states |Nat * Stack| that decreases
after every call to |unload|, we can define the following version of
the tail recursive evaluator:
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

\section{Well-foundedness tree traversals }

The tail recursive evaluator, |tail-rec-eval| processes the leaves of
our input expression in a left-to-right fashion. The leftmost leaf --
that is the first leaf found after the initial call to |load| -- is
the greatest element; the rightmost leaf is the smallest. In our
example tree from Section~\ref{sec:intro}, we would number the leaves
as follows:

\begin{figure}[h]
  \includegraphics[scale=0.25, angle=90]{figure3}
\end{figure}

This section aims to formalize this notion of ordering and prove it is
well-founded. There are two central problems with our choice of |Stack|
data type that we must overcome in this section:

\begin{enumerate}
\item The |Stack| data type is `upside down.' As demonstrated by
  \citeauthor{dissection}, such stacks arise as a generalization of
  \emph{zippers}~\cite{huet}. A zipper allows efficient navigation
  through our expression tree, but makes it harder to compare the
  relative positions of two leaves the original tree. The top of a
  stack stores information about neighbouring nodes, but to compare
  two leaves we need global information regarding their relative
  positions to the root.
\item The |Stack| data type is too liberal. As we evaluate our input
  expression the configuration of our abstract machine changes
  constantly, but satisfies one important \emph{invariant}: each
  configuration is a decomposition of the original input. Unless the
  |Stack| data type captures this invariant, we will be hard pressed
  to prove the well-foundedness of any relation defined on stacks.
\end{enumerate}

These considerations lead us to to redefine our |Stack| data type as
follows:

\begin{code}
  Stack : Set
  Stack = List (Expr U+  (Sigma Nat lambda n ->
                          Sigma Expr lambda e -> eval e == n))
  pattern Left t        = inj1 t
  pattern Right n t eq  = inj2 (n , t , eq)

  Zipper : Expr -> Set
  Zipper e = Nat * Stack e
\end{code}
\wouter{I would suggest introducing a custom data type for stacks
  here, parameterized by the original input expression.}

The original expression for which a |Nat * Stack| represents a
position can be reconstructed by forgeting that some part has already
been evaluated.  \wouter{Why are we talking about plugging at this
  point? Weren't we supposed to define a relation?}
\begin{code}
  plugup : Expr -> Stack -> Expr
  plugup e []                      = e
  plugup e (Left t        :: stk)  = plugup (Add e t) stk
  plugup e (Right n t eq  :: stk)  = plugup (Add t e) stk

  plugZup : (Nat * Stack) -> Expr
  plugZup (n , stk) = plugup (Val n) stk
\end{code}
\wouter{How do these definitions change if we revise stacks to be expr
  indexed?}

We would like to define a well-founded relation on zippers that
decreases during the execution of our tail-recursive evaluation
function. As this evaluator processes the leaves left-to-right, this
relation should order the leaves of the tree accordingly. 

Unfortunately, zippers are not the right datastructure to define such
a relation. The central problem is that zippers store the path
\emph{to} the root. This allows for efficient navigation: to move
upwards we simply inspect the top of the current stack. When comparing
two positions in the tree, however, we want to compare the path
\emph{from} the root to determine their relative positions This change
of perspective is realised with a new plug function that does the
opposite of |plugup|.

\begin{code}
  plugdown : Expr -> Stack -> Expr
  plugdown e []                     = e
  plugdown e (Left t       :: stk)  = Add (plugdown e stk) t
  plugdown e (Right n _ _  :: stk)  = Add t (plugdown e stk)

  plugZdown : (Nat * Stack) -> Expr
  plugZdown (n , stk) = plugdown (Val n) stk
\end{code}

It is clear that both views of the |Zipper| are related. Indeed, to
transport from one to the other we only have to reverse the stack. We
show the equvalence with the following lemma\footnote{The other way
  around only requires to use \todo{BLABLA} of |reverse|}:

\begin{code}
  plugdown-to-plugup  : forall (e : Expr) (stk : Stack)
                      → plugdown e stk ==  plugup e (reverse stk)
\end{code}

With these definitions in place, we can finally define a suitable
relation and prove its well-foundedness. The relation |ltOp| is
defined by simultaneously traversing two paths from the root:
\wouter{Shouldn't we really be defining separate types for zippers and
  reverse zippers?}
\begin{code}
  data ltOp : Zipper -> Zipper -> Set where
    <-Right  : (t1 , s1) < (t2 , s2)
             ->  (t1 , Right l n eq :: s1) < (t2 , Right l n eq :: s2)
    <-Left   : (t1 , s1) < (t2 , s2)
             ->  (t1 , Left r :: s1)       < (t2 , Left r :: s2)
    <-Right-Left  :   (t1' == plugdown (Tip t2) s2)
                  ->  (t2' == plugdown (Tip t1) s1)
                  ->  (t1 , Right n t1' eq :: s1) < (t2 , Left t2' :: s2)
\end{code}
The |<-Right| and |<-Left| constructors to strip off their common
prefix of the two zippers. The only base case, |<-Right-Left|,
corresponds to an |Add| constructor where the two paths diverge.

Next, we would like to show that this relation is indeed
\emph{well-founded}. A relation is well-founded if and only iff all
the descending chains starting from an arbitrary element are
finite. Put differently, such a well-foundedness proof guarantees that
our |tail-rec-eval| function will terminate on all possible inputs
after a finite number of recursive calls. 

We can try to prove that the relation is well founded by using an
auxiliary function that allows us to pattern match on the smaller than
proof. When doing so, the inputs are refined to concrete
constructors. Normally the proof either makes use of recursion over
the proof or over the input, but in the case of the |<-Right-Left|
constructor we do not have either option, because the smaller element
is not structurally related to the bigger and the proof does not have
any recursive structure to use.

\begin{code}
 <-WF : Well-founded ltOp
 <-WF x = acc (aux x)
    where
      aux : ∀ (x : Zipper)
          -> ∀ (y : Zipper) -> y < x -> Acc ltOp y
      aux dotted(t2 , Left t1' :: s2) dotted(t1 , Right n t2' eq :: s1) (<-Right-Left eq1 eq2) = {!!}
      aux ...
\end{code}

The proof fails because in |aux| both Zippers |x| and |y| might very
well be locations of leaves belonging to different trees as far we
know. Thanks to the use of dependent types, the property that a Zipper
represents a position inside a concrete tree can be made explicit at
the type level.

\begin{code}
  data Zipperdown (e : Expr) : Set where
    \_,\_ : (z : Zipper) -> plugZdown z == e -> Zipperdown e
\end{code}

We write a relation that is enforced to only relate Zippers beloging
to the same |Expr| by using a common value of that type as an of
|Zipperdown|

\begin{code}
  data IxltOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set where
    ...
\end{code}

The concrete details of the relation follow very much the one we gave
before, with the exception that every case has attached a new piece of
information specifying the concrete |Expr| obtained by plugging both
Zippers.

The new version of the relation is suitable for proving well
foundedness because we can pattern match on the equality included in
the |Zipperdown| type to show how the overall structure
decreases. This allows us to use the recursion we need to complete the
proof.  In particular, the case we were not able to prove before, now
can be proven by learning that |(t2 , s2)| is a position on the left
subtree while |(t1 , s1)| is on the right subtree of a common |Add|
node.

\begin{code}
  <-WF : forall e -> Well-founded (IxltOp e)
  <-WF x = acc (aux e x)
    where
      aux : forall (e : Expr) -> forall (x : Zipperdown e)
          -> forall (y : Zipperdown e) -> y < x -> Acc (IxltOp e) y
      aux dotted(Add (plug )) dotted((t2 , Left t1' :: s2)) , refl) dotted((t1 , Right n t2' eq :: s1), eq2)
          (<-Right-Left eq1 eq2) = {!!}
      aux ...
\end{code}

We have now the proof of well foundedness for the relation defined
over top-down Zippers. We also have proven that there is an
equivalence between top-down and bottom-up Zippers. We exploit it by
using the top-down encoding for the termination proof while we use the
bottom-up to actually compute in a tail recursive manner.

Thus we prove a lemma stating that if we apply unload to a bottom-up
Zipper and this results in another Zipper, then the result is smaller
by the relation than the input. However, to show it we have to convert
them to the top down representation. In overall, what we have is the
following lemma:

\begin{code}
unload-ltop : forall n eq s t' s' -> unload (Tip n) (TipA n) eq s == inj₁ (t' , s')
            -> (t' , reverse s') ltOp (n , reverse s)
\end{code}

\subsection*{Correctness}
\label{sec:basic-correctness}
Indexing the \emph{Zipper} with an expression allow us to prove
correcness of the transformation easily. The expression during the
fold does not change, thus in every step of the computation the result
of its evaluation remains constant.

By using induction over the definition of unload, we can prove that
when |unload| delivers a value, it corresponds to the result of
evaluating of the input expression.  In order to do so, we enrich the
type of |unload| to include the expression that has already been
folded and we have its result.

\begin{code}
  unload : (e : Expr) -> (n : Nat) -> eval e == n -> Stack -> (Nat * Stack) U+ Nat

  unload-correct  : forall (e : Expr) (n : Nat) (eq : eval e == n) (s : Stack) (x : Nat)
                  -> unload e n eq s ≡ inj2 x -> eval e == x
\end{code}

Proving correctness of the whole transformation amounts to show that
it holds for the auxiliary recursor that we use to write the function
|tail-rec-eval|. We use well founded recursion to do structural
recursion over the accesibility predicate and use the lemma
|unload-correct| in the base case.



%} end of intro.fmt

\section{Generic tail recursive fold}
%{ begining of generic.fmt
%include generic.fmt
Our solution extends naturally to a more general case than only |Expr| and
|eval|.  In this section, we will show how we can reuse the ideas presented so
far, to generically construct a correct tail recursive fold once and for all
for a wide range of algebraic datatypes.

The common feature of the types that we can encode using the \emph{regular}
universe have, as the name suggests, a tree-like structure of finite depth and
finite branching. We shall exploit this commonality to generalize our solution
by defining: the type of \emph{Zipper} used to locate leaves of the tree; the
pair of |load| and |unload| functions that perform one step of the fold; and a
well founded relation to prove termination and correcness of the construction.

\subsection{The \emph{regular} universe}
\label{sec:universe}

In a dependently typed programming language such as Agda, the usual approach to
encode a generic solution is to define a type of representations; the universe;
and an interpretation function that mapping values of the representation type
into types. Our choice of universe is that of \emph{regular} tree types as given
by \todo{cite}.

\begin{code}
  data Reg : Set1 where
    Zero  : Reg
    One   : Reg
    I     : Reg
    K     : (A : Set) -> Reg
    O+Op  : (R Q : Reg)  -> Reg
    O*Op  : (R Q : Reg) -> Reg
\end{code}

\begin{code}
  interp : Reg -> Set -> Set
  interpl Zero interpr X   = Bot
  interpl One interpr X    = Top
  interpl I interpr X      = X
  interpl (K A) interpr X  = A
  interpl (R O+ Q) interpr X = interpl R interpr X U+ interpl Q interpr X
  interpl (R O* Q) interpr X = interpl R interpr X * interpl Q interpr X
\end{code}

The codes of our universe, |Reg|, are capable of representing non-recursive
functorial datatypes. This claim is sustained by the fact that we interpret them
as functors over Agda small types, i.e. |Set -> Set| , and that we can define a
law abiding fmap\footnote{Proofs are left for the reader.}.

\begin{code}
  fmap : (R : Reg) -> (X -> Y) -> interpl R interpr X -> interpl R interpr Y
  fmap Zero f ()
  fmap One  f tt  = tt
  fmap I f x      = f x
  fmap (K A) f x  = x
  fmap (R O+ Q) f (inj1 x)  = inj1 (fmap R f x)
  fmap (R O+ Q) f (inj2 y)  = inj2 (fmap Q f y)
  fmap (R O* Q) f (x , y)   = fmap R f x , fmap Q f y
\end{code}

In order to enhance the expressiveness of our generic construction to handle
recursive datatypes we have to tie the knot over the functor. We do so by
introducing the fixed point of a code interpreted over itself.

\begin{code}
  data mu (R : Reg) : Set where
    In : interpl R interpr (mu R) -> mu R
\end{code}

A recursive datatype always comes in pair with a recursive eliminator, fold,
capable of collapsing terms of such type into a single value. As |mu R| is used
to represent recursive types, we can define a generic operation fold to consume
terms into values. The generic fold is historically dubbed \emph{catamorphim}.

\begin{code}
  catamorphism : forall {X : Set} (R : Reg) (interpl R interpr X -> X) -> mu R -> X
  catamorphism R alg (In r) = alg (fmap R (catamorphism R alg) r)
\end{code}

However, this is a definition that Agda cannot cope with because of the
higher-order argument to fmap. We rewrite |catamorphism| to fuse together
the \emph{fmap} with the \emph{fold} so termination checker warnings are avoided
all along.

\begin{code}
  mapFold : (R Q : Reg) -> (interpl Q interpr X -> X) -> interpl R interpr (mu Q) -> interpl R interpr A
  mapFold Zero Q alg ()
  mapFold One Q alg tt    = tt
  mapFold I Q alg (In x)  = alg (mapFold Q Q alg x)
  mapFold (K A) Q alg x   = x
  mapFold (R O+ Q) P alg (inj1 x)  = inj2 (mapFold R P alg x)
  mapFold (R O+ Q) P alg (inj2 y)  = inj2 (mapFold Q P alg y)
  mapFold (R O* Q) P alg (x , y)   = mapFold R P alg x , mapFold Q P alg y

  catamorphism : forall {X : Set} (R : Reg) (interpl R interpr X -> X) -> mu R -> X
  catamorphism R alg (In r) = mapFold R R alg r
\end{code}

We aim to encode a tail recursive function that given an algebra |interpl R
interpr X -> X| is correct with regard to |catamorphism|.

\subsection{Dissection}
\label{sec:dissection}

Given a generic representation of a type, we can automatically calculate the
type of its one hole context by a method dubbed \emph{dissection} that resembles to the
rules of derivative calculus as devised by Leibniz.

In a |mu R| type there are two recursive structures, the explicit one have the
induced by taking the fixed point of interpreting |R| over itself and the
implicit within the functor layer that can be recursive due to the possibility
of combining functors either as products, |O*Op|, or coproducts |O+Op|.

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

Having a \emph{dissection}, |R X Y|, we can show that we can reconstruct the
original structure by means of a \emph{plugging} operation given a element of
type |X|. The type of variables to the left, |X|, does not need to agree with
|Y| as long as we can recover |X|s from |Y|s.

\begin{code}
  plug : (R : Reg) -> (Y -> X) -> nabla R Y X -> X -> interpl R interpr X
  plug Zero   eta () x
  plug One    eta () x
  plug I eta tt x  = x
  plug (K A)  eta () x
  plug (R O+ Q) eta (inj1 r) x  = inj1 (plug R eta r x)
  plug (R O+ Q) eta (inj2 q) x  = inj2 (plug Q eta q x)
  plug (R O* Q) eta (inj1 (dr , q)) x = plug R eta dr x  , q
  plug (R O* Q) eta (inj2 (r , dq)) x = fmap R eta r           , plug Q eta dq x
\end{code}

\subsection{Generic Zippers}

A dissection tell us how to calculate the type of one hole contexts from given
representation without taking into account the recursive structure introduced by
|mu|.

A path within a tree is a list of \emph{dissections} and a subtree. On the left
part of the \emph{dissection} we store the results of the subtrees that we have
already processed while on the right the subtrees that are still to be consumed.
We do not only want the partial results but also the subtree from which they
come and a proof of the fact.

\begin{code}
 record Computed (R : Reg) (X : Set) (alg : interpl R interpr X → X) : Set where
    field
      Tree  : μ R
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
  data NonRec : (R : Reg) → interpl R interpl X → Set where
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

\subsection{One step of a fold}

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


\todo{STOP HERE}

+ Unload
+ Load / unload preserve the tree strucuture

\subsection{Relation over Generic \emph{Zipper}s}

+ Relation over dissections
+ Relation over recursive
+ Indexed relation
+ Proof of well foundedness

\subsection{Putting the pieces together}

+ unload to a smaller position by the relation
+ tail recursive fold
+ correctness for free by indexed 
+ The proof holds

%} end of generic.fmt

>>>>>>> master
\section{Conclusion and future work}

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


%% Bibliography
\bibliography{main}



%% Appendix
\appendix
\section{Appendix}

Text of appendix \ldots

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "lagda2pdf"
%%% End:


