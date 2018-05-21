
\documentclass[sigplan,10pt,review]{acmart}

%include preamble.tex
%include paper.fmt

% fontsize of code snippets
\renewcommand\hscodestyle{%
   \setlength\leftskip{0.25cm}%
   \footnotesize
}

\begin{document}

\title{Dissection: verified and terminating}

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
%{ begining of intro.fmt
%include intro.fmt

Folds, or \emph{catamorphisms}, are a pervasive
programming pattern. A fold generalizes many simple traversals over an
algebraic data type. Functions implemented by means of a fold are
\emph{compositional} and structurally recursive. Consider, for
instance, the following expression data type, written in the
dependently typed programming language Agda\todo{citation}:

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
calls and sums their results. Such a function can be implemented by a
fold, passing the addition and identity functions as the argument
algebra.

Unfortunately, not all in the garden is rosy. The operator |plusOp|
needs both of its parameters to be fully evaluated before it can
reduce further. When evaluating large expressions, the size of the
stack used during execution grows linearly with the size of the input,
potentially leading to a stack overflow, causing the execution of the
program to halt unexpectedly.

To address this problem, we can manually rewrite the evaluator to be
\emph{tail recursive}. Modern compilers typically map tail recursive
functions to machine code that runs in constant memory. To write such
a tail recursive function, we need to introduce an explicit stack
storing both intemediate results and the subtrees that have not yet
been evaluated. We can define such a stack as follows:

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
  this relation, we prove that it agrees with the |eval| function on
  all inputs.
\item We generalize this construction, inspired by McBride and Danvy's
  work on calculating abstract machines from their recursive
  counterparts. To do so, we define a universe of algebraic data types
  and a generic fold operation
  (Section~\ref{sec:universe}). Subsequently we show how to turn any
  structurally recursive function defined using a fold into its tail
  recursive counterpart (Section~\ref{sec:dissection}).
\item Finally, we sketch how the proofs of termination and semantics
  preservation from our example are generalized to the generic fold
  over arbitrary types in our universe
  (Section~\ref{correctness}).

\end{itemize}

All the constructions and proofs presented in this paper have been
implemented in and checked by Agda. The corresponding code is freely
available online.\footnote{\todo{url}}


\section{Termination and tail-recursion}
\label{sec:basics}
The functions |load| and |unload| are marked as non terminating
because they are not defined by structural recursion over their
arguments. In particular, the stack passed as an argument to the
recursive call of |load| in the definition of |unload| is structurally
equal in size as the input stack.

Intuitively, |load| and |unload| fold the tree by traversing it from
its leftmost leaf to its rightmost using the stack to store both
partial results and the remaining subtrees to fold them as
neccesary. The problem arises because the stack is simply typed and
any information about how the subtrees kept in the stack relate to
each other and to the original tree is lost once a subtree is inserted
onto the stack.

However, it is clear that virtually every node (either leaf or not)
from the original tree is visited at most twice during the
computation. First when the function |load| decomposes it looking for
its leftmost leaf and a second time when |unload| is accumulating over
the stack searching for another subtree to continue. This process is
depicted in figure 1.

\begin{figure}[h]
  \includegraphics[scale=0.25]{figure1}
\end{figure}

We can argue that because there are finitely many nodes on a tree,
|load| and |unload| neccesarily terminate. The question is now, How
can we encode this information in such a way that Agda understand that
the fold terminates?

The idea is that |load| and |unload| should not fold the full input
tree in one go, but instead they will perform one step of the
computation at a time.  Morover, by defining them by structural
recursion over their arguments now they are classified as terminating
by the termination checker.

\begin{code}
  load : Expr -> Stack -> Nat * Stack
  load (Val n)      stk = (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)

  unload : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload v   Top             = inj2 v
  unload v   (Right v' stk)  = unload (v' + v) stk
  unload v   (Left r stk)    = inj1 (load r (Right v stk))
\end{code}

For example, if we take the same tree in figure 1, after |load| finds
the initial leftmost leaf we can apply one step of the new |unload|
that will end up in the next leaf to the right.


\begin{figure}[h]
  \includegraphics[scale=0.25]{figure2}
\end{figure}

A tail recursive fold corrensponds to repeatedly applying the function
|unload| until we find a |inj2| whose value is the result of folding
the tree.
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top)
    where
      nrec : (Nat * Stack) -> Nat
      rec (n , stk) with unload n stk
      ... | inj1 z' = nrec z'
      ... | inj2 r = r
\end{code}

The function |tail-rec-eval| still does not pass the termination
checker, The variable |z'| is not structurally smaller than |(n ,
stk)|. However, now we can refine it by using well founded recursion
to make it structurally recursive by performing the recursion over the
accessibility predicate instead of the pair |Nat * Stack|.

\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top) ??1
    where
      rec : (z : Nat * Stack) -> Acc ltOp z -> Nat
      rec (n , stk) (acc rs) with unload n stk
      ... | inj1 z' = rec z' (rs ??2)
      ... | inj2 r = r
\end{code}

For the function above to work, we need to find a suitable definition
for the relation |ltOp| over pairs of |Nat * Stack|, prove that
applying |unload| results in an smaller element by the relation and
finally show that the relation is |Well-founded|, so the call to |rec|
can be made in the first place. Before any of that, we need to revisit
Huet's notion of \emph{Zipper} and show how it relates to what we are
trying to achieve.

\subsection{Zippers up, Zippers down}

Huet introduced \emph{Zippers} to allow a tree datastructure to be
efficiently updated in a purely functional way. The idea is that any
location on a tree, either an internal node or a leaf, can be
represented by a path to the root and the subtree that hangs
downwards.

The pair |Nat * Stack| used to compute the tail recursive fold is
nothing more that a restricted version of the \emph{Zipper} where the
locations can only be leaves of the tree.

\begin{code}
  Zipper : Set
  Zipper = Nat * Stack
\end{code}

From a |Zipper| we have to be able to reconstruct the original |Expr|
which will be neccesary later on for the proof that the relation is
well founded. For this matter, we have to enhance the type of stacks
to store not only the partial results but also the expressions that
where consumed in order to produce them.

\begin{code}
  Stack : Set
  Stack = List (Expr U+  (Sigma Nat lambda n ->
                          Sigma Expr lambda e -> eval e == n))
  pattern Left t        = inj1 t
  pattern Right n t eq  = inj2 (n , t , eq)
\end{code}

The original expression for which a |Nat * Stack| represents a
position can be reconstructed by forgeting that some part has already
been evaluated.

\begin{code}
  plugup : Expr -> Stack -> Expr
  plugup e []                      = e
  plugup e (Left t        :: stk)  = plugup (Add e t) stk
  plugup e (Right n t eq  :: stk)  = plugup (Add t e) stk

  plugZup : (Nat * Stack) -> Expr
  plugZup (n , stk) = plugup (Val n) stk
\end{code}

Our goal is to impose an ordering relation over elements of |Zipper|
such that for any input the |unload| function delivers a |Zipper| that
is smaller by the relation when it does not terminate with a
value. Because the folding happens from left to right, we want the
relation to order the leaves of the tree accordingly, so the leftmost
leaf is the greatest element and the rightmost the smallest. Using the
example from before, we number the leaves as follows:

\begin{figure}[h]
  \includegraphics[scale=0.25, angle=90]{figure3}
\end{figure}

Using the |Stack| as a path from the leaf to the root of the tree is
difficult if not impossible to encode a smaller than relation that
does not relate any two elements. Such relation has to be defined by
induction on the |Stack| part of the |Zipper|. But for any two given
stacks a priori we cannot know how many layers we have to peel in
order to reach a case where one of them is obviously smaller that the
other.

We can approach the problem by understanding the |Stack| not as a path
from the leaf up to the root but from the root down to the leaf. This
change of perspective is realised with a new plug function that does
the opposite of |plugup|.

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
  around only requires to use BLABLA of |reverse|}:

\begin{code}
  plugdown-to-plugup  : forall (e : Expr) (stk : Stack)
                      → plugdown e stk ==  plugup e (reverse stk)
\end{code}


Why do we need this equivalence? The bottom up view of a |Zipper| is
suitable for defining the tail recursive fold, alas to prove
termination we have to use use the top down view to describe the
relation we need.

\subsection{A relation on Zipper}

The relation over elements of |Zipper| is defined by induction on the
|Stack|.  If we start in the root of the tree, we can navigate
downwards both stacks in parallel removing their common prefix. Once
we find an |Add| where they disagree then whether the first |Zipper|
is located in the left or right subtree fully determines if its bigger
or smaller than the other |Zipper|.  The following type accounts for
this explanation:

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

Having the relation defined, we turn our focus to prove that it is
well founded.  This is an important step towards filling the holes
that were left open in the function |tail-rec-eval|.

A relation is well founded iff all the descending chains starting from
an arbitrary element are finite. In a theorem prover such as Agda, an
alternative definition of well foundedness is used which is based on
an accesibility predicate.

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

\subsection{Correctness}
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


\subsection{Dissection}

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

The last line of the definition is the interesting one. To \emph{dissect} a
product of things we either \emph{dissect} the left component pairing it with
the second component interpreted over the second variable |Y|; or we
\emph{dissect} the second component and pair it with the first interpreted over
|X|. This \emph{or} is what will give us all the possible combinations.

Having a \emph{dissection}, |R X Y|, we can show that we can reconstruct the
original structure by \emph{plugging} operation given a element of type |X| to
plug in the hole. However, the type |X| does not need to agree with |Y| as long as
we can recover |X|s from |Y|s.

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

\todo[inline]{STOP HERE}
Recalling from before, a stack represents a path either from the root of the
tree to a leaf or from the leaf to the root. Each element of the stack is a
value that represents a node with a hole on it. For example, in the case of
|Expr| the |Left| constructor stands for a |Add| without the left subexpression.

McBride main contribution in BLABLA, is to show that we can define a syntactic
operation over codes of type |Reg| to calculate the type of elements in the
stack for the generic case.


The first step to derive a generic solution is to define what means in the
generic case to be a
stack
For the type of expressions it was easy to define a datatype that allows us to
distinguish a hole

  + Dissection as generically calculate the type of stacks in agda
  + Plug
  + Zipper up Zipper down
  + relation on dissection?
  + Make clear the separation between recursion in the functor level and
  the fix level

%} end of generic.fmt

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


