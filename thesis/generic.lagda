%include polycode.fmt
%include generic.fmt

\section{A verified generic tail-recursive catamorphism}
\label{sec:generic}
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
  eval = cata expr [ id , plusOp ]
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
  nabla : (R : Reg) → (Set → Set → Set)
  nabla Zero      X Y  = Bot
  nabla One       X Y  = Bot
  nabla I         X Y  = Top
  nabla (K A)     X Y  = Bot
  nabla (R O+ Q)  X Y = nabla R X Y U+ nabla Q X Y
  nabla (R O* Q)  X Y = nabla R X Y * interpl Q interpr Y U+ interpl R interpr X * nabla Q X Y
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
  data IxDissection (R : Reg) (X Y : Set) (eta : X → Y) (tx : interpl R interpr Y) : Set where
    prodOp : (d : Dissection R X Y) → plug R d eta == tx → IxDissection R X Y eta tx 
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
 record Computed (R : Reg) (X : Set) (alg : interpl R interpr X → X) : Set where
    constructor _,_,_
    field
      Tree   : mu R
      Value  : X
      Proof  : catamorphism R alg Tree == Value

\end{code}
\begin{code}
  Stack : (R : Reg) → (X : Set) → (alg : interpl R interpr X → X) → Set
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
               -> mu R -> Stack R X alg → mu R
  plug-mudown R t []         = t
  plug-mudown R t (h :: hs)  = In (plug R Computed.Tree h (plug-mudown R t hs))

  plug-muup  : (R : Reg) -> {alg : interpl R interpr X -> X}
             -> mu R → Stack R X alg → mu R
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
  data NonRec : (R : Reg) → interpl R interpr X → Set where
    NonRec-One  : NonRec One tt
    NonRec-K    : (B : Set) → (b : B) → NonRec (K B) b
    NonRec-+1   : (R Q : Reg) → (r : interpl R interpr X)
                → NonRec R r → NonRec (R O+ Q) (inj1 r)
    NonRec-+2   : (R Q : Reg) → (q : interpl Q interpr X)
                → NonRec Q q → NonRec (R O+ Q) (inj2 q)
    NonRec-*    : (R Q : Reg) → (r : interpl R interpr X) → (q : interpl Q interpr X)
                → NonRec R r → NonRec Q q → NonRec (R O* Q) (r , q)

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
\begin{code}
  coerce : (R : Reg) -> (x : interpl R interpr X) → NonRec R x -> interpl R interpr Y  
\end{code}

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
  Zipper : (R : Reg) → (X : Set) → (alg : interpl R interpr X → X) → Set
  Zipper R X alg = Leaf R X * Stack R X alg
\end{code}

Finally, we can recompute the original tree using a |plug| function as before:
\begin{code}
  plugZ-mudown : (R : Reg) {alg : interpl R interpr X → X} → Zipper R X alg → μ R →  Set
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
load  : (R : Reg) {alg : interpl R interpr X → X} -> mu R
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
  first-cps I Q (In x) k f s  = first-cps Q Q x id (lambda z  → inj1 . prodOp z) (k tt :: s)
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
none, a recursive call to |unload| is dispathed, otherwise, if there is still a subtree to be
processed the function |load| is called.

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

However, what is needed for the recursive call is: first, the functor
interpreted over values, | interpl R interpr X|, in order to apply the algebra;
second, the functor interpreted over subtrees, | interpl R interpr (mu R)|, to
keep the original subtree where the value came from; Third, the proof that the
value equals to applying a |catamorphism| over the subtree.  The function
|compute| massages |r| to adapt the arguments for the recursive call to |unload|.

\subsection{Relation over generic configurations}
\label{subsec:rel-gen}

We can engineer a \emph{well-founded} relation over elements of type |Zipperdown
t|, for some concrete tree |t : mu R|, by explicity separating the functorial layer
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
             -> IxDissection R X Y eta tx -> IxDissection R X Y eta tx → Set where


  data IxLtdown {X : Set} (R : Reg) {alg : interpl R interpr X -> X}  : (t : μ R) 
             -> Zipperdown R X alg t -> Zipperdown R X alg t -> Set where
\end{code}

The proof of \emph{well-foundedness} of |IxLtdown| is a straightforward generalization
of proof given for the example in \Cref{subsec:relation}. 
The full proof of the following statement can found in the accompanying code:
\begin{code}
  <Z-WF : (R : Reg)  -> (t : μ R) -> Well-founded (llcorner R lrcornerllcorner t lrcornerIxLtdown)
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
  step  : (R : Reg) → (alg : interpl R interpr X → X) -> (t : mu R)
        -> Zipperup R X alg t -> Zipperup R X alg t U+ X
\end{code}
We omit the full definition. The function |step| performs a call to |unload|,
coercing the leaf of type |interpl R interpr X| in the |Zipperdown| argument to
a generic tree of type |interpl R interpr (mu R)|.

We show that |unload| preserves the invariant, by proving the following lemma:
\begin{code}
  unload-preserves  : forall (R : Reg) {alg : interpl R interpr X → X}
                    → (t : mu R) (x : X) (eq : catamorphism R alg t == x) (s : Stack R X alg)
                    → (z : Zipper R X alg)
                    → forall  (e : μ R) → plug-muup R t s == e 
                              → unload R alg t x eq s == inj1 z → plug-muup R z == e
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
           → llcorner R lrcorner ((dr' , t')) <Nabla ((dr , t)) 
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
  step-<  : (R : Reg) (alg : interpl R interpr X → X) → (t : mu R)
          → (z1 z2 : Zipperup R X alg t)
          → step R alg t z1 == inj1 z2 → llcorner R lrcornerllcorner z2 lrcorner <ZOp z1
\end{code}

Finally, we can write the \emph{tail-recursive machine}, |tail-rec-cata|, as the
combination of an auxiliary recursor over the accessibility predicate and a top-level
function that initiates the computation with suitable arguments:
\begin{code}
  rec  : (R : Reg) (alg : interpl R interpr X → X) (t : mu R) 
       → (z : Zipperup R X alg t) 
       → Acc (llcorner R lrcornerllcorner t lrcornerIxLtdown ) (Zipperup-to-Zipperdown z) → X
  rec R alg t z (acc rs) with step R alg t z | inspect (step R alg t) z
  ... | inj1 x |  [ Is  ] = rec R alg t x (rs x (step-< R alg t z x Is))
  ... | inj2 y |  [ _   ] = y

  tail-rec-cata : (R : Reg) → (alg : interpl R interpr X → X) → mu R → X
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
  unload-correct  : forall  (R : Reg) (alg : interpl R interpr X → X)
                            (t : mu R) (x : X) (eq : catamorphism R alg t == x)
                            (s : Stack R X alg) (y : X)  
                  → unload R alg t x eq s == inj2 y
                  → ∀ (e : mu R) → plug-muup R t s == e → catamorphism R alg e == y
\end{code}
Our generic correctness result is an immediate consequence:
\begin{code}
  correctness  : forall (R : Reg) (alg : interpl R interpr X → X) (t : mu R)
               → catamorphism R alg t == tail-rec-cata R alg t
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

