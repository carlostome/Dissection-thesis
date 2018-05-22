\documentclass[sigplan,10pt,review]{acmart}

%include preamble.tex
%include paper.fmt

% fontsize of code snippets
\renewcommand\hscodestyle{%
   \setlength\leftskip{0.25cm}%
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

%include main.fmt

\section{Introduction}

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

%{
%format loadN   = "\nonterm{" load "}"
%format unloadN = "\nonterm{" unload "}"
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
%}

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
\item We generalize this construction, inspired by
  McBride~\cite{dissection}'s work on \emph{dissections}, to show how
  to calculate an abstract machine from an algebra. To
  do so, we define a universe of algebraic data types and a generic
  fold operation (Section~\ref{sec:universe}). Subsequently we show
  how to turn any structurally recursive function defined using a fold
  into its tail recursive counterpart (Section~\ref{sec:dissection}).
\item Finally, we sketch how the proofs of termination and semantics
  preservation from our example are generalized to the generic fold
  over arbitrary types in our universe
  (Section~\ref{correctness}). 
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
and repeatedly call |unload| until it returns a value.  This version
of our evaluator, however, does not pass the termination checker. The
new state, |(n' , stk')|, is not structurally smaller than the initial
state |(n , stk)|. If we work under the assumption that we have a
well-founded relation between the states |Nat * Stack| that decreases
after every call to |unload|, we can define the following version of
the tail recursive evaluator:
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top) ??1
    where
      rec : (z : Nat * Stack) -> Acc ltOp z -> Nat
      rec (n , stk) (acc rs) with unload n stk
      ... | inj1 (n' , stk') = rec (n' , stk') (rs ??2)
      ... | inj2 r = r
\end{code}

To complete this definition, we still need to define a suitable
well-founded relation |ltOp| between configurations of type |Nat *
Stack| and prove that the calls to |unload| produce smaller
states. Before we can do so, however, we need to revisit the
\emph{zippers} underlying this traversal.

\subsection*{Zippers up, Zippers down}

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

\subsection*{A relation on Zipper}

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

\todo[inline]{STOP HERE}

\section{Regular universe}
\label{sec:universe}
  + Universe interpretation generic programming
  + Fixpoint
  + Example??
\section{Dissection}
\label{sec:dissection}  
  + Dissection in agda
  + Plug
  + Zipper up Zipper down
  + Make clear the separation between recursion in the functor level and
  the fix level
  + relation on dissection?

\section{Termination and correctness, generically}
\label{sec:dissection}  

  
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


