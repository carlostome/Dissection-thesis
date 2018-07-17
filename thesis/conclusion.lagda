%include conclusion.fmt
\chapter{Conclusions and future work}
\label{chap:conclusion}

In this master thesis, we presented the derivation of a generic tail-recursive
machine capable of computing the catamorphism of any algebra for any regular
datatype. Moreover, we proved our tail-recursive machine to be both terminating
and correct with respect to the catamorphism. We formalized the work discussed
in this thesis in the dependently typed programing language \Agda, only using
the sound and complete parts of the language: our construction does not require
the utilization of any exotic termination flags or extraneous postulates.

We have developed two abstract machines, one for the type of binary trees with
natural numbers in the leafs and another for any datatype representable in the
regular universe. We have shown how the construction of the latter machine
follows the same steps to those of the former. By doing so we tried to motivate
the design choices made in the generic setting; it is always hard to reason
alone about generic constructions because of their abstract nature. The most
complicated part of our development was to find the appropriate predicates and
lemmas that allowed us to show termination; once the properties were correctly
spelled, they mostly followed by induction over their arguments.The correctness
of the tail-recursive machine was immediately obvious from the usage of
type-indexed configurations and a type-indexed step function.

The termination proof we have given defines a well-founded relation and shows
that this decreases during execution. There are other techniques for writing
functions that are not obviously structurally recursive, such as the
Bove-Capretta method\\*\citep{bove}, partiality monad~\citep{partiality}, or
coinductive traces\\*~\citep{nakata}. In contrast to the well-founded recursion used
in this thesis, however, these methods do not yield an evaluator that is directly
executable, but instead defer the termination proof. Given that we can---and
indeed have---shown termination of our tail-recursive abstract machines, the
abstract machines are executable directly in \Agda.

The use of \Agda~as the formalization language is not casual. Skipping parts of
a proof is a standard procedure in hand-written mathematics. However, in a
theorem prover such as \Agda~we have to be completely honest: to prove every
theorem and lemma we have to reason up to the most concrete detail. In return,
we can be certain---as certain as we trust \Agda's implementation to be
correct---that when a program (or proof) typechecks then it is
\emph{mathematically} true. We know once and for all that the abstract machine
terminates and is correct; no amounts of testing can ever provide a more
definite and convincing argument. In addition, the type theory underlying Agda
is constructive. A theorem can be interpreted as function that transforms inputs
into outputs. Within our work, we can appreciate this in the fact that the proof
of a relation being \emph{well-founded} implies that we can construct the
accessibility predicate mechanically for any term in the domain of the relation. 

However, using \Agda~has also its drawbacks. The experience working with it as an
interactive proof assistant is far from being ideal: typechecking big modules is
rather slow; most the theorems and functions depend on the inductive structure
of the input and a simple change in the definition of the datatype results in
massive changes to the codebase; irrelevance in Agda is very primitive, for
example we cannot have functions that purely work on the irrelevant side, thus,
its application is limited.

There are several directions in which this thesis could be further developed.
First, the choice of universe. As we mentioned in
\cref{subsec:background:regular,chap:generic}, we chose to build our generic
tail-recursive machine in the regular universe because of practical reasons.
However, the development presented in this thesis can be taken as a recipe to
build tail-recursive machines for other universes.  The main insight we provide
is: restrict the \emph{zippers}, or configurations of the abstract machine, to
leaves of the generic tree; assume that the stack has to be interpreted both
top-down or bottom-up depending whether its used for computing or proving;
define a suitable relation over configurations that can be proven to be
well-founded because is type-indexed with the input tree.  Moreover, correctness
of the machine follows almost directly from having the type of configurations
indexed by the input tree.

The universe of regular types used in this thesis is somewhat restricted: we
cannot represent mutually recursive types~\citep{mutual}, nested data
types~\citep{nested}, indexed families~\citep{dybjer-inductive}, or
inductive-recursive types~\citep{induction-recursion}. Fortunately, there is a
long tradition of generic programming with universes in \Agda, arguably dating
back to \cite{martin-loef}. It would be worthwhile exploring how
to extend our construction to more general universes, such as the context-free
types~\citep{morris}, containers~\citep{containers,indexed-containers}, or the
`sigma-of-sigma' universe~\citep{power-of-pi,levitation}.  Doing so would allow
us to exploit dependent types further in the definition of our evaluators. A long
term goal of our work would be to export our development to a generic universe
capable of representing well-typed lambda calculus terms, and their evaluation
as a simple fold over the syntax. In such environment, we could derive a
tail-recursive evaluator automatically, rather than verifying the construction
by hand~\citep{krivine}.
 
Moreover, it would be worthwhile to explore how to use a well-founded argument
to show that other variety of recursion schemes, such as hylomorphisms,
histomorphisms, paramorphisms, etc~\citep{meijer1991functional}, can be turned
into provably terminating and correct tail-recursive functions. Another possible
path would be to derive a tail-recursive machine equivalent to an effectful fold
where the algebra determines the order of the effects involved. A common method
to encode effects in pure functional languages is to use
monads~\citep{wadler1998marriage}, thus, a monadic fold would be the
self-evident choice.

Marking some parts of the code as computationally irrelevant, such as the
relation or the proofs, is important to keep the resulting abstract machine both
tail-recursive and overhead free. The tail-recursive function that we derived is
`morally' tail-recursive but not practically: to show termination the step
function is executed by the recursor, but its result is then used to show
termination before actually recursing on the accessibility predicate. Ideally,
the derived machine should have the same runtime impact as if it was implemented
in a general purpose functional programming language, such as \Haskell.  At the
end of both \cref{chap:expression,chap:generic} we discussed about the
shortcomings of using irrelevance directly in \Agda. However, it should be
possible to export our construction to a more mature proof system such as
\emph{Coq} where the distinction between the parts of the code used for proving
and those used for computing can be clearly separated.  We could use the
impredicative universe \textbf{Prop} for the former while using the predicative
universe, \textbf{Type}, for the latter.  Nevertheless, it is well-known that
\emph{Coq} as a theorem prover excels for its capability of using the
dependently typed part of the language to prove properties about programs
expressed in the simply typed fragment. The generic machinery relies upon
dependent types, thus, it is not unambiguous how suitable is Coq for its
implementation.

