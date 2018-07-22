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
spelled out, most of the proofs were completed by straightforward induction. The
correctness of the tail-recursive machine was immediately obvious from the usage
of type-indexed configurations and a type-indexed step function.

The termination proof we have given defines a well-founded relation and shows
that this decreases during execution. There are other techniques for writing
functions that are not obviously structurally recursive, such as the
Bove-Capretta method\\*\citep{bove}, partiality monad~\citep{partiality}, or
coinductive traces\\*~\citep{nakata}. In contrast to the well-founded recursion used
in this thesis, however, these methods do not yield an evaluator that is directly
executable, but instead defer the termination proof. Given that we can---and
indeed have---shown termination of our tail-recursive abstract machines, the
abstract machines are executable directly in \Agda.

The use of \Agda~as the formalization language keeps us honest. Skipping parts of
a proof is a standard procedure in hand-written mathematics. However, in a
theorem prover such as \Agda~we have to be completely honest: to prove every
theorem and lemma we have to reason up to the most concrete detail. In return,
we can be certain---as certain as we trust \Agda's implementation to be
correct---that when a program (or proof) typechecks then it is
\emph{mathematically} true. We know once and for all that the abstract machine
terminates and is correct; no amounts of testing can ever provide a more
definite and convincing argument. In addition, the type theory underlying \Agda~
is constructive. A theorem can be interpreted as function that transforms inputs
into outputs. Within our work, we can appreciate this in the fact that the proof
of a relation being \emph{well-founded} implies that we can construct the
accessibility predicate mechanically for any term in the domain of the relation. 

However, using \Agda~has also its drawbacks. The experience working with it as
an interactive proof assistant is far from ideal: typechecking big modules is
rather slow; most of the theorems and functions are tightly coupled with the
inductive structure of the input and a simple change in the definition of the
datatype results in massive changes to the codebase; irrelevance in \Agda~is very
primitive, for example we cannot have functions that purely work on the
irrelevant side, thus, its application is limited.

There are several directions in which this thesis could be further developed.
First, the choice of universe. As we mentioned in
\cref{subsec:background:regular,chap:generic}, we chose to build our generic
tail-recursive machine in the regular universe because of practical reasons.
However, the development presented in this thesis can be taken as a recipe to
build tail-recursive machines for other universes. The key points of our
construction are: we restrict the \emph{zippers}, or configurations of the
abstract machine, to leaves of the generic tree; we interpret the stack both
top-down or bottom-up depending whether it is used for computation or for
termination proofs; we define a function that performs one step of the fold and
it obviously terminates; we define a relation over configurations that decreases
in each invocation of the step function, and we prove it to be well-founded.
Indexing the relation by the input tree is essential to complete the proof of
well-foundedness. In addition, correctness of the machine follows almost
directly from having the type of configurations indexed by the input tree.

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
self-evident choice. However, \cite{fokkinga1994monadic} shows that not all
monads are suitable for a monadic catamorphism that fulfils some expected laws.
If we need a more systematic approach to construct the monadic catamorphism,
we would also require some extra work to develop an equivalent monadic
tail-recursive machine.

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
dependent types, but programming with them in \emph{Coq} is inherently
complex~\citep[chap 8]{chlipala2011certified}. Thus, it is not clear how
suitable \emph{Coq} is for implementing the generic tail-recursive catamorphism.

%{
%format eval = "\AF{eval}" 
%format Add = "\AI{Add}"
In recent years, there has being an ongoing effort in bringing dependent types
from the researchers ivory tower into real world programming languages. The
benefits are clear: we can use the same language to write a specification, an
implementation, and prove that the implemented program satisfies its
specification. For instance, we can understand the fold over a datatype as the
specification of a problem; the function |eval| states that evaluating an |Add|
expression is equal to the addition of the results of evaluating its
subexpressions. Computing directly using the specification, however, is not
ideal; |eval| is not a tail-recursive function. Specifications must be simple
enough to be obviously correct, consequently, when used as programs they are not
as efficient as they could be. In our example, we wrote a tail-recursive
function---the implementation---that we later proved to be equivalent to |eval|;
that is, the program satisfied its specification. Termination of all programs
written in \Agda~is mandatory, otherwise, the proofs of correctness could not be
trusted. This is a high toll for the widespread adoption of dependent types in
software development. There are many programs that terminate but are not, or
cannot, be defined by structural recursion. Our tail-recursive evaluators are a
representative example of such functions, yet, we exhibited how through a
carefully crafted well-founded relation we can prove the functions terminate. Building
upon the tail-recursive evaluator for the type of expressions, we showed how to
construct a provably correct tail-recursive catamorphism that works for any
datatype in the regular universe.  This proves the generality of our results; we
developed a recipe for constructing a terminating and correct abstract machine
and later we applied it to the regular universe. The resulting tail-recursive
abstract machine is an executable program that computes the catamorphism for any
algebra over any regular datatype. We believe that we can easily export this
recipe to a widespread range of generic universes to derive
correct-by-construction tail-recursive abstract machines equivalent to their
associated folds.
%}
