%include polycode.fmt
%include proposal.fmt

\section{Literature review}

\subsection{A universe for functors}

As it is commonly done in the dependently typed setting, we shall employ a
universe construction to encode  functorial types along with an interpretation
function that converts a \textbf{code} into a functor.

\InsertCode{Proposal/FDesc.tex}{FDesc}

\todo[inline]{Do we want full K or just 0 and 1 and some Iso,
              for doing dissection it doesn't matter as we only make use
              of 1 or 2 also for bifunctors}

The inhabitants of the description type \AD{FDesc} match one-to-one with the
inhabitants of the described type. We can witness such, by defining an
interpretation function that maps an element of type \AD{FDesc} into an element of
type |Set -> Set|.

\InsertCode{Proposal/FDesc.tex}{Interpretation}

As a first example, we recall the usual definition for the type of computations
that may not succeed.

%%% include snippets/Proposal.FDesc.Maybe-Example-Type

Because |Maybe| is a functorial type, we can describe it using the following |FDesc|.

We can for a simple type as maybe

\InsertCode{Proposal/FDesc.tex}{Maybe}
%%% include snippets/Proposal.FDesc.Maybe-Example-FDesc

\todo{Embbed-projection pair?}

\subsubsection{Functorial types}

The |FDesc| universe provides a basic set of combinators from which we can build
a functorial type. Because the resulting type is a functor, we should also be
able to lift any function working on type |A| and |B|, |A -> B|, to work on the
functor itself. This is commonly known as the fmap operation.

\InsertCode{Proposal/FDesc.tex}{fmap}

\todo{Maybe include the functor laws?}

\subsubsection{Recursive types}

The |FDesc| description type is somewhat limited in the sense that it is not
suitable to describe recursive datatypes. However, we can exploit the fact that
recursive types can be characterized as the fixpoints of polynomial functors
\cite{BirddeMoor96:Algebra}.

It is mandatory to remember that fixpoints in general do not necessarily
terminate and thus if we try to directly encode it in Agda the termination
checkerwill give us the red flag. Therefore, instead of a general fixpoint type
we specialize it to the |FDesc| type.

\InsertCode{Proposal/FDesc.tex}{mu}
\InsertCode{Proposal/FDesc.tex}{cata-nt}
\InsertCode{Proposal/FDesc.tex}{cata}

%%% include snippets/Proposal.FDesc.Mu

%%% include snippets/Proposal.FDesc.Nat-Example

%%% include snippets/Proposal.FDesc.cata-nt

%%% include snippets/Proposal.FDesc.cata

\subsubsection{Catamorphism}

\subsection{Universe for bifunctorial types}

%%% include snippets/Proposal.BiFDesc.BiFDesc

%%% include snippets/Proposal.BiFDesc.Interpretation

%%% include snippets/Proposal.BiFDesc.Either-Example

%%% include snippets/Proposal.BiFDesc.bimap

%%% include snippets/Proposal.BiFDesc.Origami

%%% include snippets/Proposal.BiFDesc.BTree-Example

\todo{Include cata/fold for μ₂?}

subsection{Dissection}
\todo{some pictures of trees}

\InsertCode{Proposal/Dissection.tex}{Dissection}
\InsertCode{Proposal/Dissection.tex}{right}
\InsertCode{Proposal/Dissection.tex}{tcata}

\section{Termination}

Following the Curry-Howard correspondence, if types are to be interpreted as
propositions and terms inhabiting them as their proofs then termination of terms
is customary to keep the logic consistent. A non terminating term such as
|non-term = non-term| could stand as a proof for any proposition (respectively
as an inhabitanat of any type) thus even a false proposition would have a proof
backing its truth!


Moreover, in the dependently typed setting where types can and may depend on terms,
termination of terms also ensures decidability of the typechecking
procedure.\arewesure{decidability really depends on termination?}

Systems based on different flavours of dependent type theory such as Agda or Coq
\referenceneeded{Agda Coq} 


The traditional approach to ensure termination in systems implementing type
theory is to restrict the kind of programs that would pass the typechecker.

By only allowing the user to write function that when performing a recursive
call this must be made in a structural smaller argument.


where structural smaller means that a
constructor or more must be peleed of before performing the recursive call.

As a first example the implementation of Euclides algorithm for computing the
greatest common division is analyzed. We state its definition in the following
snippet.

In the rest of this section we explore various techniques to approach the
termination problem in type theory.

\subsection{Sized types}

Sized types are a type-based termination checkerk

\subsection{Well founded relation}

\subsection{Bove-Capretta}

\section{Step back}
