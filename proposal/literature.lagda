%include lhs2TeX.fmt
%include polycode.fmt
%include proposal.fmt

\section{Literature review}

\subsection{Universe for functorial types}

Finite functorial types are all those types which having a finite number of inhabitants
can be described using the grammar

A simple manner to formalize the notion of finite functorial type is to use a
universe construction. We do so by using the \AD{FDesc} type in Agda.

\InsertCode{Proposal/FDesc.tex}{FDesc}
\todo{Do we want full K or just 0 and 1 and some Iso}

The inhabitants of the description type \AD{FDesc} match one-to-one with the
inhabitants of the described type. We can witness such, by defining an
interpretation function that maps an element of type \AD{FDesc} into an element of
type |Set -> Set|.

\InsertCode{Proposal/FDesc.tex}{Interpretation}

As a first example, we recall the usual definition for the type of computations
that may not succeed.

%%% include snippets/Proposal.FDesc.Maybe-Example-Type

Because |Maybe| is a functorial type, we can describe it using the following |FDesc|.

%%% include snippets/Proposal.FDesc.Maybe-Example-FDesc

\todo{Embbed-projection pair?}

\subsubsection{Functorial types}

The |FDesc| universe provides a basic set of combinators from which we can build
a functorial type. Because the resulting type is a functor, we should also be
able to lift any function working on type |A| and |B|, |A -> B|, to work on the
functor itself. This is commonly known as the fmap operation.


%%% include snippets/Proposal.FDesc.fmap

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

%%% include snippets/Proposal.Dissection.Dissection

%%% include snippets/Proposal.Dissection.right

%%% include snippets/Proposal.Dissection.tcata

\section{Step back}
