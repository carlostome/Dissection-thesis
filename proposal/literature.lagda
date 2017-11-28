%include polycode.fmt
%include proposal.fmt

\section{Literature review}

\subsection{A universe for functors}

The common approach in a dependently typed setting such as \Agda~is to represent
functorial types using a universe construction. The construction is given by a
type of descriptions |FDesc| and an interpretation function
|fun (⟦_⟧₁) : FDesc -> (Set -> Set)|.

With \AD{FDesc} we can encode the identity functor, \AI{I₁}; the konstant
functor \AI{K₁}; coproduct ,\AI{+₁}, and product of functors
\AI{×₁}.  We relay on the sum \AD{⊎} and (non dependent) product type \AD{×}
from the standard library to interpret products and coproducts.

\InsertCode{Proposal/FDesc.tex}{FDesc}

We can witness that the construction above |langle FDesc ,| |fun (⟦_⟧₁)| |rangle| 
serves to faithfully represent functors by showing that it is possible to lift
functions, and that the functor laws are respected.

\InsertCode{Proposal/FDesc.tex}{fmap}

As a first example on how to work with |FDesc|, we recall the usual definition
of the Maybe type used to representing comptations that may not succeed.

\InsertCode{Proposal/FDesc.tex}{Maybe}

Maybe is a functor and can be encoded by a a description such as 


We can witness that Maybe is a functor by implementing a fmap function that
allows us low lift functions over and proving that they fulfil the functor laws.
However,

% Because |Maybe| is a functorial type, we can describe it using the following |FDesc|.

% We can for a simple type as maybe

% \InsertCode{Proposal/FDesc.tex}{Maybe}
% %%% include snippets/Proposal.FDesc.Maybe-Example-FDesc

% \todo{Embbed-projection pair?}

% \subsubsection{Functorial types}

% The |FDesc| universe provides a basic set of combinators from which we can build
% a functorial type. Because the resulting type is a functor, we should also be
% able to lift any function working on type |A| and |B|, |A -> B|, to work on the
% functor itself. This is commonly known as the fmap operation.

% \InsertCode{Proposal/FDesc.tex}{fmap}

% \todo{Maybe include the functor laws?}

% \subsubsection{Recursive types}

% The |FDesc| description type is somewhat limited in the sense that it is not
% suitable to describe recursive datatypes. However, we can exploit the fact that
% recursive types can be characterized as the fixpoints of polynomial functors
% \cite{BirddeMoor96:Algebra}.

% It is mandatory to remember that fixpoints in general do not necessarily
% terminate and thus if we try to directly encode it in Agda the termination
% checkerwill give us the red flag. Therefore, instead of a general fixpoint type
% we specialize it to the |FDesc| type.

% \InsertCode{Proposal/FDesc.tex}{mu}
% \InsertCode{Proposal/FDesc.tex}{cata-nt}
% \InsertCode{Proposal/FDesc.tex}{cata}

% %%% include snippets/Proposal.FDesc.Mu

% %%% include snippets/Proposal.FDesc.Nat-Example

% %%% include snippets/Proposal.FDesc.cata-nt

% %%% include snippets/Proposal.FDesc.cata

% \subsubsection{Catamorphism}

% \subsection{Universe for bifunctorial types}

% %%% include snippets/Proposal.BiFDesc.BiFDesc

% %%% include snippets/Proposal.BiFDesc.Interpretation

% %%% include snippets/Proposal.BiFDesc.Either-Example

% %%% include snippets/Proposal.BiFDesc.bimap

% %%% include snippets/Proposal.BiFDesc.Origami

% %%% include snippets/Proposal.BiFDesc.BTree-Example

% \todo{Include cata/fold for μ₂?}

% subsection{Dissection}
% \todo{some pictures of trees}

% \InsertCode{Proposal/Dissection.tex}{Dissection}
% \InsertCode{Proposal/Dissection.tex}{right}
% \InsertCode{Proposal/Dissection.tex}{tcata}

