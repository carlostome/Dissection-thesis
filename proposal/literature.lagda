%include polycode.fmt
%include proposal.fmt

\section{Generic programming}

\subsection{A universe for functors}

The common approach in a dependently typed setting such as \Agda~is to represent
functorial types using a universe construction. The construction is given by a
type of descriptions |FDesc| and an interpretation function |fun (⟦_⟧₁) : FDesc
-> (Set -> Set)|.

With \AD{FDesc} we can encode the identity functor, \AI{I₁}; the konstant
functor \AI{K₁}; coproduct ,\AI{+₁}, and product of functors
\AI{×₁}.  We relay on the sum \AD{⊎} and (non dependent) product type \AD{×}
from the standard library to interpret products and coproducts.

\InsertCode{Proposal/FDesc.tex}{FDesc}

We can witness that the construction above |langle FDesc ,| |fun (⟦_⟧₁)| |rangle| 
serves faithfully to represent functors by showing that it is possible to define
\AF{fmap} and prove that the functor laws are respected.

\InsertCode{Proposal/FDesc.tex}{fmap}

\begin{example}
  As a first example on how to work with \AD{FDesc}, we recall the usual
  definition of the \AD{Maybe} type used to represent computations that may not
  succeed.

  \InsertCode{Proposal/FDesc.tex}{Maybe}

  \AD{Maybe} is a functor and so it can be encoded as a value of type \AD{FDesc}.

  \InsertCode{Proposal/FDesc.tex}{Maybe-Desc}

  Both the \AD{Maybe} type and its description \AF{Maybe'} interpreted as |Set
  -> Set| are equivalent.

  \InsertCode{Proposal/FDesc.tex}{Maybe-Witness}
\end{example}

The \AD{FDesc} description type is somewhat limited in the sense that it is not
suitable to describe recursive datatypes. However, we can exploit the fact that
inductive types can be characterized as the least fixed point of a polynomial
functor \cite{BirddeMoor96:Algebra}.

The idea is that the type variable can be used to mark the recursive positions
in the constructors of the datatype. The fixpoint then ties the knot by
replacing the marked positions with full trees.

For any functor |F : Set -> Set| we cannot construct directly the least fixed
point of it because |F| might send its argument type to a negative position.
Negative types are not allowed in \Agda~ because when avaliable they can be used
to derive a contradiction.

The \AD{FDesc} type of descriptions only allows to encode strictly positive
functors so we can specialize the fixpoint to interpretations of \AD{FDesc}.

\InsertCode{Proposal/FDesc.tex}{mu}

\begin{example}

  As an example of a recursive datatype we can use the type of natural numbers.

  \InsertCode{Proposal/FDesc.tex}{Nat}

  In this case the functor we choose uses its type variable to encode the
  recursive positions of the constructors. Sometimes this is called the base
  functor.

  \InsertCode{Proposal/FDesc.tex}{Nat-FDesc}

  We can witness that the least fixed point of the description above correspond
  in one to one to the definition of the natural numbers.

  \InsertCode{Proposal/FDesc.tex}{Nat-Witness}
\end{example}

\subsection{Partial derivative of a functor}

Polynomial functors closed under least fixed point describe recursive tree like
structures. Following the idea of a \AD{Zipper} for binary trees we should be
able to represent a position in the tree by a subtree and a list of
substructures that when \textit{plugged} reconstruct the original tree.

The type of substructures of a polynomial functor can be calculated by
\textit{partial differentiation}, as shown by
McBride\cite{Mcbride01thederivative}, on its syntactic description.

  \InsertCode{Proposal/Derive.tex}{Diff}


