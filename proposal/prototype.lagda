\section{Prototype implementation}

As a first approximation to the problem, we restrict our attention to the case
of traversing a tree-like structure from left to right in a tail-recursive
fashion. The most simple form of a tree-like structure is the type of skeleton
binary trees (binary trees without values).

\InsertCode{Proposal/Tree/Base.tex}{Tree}

Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any position in
the tree can be represented as a pair of a subtree and a stack that holds all
the trees, to the left and to the right, in the path to the root.

\InsertCode{Proposal/Tree/Base.tex}{Stack}

Given a value of type \AD{Zipper} it is possible to \emph{plug} the subtree and the
stack together to reconstruct the original tree.

\InsertCode{Proposal/Tree/Base.tex}{BUPlug}

Navigating one position to the right on the tree can be easily defined in a
tail-recursive manner.

\InsertCode{Proposal/Tree/Base.tex}{BURight}
\todo{maybe I should not include all}

However, we cannot directly encode a function that calculates the rightmost
position of the tree by iterating the \AF{right} function until it yields
\AI{nothing}.

\InsertCode{Proposal/Tree/Base.tex}{BUIterate}
\colored

Pattern matching on the result of \AF{right}\AS{}\AB{z} does not reveal any
structural relation between the input \AB{z} and \AB{z₁}. Thus \Agda~'s
termination checker correctly classifies the function as non-terminating. It
does not know in which sense the recursive call is made on a smaller argument.

Any position in the tree has a finite number of positions to the right of
itself. Each time we move one position to the \AF{right} this number decreases.
Using \emph{well founded} recursion, as explained in \cref{sec:termination}, we
can define a relation \AD{\_<\_}, over elements of \AD{Zipper}, that exposes the
decreasing structure of moving to the right.  Additionally, by proving
\textit{well foundedness} of the relation and the property that whenever the
evaluation of \AF{right} \AB{z} yields a \AI{just}\AS{}\AB{z₁} then
\mbox{\AB{z₁}\AS{}\AD{<}\AS{}\AB{z}}, we will be able to define \AF{rightmost}
by structural recursion on the accessibility predicate of \AD{\_<\_}.

\InsertCode{Proposal/Tree/Base.tex}{Skeleton}

The purpose of the following subsections is to show how we can fill
the open holes and the definition of \AD{\_<\_}.

\colored

\subsection{Defining the relation}

The relation we want to define shall consider positions on the left subtree of a
\AI{Node} bigger than the \AI{Node} itself which at the same time is bigger than
any position in its right subtree.

\todo{a picture here?}

Following Huet's idea, we regard the \AD{Stack} type as a path going
\textit{backwards} from the position of the subtree up to the root. The relation
has to be inductively defined on the \AD{Stack} part of the \AD{Zipper}.
Removing a constructor from the \AD{Stack} means moving up a position on the
tree. For any two arbitrary positions on the tree, we cannot determine a priori
from which one we have to move up on the tree to reach a base case. Because of
this, we need to consider all the possible situations. This in fact will allow
us to prove that any two positions of the tree are related in both directions of
. The relation will then be useless.  Because of this, the \textit{backwards}
representation is not well suited for the definition of \AD{\_<\_}.

\rewrite

As an alternative, we can consider the \AD{Stack} as the \textit{forward} path
from the root to the position where the subtree is located. We can have another
\emph{plug} operator to reconstruct the original tree.

\InsertCode{Proposal/Tree/Base.tex}{TDPlug}

The new representation for positions is better suited for defining the relation.
However, our purpose is to traverse the tree in a tail-recursive manner for
which the \textit{backward} representation is a more natural fit.  Converting
from one to the other amounts to reverse the \AD{Stack}. Additionally, plugging
should yield the same original tree in both directions.

\InsertCode{Proposal/Tree/Base.tex}{Convert}

The main idea to construct the relation is to look for the point where the left
and right \AD{Stack} diverge. The manner in how they diverge defines which
element is smaller.

\InsertCode{Proposal/Tree/Base.tex}{TDRel}

Moreover, by including information that relates the subtrees on the \AD{Stack}
to the original tree it is easily proven that whenever two elements of
\AD{Zipper} are related by < they represent positions of the same tree.

\InsertCode{Proposal/Tree/Base.tex}{Related}

\subsection{Proving \textit{well foundedness}}

As explained in \ref{subsec:wf}, in order to prove the \emph{well foundedness}
property for a relation either the input or the proof needs to be structurally
smaller for the recursive call. 
The naive approach to prove that \AD{\_<\_} is \textit{well founded} fails. 

evidently structurally smaller than the input or 
\Agda~that some structure isrecursion,as explained in \ref{sec:termination}, requires us to
show \Agda~that any recursive call to the well-foundedness property we are
trying to prove has to be made in --evidently-- structurally smaller arguments.

Because of
this, if we try to prove directly that \AD{\_<\_} is \textit{well founded} we
will miserably In the base cases we are not able to make a recursive call
to the well foundedness property because again is not explicit that the zipper
is smaller.

This realisation motivates us to make explicit in the relation the tree for
which the values of \AD{Zipper} in \AB{z}\AS{}\AD{\_<\_}\AS{}\AB{z₁} plug to.

\InsertCode{Proposal/Tree/Base.tex}{TDRelIx}


provide an explicit
- The relation as it is we cannot show it is accesible
- In the base cases we need to recurse on something Agda can see is structurally
smaller.
- Thus we may be tempted to include such information in the proof. However, we
are not proving well foundedness anymore.
- Instead we can define a relation over Zipper that has the tree they plug to as
an index.
- We rely on the other relation but the proofs are explicit.
- We can patternmatch on them to show where is the decreasing structure.
- Thus we can prove well founded ness.

We need also to show that the relation is well founded. In order to do so
normally we would try to prove directly well foundedness over <. However, the
definition of Accesibility doesn't know that both trees plug to the same subtree
and that when we reach the base cases we can perform recursion over some smaller
tree. To reveal this information to agda we shall encode another relation
between zippers that makes this connection explicit. Thus in the proof for well
foundedness the structure is revealed and we can use recursion.

\InsertCode{Proposal/Tree/Base.tex}{WF}

\subsection{Navigating through the tree}

% \InsertCode{Proposal/Tree/Base.tex}{TDRelIx}
% This representation allows us to build a new datatype that relates 
