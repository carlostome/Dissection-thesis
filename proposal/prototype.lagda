\section{Prototype implementation}

As a first approximation to the problem, we restrict our attention to the case
of traversing a tree-like structure from left to right in a tail-recursive
fashion. The most simple form of a tree-like structure is the type of skeleton
binary trees (binary trees without values).

\InsertCode{Proposal/Tree/Base.tex}{Tree}

Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any position in
the tree can be represented as a pair of a subtree and a stack that holds all
the trees in the path to the root.

\InsertCode{Proposal/Tree/Base.tex}{Stack}

Given a value of type \AD{Zipper} it is possible to plug them together to
reconstruct the original tree.

\InsertCode{Proposal/Tree/Base.tex}{BUPlug}

Navigating one position to the right on the tree can be easily defined.
However, we cannot directly encode a function that calculates the rightmost
position of the tree. \Agda~'s termination checker is not able to classify the
function as terminating because it has no evidence that the argument to the
recursive call \AB{z₁} is structurally smaller than \AB{z}.

\InsertCode{Proposal/Tree/Base.tex}{BURight}
\vspace*{-0.75cm}
\InsertCode{Proposal/Tree/Base.tex}{BUIterate}
\todo{tweak the color for TERMINATION}

We can alleviate the situation by defining a relation \AD{<} over elements of
the \AD{Zipper} type, and prove that whenever the evaluation of \AF{right}
\AB{z} yields a \AI{just}\AS{}\AB{z₁} then \mbox{\AB{z₁}\AS{}\AD{<}\AS{}\AB{z}}. If the
relation is \textit{well founded} we can use structural recursion on the
accessibility predicate to define \AF{rightmost}. Such relation shall consider
positions on the left subtree of a node bigger than the node itself which at the
same time is bigger than any position in its right subtree.

\todo{Maybe explain here why the well founded and not sized neither Bove}

With a representation where the \AD{Stack} denotes the path from the
subtree up to the root does it is not clear how to define a \emph{well
founded} relation\footnote{We have done several attempts, but none successful.}.

\todo{include a more detailed explanation why we even failed to define a
relation :)}

Alternatively, we can think of the \AD{Stack} as a path from (instead of to) the
root of the tree to the position. With this change of view a plugging operator
can also be defined. Converting between both representations amounts to reverse
the \AD{Stack}.

\InsertCode{Proposal/Tree/Base.tex}{TDPlug}

A relation between elements of \AD{Zipper} can be now constructed. The main idea
behind is that if we have two positions of the same tree the relation looks for
the points where both stacks diverge.

\InsertCode{Proposal/Tree/Base.tex}{TDRel}

In order to prove that the relation we just defined is well founded we need to
introduce a new relation that makes explicit the tree that a Zipper plugs to.

\InsertCode{Proposal/Tree/Base.tex}{TDRelIx}
\InsertCode{Proposal/Tree/Base.tex}{WF}
\InsertCode{Proposal/Tree/Base.tex}{Theorem}
% \InsertCode{Proposal/Tree/Base.tex}{TDRelIx}
% This representation allows us to build a new datatype that relates 
