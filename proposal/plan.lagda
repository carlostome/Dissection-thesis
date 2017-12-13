%include proposal.fmt

\section{Plan}\label{sec:plan}

In the proposal phase of this master thesis we have studied the relevant
literature and implemented a first prototype that shows how it is possible to
define a \emph{well founded} relation over positions in a tree-like structure
for traversing the tree left to right. The next phase will consist on extending
the prototype, first to prove that a tail recursive fold terminates and then
that it is extensionally equivalent to the fold induced by the definition of the
datatype. Once we have solved the concrete problem over binary trees our aim is
to generalize the result to other tree-like datatypes by exploiting generic
programming techniques. We present a plan for the next steps to follow for the
rest of the thesis.

\subsection{Binary tree - Fold - Termination}

In our prototype we simplified the original problem of folding to traversing the
tree like structure. Our first objective is to define a tail-recursive fold. In
order to do so we will extend the \emph{well founded} relation over \AD{Zipper}
to cope with evaluation. A first step in this direction is described in
\cref{subsec:traverse-to-fold}.

\subsection{Binary tree - Fold - Correctness}

After proving termination for the function that computes a fold in a tail
recursive manner, the next step is to verify that this function is equivalent to
the fold induced by the type of binary trees. In order to do so, we will
probably need to add to the relation we defined for termination information that
allows us to relate the values denoted by subtrees to the full structure.

\subsection{\emph{Regular} type - Fold - Termination and Correctness}

The original motivation of this thesis is to explore how we can verify a tail
recursive fold using the idea of dissection. In this part of the work we will
generalize previous results over binary trees both for termination and
correctness to the \emph{Regular} tree universe as was presented in
\cref{sec:generic}.

\subsection{Generic programming - Generalize}\label{subsec:generalize}

Dissection as defined by McBride uses a \emph{Regular} type tree universe. This
universe is very limiting in the types that can express. We can try to apply the
idea of dissection to richer universes that for example allow us to represent
composed datatypes such a rose trees; nested datatypes such as perfect binary
trees; or mutually recursive datatypes.

The most promising direction is to use a universe for indexed functors as
presented by Löh and Magalhães\cite{genericindex}. Although they introduce the
idea of differentiation for indexed functors, they do not explore the notion of
dissection over that universe.

\subsection{Examples}\label{subsec:examples}

There are many examples in the literature about using a function defined as a
fold over a datatype to derive an abstract machine with the same semantics. 
Danvy \cite{Danvy2009}, shows how to derive a tail recursive abstract machine
starting with a reduction semantics for the type of arithmetic expressions.
\todo{finish this}
