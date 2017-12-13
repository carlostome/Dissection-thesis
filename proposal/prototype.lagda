\section{Prototype implementation}

  The purpose of this thesis is to formalize the notion of dissection and its
  usage to transform a fold into a tail-recursive function.

  The first step is to prove that it is possible to write a function that computes
  the fold of a non-linear (tree like) structure by tail recursion over a explicit
  stack and that this function terminates.

  This section is devoted to show that by using \emph{well founded} recursion we
  can solve a simplified version of the problem; that of traversing a tree from
  left to right. This simplification from folding to traversing a tree will not
  be an impediment to later generalize our results. A traversal can be
  conceptually thought as a fold that does nothing.

  The recursive structure of a inductive type is naturally defined in a top to
  bottom manner. However, the traversing function has to exploit the left to
  right inductive structure that is implicit in any tree-like type. For this
  reason we cannot directly write in \Agda~ the function that performs the
  traversal. The termination checker warns that it does not terminate because
  the argument is not --evidently-- structurally smaller.

  In \cref{sec:termination} we reviewed several well known techniques that can
  be used to assist \Agda's termination checker. \emph{Well founded} recursion
  is the only one that allows us to make evident the left to right inductive
  structure and provides us with a means for exploiting it.

\subsection{Trees and Zippers}

  Any tree-like datatype shares a common branching structure with the type of
  skeleton binary trees. We will use this type as the basis of our work.

  \InsertCode{Proposal/Tree/Base.tex}{Tree}

  Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any position
  in the tree can be represented as a pair of a subtree and a stack that holds
  all the trees, to the left and to the right, in the path to the root.

  \InsertCode{Proposal/Tree/Base.tex}{Stack}

  Given a value of type \AD{Zipper} it is possible to \emph{plug} the subtree
  and the stack together to reconstruct the original tree.

  \InsertCode{Proposal/Tree/Base.tex}{BUPlug}

  Navigating one position to the right on the tree can be easily defined in a
  tail-recursive manner.

  \InsertCode{Proposal/Tree/Base.tex}{BURight}

  However, it is not possible to write a function that calculates the rightmost
  position of the tree by iterating the \AF{right} function until it yields
  \AI{nothing}.

  \InsertCode{Proposal/Tree/Base.tex}{BUIterate}
  \colored

  Pattern matching on the result of \AF{right}\AS{}\AB{z} does not reveal any
  structural relation between the input \AB{z} and \AB{z₁}. Thus \Agda~'s
  termination checker correctly classifies the function as non-terminating. It
  does not know in which sense the recursive call is made on a smaller argument.

\subsection{Preparing the stage}
\label{subsec:preparing}

  In order to be able to define \AF{rightmost}, we should find the structure
  that decreases with each call to the function \AF{right} so \AF{rightmost} can
  be defined by structural recursion over it.

  Any position in the tree has a finite number of positions to the right of
  itself. A value of type \AD{Zipper} represents a position in the tree and for
  this reason each time we apply the function \AF{right} to some input the
  number of positions to the right decreases.

  Using \emph{well founded} recursion, as explained in \cref{sec:termination},
  we can define a relation \AD{\_<\_} over elements of \AD{Zipper} that exposes
  the decreasing structure of moving to the right.

  Additionally, by proving \textit{well foundedness} of the relation and the
  property that whenever the evaluation of \AF{right} \AB{z} yields a
  \AI{just}\AS{}\AB{z₁} then \mbox{\AB{z₁}\AS{}\AD{<}\AS{}\AB{z}}, we will be
  able to define \AF{rightmost} by structural recursion on the accessibility
  predicate of \AD{\_<\_}.

  \InsertCode{Proposal/Tree/Base.tex}{Skeleton}

  The purpose of the following subsections is to show how we can fill
  the open holes and the definition of \AD{\_<\_}.

  \colored

\subsection{Defining the relation}

  The relation we need shall consider positions on the left subtree of a
  \AI{Node} bigger than the \AI{Node} itself which at the same time is bigger
  than any position in its right subtree.

  \todo{a picture here?}

  Following Huet's idea, we regard the \AD{Stack} type as a path going
  \textit{backwards} from the position of the subtree up to the root. The
  relation has to be inductively defined on the \AD{Stack} part of the
  \AD{Zipper}.  Removing a constructor from the \AD{Stack} means moving up a
  position on the tree.

  For any two arbitrary positions on the tree, it is unknown a priori what is
  the order of removing constructors from the stack, that has to be followed to
  reach one of the base cases.
  Because of this, the relation has to be able to handle all possible situations
  which effectively will lead to a relation that allows us to prove that any two
  elements are related in both directions. Needless to say that such relation
  is just useless for our mission: a change of representation is needed.

  As an alternative, we can consider the \AD{Stack} as the \textit{forward} path
  from the root to the position where the subtree is located. A \emph{plug} operator
  that reconstruct the tree from the root can also be defined.

  \InsertCode{Proposal/Tree/Base.tex}{TDPlug}

  The new representation for positions is better suited for defining the
  relation where positions to the right are considered smaller that positions to
  the left. However, for our purpose of traversing the tree tail recursively,
  the \textit{backward} representation is a more natural fit.

  For this reason it is convenient to keep both representations and have a means
  of converting from one to the other. The conversion amounts to reverse the
  \AD{Stack}. To be sure that both representations are equivalent we can prove
  that plugging in one should yield the same tree as converting and plugging in
  the other.

  \InsertCode{Proposal/Tree/Base.tex}{Convert}

  We are ready to define the relation between elements of type \AD{Zipper}. The
  main idea of the relation is to look in the \AD{Stack} part of the \AD{Zipper}
  for the point where both \AD{Stack} diverge.

  Once this happens, the \AD{Stack} that has a \AI{Left} constructor on top
  indicates that its position located in the left subtree of the \AI{Node} and
  therefore should be always considered smaller than the \AI{Node} itself and
  that any position that is in the right subtree.

  When the topmost constructor of the \AD{Stack} is \AI{Right} this means that
  the location is in the right subtree. This position is smaller than the
  \AI{Node} itself and any other position on the left subtree.

  The relation we defined is formalized in \Agda~as follows.

  \InsertCode{Proposal/Tree/Base.tex}{TDRel}

  Two values of type \AD{Zipper} related by \AD{\_<\_} should represent
  positions in the same tree. By including the information of how the subtrees
  are reconstructed from the \AD{Tree} and \AD{Stack} on the other side of the
  relation this invariant is enforced in the type level.
  We can indeed prove that any two related elements when \emph{plugged} yield
  the same tree.

  \InsertCode{Proposal/Tree/Base.tex}{Related}

\subsection{Proving \textit{well foundedness}}

  The relation itself would be useless if we cannot prove that it is \emph{well
  founded}. As it was explained in \cref{subsec:wf}, the \emph{well foundedness}
  property for a relation requires us to exploit the recursive structure either
  of the input, in the base cases, or of the proof , in the inductive cases. If
  we are not able to show \Agda's termination checker that the argument is
  --evidently-- structurally smaller then we would not be able to use recursion
  to prove \emph{well foundedness}.

  The naive approach to the proof fails because in general pattern matching on
  the \AD{\_<\_} proof does not reveal any information about the structure of
  the tree for which both elements are positions of.

  In the base cases the structure we need to perform recursion is exactly the
  subtrees of the original tree, however this is not explicit in the proof.

  This realisation motivates us to define a new relation over \AD{Zipper} that
  makes the tree explicit. Even though we proved that related \AD{Zipper} values
  are positions of the same tree we include the proofs that both trees
  reconstruct to the same tree in the relation so during the proof we can refine
  the structure of the tree by pattern matching. This is the crucial step that
  allows the proof of \emph{well foundedness} to succeed.

  \InsertCode{Proposal/Tree/Base.tex}{TDRelIx}

  Because the new relation is indexed by a \AD{Tree} the definition of what
  means for this relation to be well founded has to change accordingly. The
  relation is well founded if for any \AD{Tree} any position of it, \AD{Zipper}
  is accessible.

  \InsertCode{Proposal/Tree/Base.tex}{WF}

  The full proof is omitted but can be found in the accompanying code. It works
  by induction on the \AD{\_<\_} structure as before, but it uses the equality
  proofs to discover the smaller structure on which perform recursion.


\todo{include the full proof?}

\subsection{Navigating through the tree}

  Finally we have developed the necessary machinery to fill the holes of the
  program we proposed in \cref{subsec:preparing}. The definition of \AF{rightmost}
  is more complex than we originally devised due to the change of representation
  that we use. Moreover, the full proof that \AF{right} yields a smaller element
  involves a lot of auxiliary lemmas and a lot of rewriting regarding the
  properties of list concatenation and reversal.

  \InsertCode{Proposal/Tree/Base.tex}{Right-preserves}
  \vspace*{-0.5cm}
  \InsertCode{Proposal/Tree/Base.tex}{to-right}
  \vspace*{-0.5cm}
  \InsertCode{Proposal/Tree/Base.tex}{Rightmost}

\subsection{From traverse to fold}\label{subsec:traverse-to-fold}

  Once we have shown how it is possible to prove in \Agda~ that the traversal of
  a tree from left to right in a tail recursive fashion terminates we are ready
  to extend the work to show that the tail recursive counterpart of a fold also
  terminates.

  In this subsection we build the basis for the work on the thesis that will us
  allow to prove the termination of a tail recursive fold. As a more interesting
  example we will use the type of binary trees with natural numbers in the
  leaves which resemble arithmetic expressions.

  \InsertCode{Proposal/Tree/Fold.tex}{Tree}

  The fold requires that the stack records not only the structure of the tree
  that is left to consume but also the intermediate results that have been
  produced but not yet consumed. For this reason the \AD{Stack} now holds
  subtrees that are to the right while the computed values have to substitute
  the left subtrees.

  \InsertCode{Proposal/Tree/Fold.tex}{Stack}

  In the case of the trees we are using we can define an analogous
  \emph{plugging} operator for both the \textit{backwards} and \textit{forwards}
  view of the \AD{Stack}. Because the \AD{Stack} does not represent a path on
  the original tree but is just a partial image on how the evaluation proceed we
  embed the intermediate results as leaves to be able to output a full tree.

  \InsertCode{Proposal/Tree/Fold.tex}{Plug}

  As opposed to McBride's example as explained in \cref{subsec:problem} we
  will not consider the tail recursive version of a fold as a pair of functions,
  \AD{load} and \AF{unload}. Instead we will define a function that performs
  only one step of the computation at a time.

  \InsertCode{Proposal/Tree/Fold.tex}{load-unload}

  If we define a suitable relation over \AD{Zipper} we should be able to define
  fold by iterating \AF{load/unload} until it yields a natural number.

  \InsertCode{Proposal/Tree/Fold.tex}{fold}

  The relation is not as straightforward to define as it was in the case of
  traversing the tree with a \AD{Zipper} because now the structure of the tree
  changes during the folding process.

  Two related elements by \AD{\_<\_} need not to reconstruct to the same tree
  but instead they reconstruct to a \textbf{partial image} of the original tree
  where some full subtrees have been replaced by the values they denote.
