%include polycode.fmt
%include thesis.fmt

%{
%format Tree  = "\AD{Tree}"
%format Tip   = "\AI{Tip}"
%format Node  = "\AI{Node}"
%format eval  = "\AF{eval}"
%format +     = "\AF{+}"
%format pretty   = "\AF{pretty}"
%format TreeAlg  = "\AD{TreeAlg}"
%format A        = "\AB{A}"
%format NodeA    = "\AB{NodeA}"
%format TipA     = "\AB{TipA}"
%format treeCata = "\AF{treeCata}"

%format UZipper = "\AD{UZipper}"
%format Stack = "\AD{Stack}"
%format Top   = "\AD{Top}"
%format Left  = "\AD{Left}"
%format Right = "\AD{Right}"
%format load  = "\AF{load}"
%format unload  = "\AF{unload}"
%format foldr = "\AF{foldr}"
%format foldl = "\AF{foldl}"

%format plugD   = "\AF{plug\ensuremath{\!\!\Downarrow}}"
%format plugZD  = "\AF{plugZ\ensuremath{\!\!\Downarrow}}"
%format ZipperD = "\AD{Zipper\ensuremath{\!\!\Downarrow}}"
%format forgetD = "\AF{forget\ensuremath{\!\!\Downarrow}}"

%format step = "\AF{step}"

%format plugU = "\AF{plug\ensuremath{\!\!\Uparrow}}"
%format plusOp = "\AF{\_+\_}"


\section{Verified tail-recursive fold for binary trees}\label{sec:tree}

  In this chapter, we present the transformation of a catamorphism for binary
  trees with natural numbers in the leaves onto a tail-recursive function.
  Moreover, we show how to prove that the resulting function terminates and that
  it is correct (for every possible input it computes the same result as the
  original fold).

  In order to do so, in \cref{subsec:bintree} we introduce the type of binary
  trees along with several examples of evaluation functions and how their common
  structure can be abstracted into a catamorphism. Then, in \cref{subsec:zipper},
  we explain the concept of a Zipper with its many type indexed variants and in
  \cref{subsec:onestep}.

  % In order to do, we first introduce the type of binary trees. In \subi We
  % provide both a proof of the termination of the transformation by defining a
  % suitable well-founded relation and also prove that the transformation is
  % correct.


  % The purpose of this thesis is to formalize the notion of dissection and its
  % usage to transform a fold into a tail-recursive function.

  % The first step is to prove that it is possible to write a function that
  % computes the fold of a non-linear (tree like) structure by tail recursion over
  % a explicit stack and that this function terminates.

  % This section is devoted to show that by using \emph{well founded} recursion we
  % can solve the problem for a specific datatype, the binary tree. simplified
  % version of the problem; that of traversing a tree from left to right. This
  % simplification from folding to traversing a tree will not be an impediment to
  % later generalize our results. A traversal can be conceptually thought as a
  % fold that does nothing.

  % The recursive structure of a inductive type is naturally defined in a top to
  % bottom manner. However, the traversing function has to exploit the left to
  % right inductive structure that is implicit in any tree-like type. For this
  % reason we cannot directly write the function that performs the traversal in
  % \Agda. The termination checker warns that it does not terminate because the
  % argument is not --manifestly-- structurally smaller.

  % In \cref{sec:termination} we reviewed several well known techniques that can
  % be used to assist \Agda's termination checker. \emph{Well founded} recursion
  % is the only one that allows us to make evident the left to right inductive
  % structure and provides us with a means for exploiting it.

\subsection{Binary trees}\label{subsec:bintree}
% Binary tree type
% Evaluation
% Abstraction with algebra
% Catamorphism

  The type of binary trees with natural numbers on the leaves is represented in
  \Agda using the following inductive type.

\begin{code}
  data Tree : Set where
    Tip   :  Nat   -> Tree
    Node  :  Tree  -> Tree -> Tree
\end{code}

  As examples of binary trees for example we can have:

  \todo{photo example}

  We can use binary trees to represent the syntax of arithmetic expressions. A
  value of type |Tree| is an expression where the |Node| constructor stands for
  addition and the natural numbers stand for themselves. Under this view, we can
  interpret (or evaluate) an expression into a natural number using a function
  |eval|.

%{
%format n     = "\AB{n}"
%format t1    = "\AB{\ensuremath{t_1}}"
%format t2    = "\AB{\ensuremath{t_2}}"
\begin{code}
  eval : Tree -> Nat
  eval (Tip n)       = n
  eval (Node t1 t2)  = eval t1 + eval t2
\end{code}
%}

  The function |eval| is defined compositionally (in the style of denotational
  semantics) where the value of a |Node| is computed by composing the values for
  the left and right subtree. Analogously, we can have another interpetation
  function that pretty prints a binary tree. This is a function of type |Tree ->
  String|.

%{
%format n     = "\AB{n}"
%format t1    = "\AB{\ensuremath{t_1}}"
%format t2    = "\AB{\ensuremath{t_2}}"
\begin{code}
  pretty : Tree -> String
  pretty (Tip n)       = show n
  pretty (Node t1 t2)  = pretty t1 ++ " + " ++ pretty t2
\end{code}
%}

  Both interpretations functions share some underlying structure. In the case of
  |eval|, when evaluating the constructor |Node| we combine the results of both
  subtrees using the addition operator |+| while when pretty printing we combine
  them by concatenating the resulting |String|s.

  Abstracting the concrete functions used in each case into an algebra.

\begin{code}
  record TreeAlg : Set1 where
    field
      A      : Set
      TipA   : Nat -> A
      NodeA  : A -> A -> A
\end{code}

\todo{A has to be in TreeAlg or it should be made parametric over it?}

  We can define a general catamorphism that folds a tree into a value of the
  type specified by the algebra.

%{
%format n     = "\AB{n}"
%format t1    = "\AB{\ensuremath{t_1}}"
%format t2    = "\AB{\ensuremath{t_2}}"
\begin{code}
  treeCata : (tAlg : TreeAlg) → Tree → A tAlg
  treeCata tAlg (Tip n)       = TipA  tAlg n
  treeCata tAlg (Node t1 t2)  = NodeA tAlg (treeCata tAlg t1) (treeCata tAlg t2)
\end{code}
%}

  Using the catamorphism, the |eval| function can be re-implemented as follows.

%{
%format tAlg = "\AB{tAlg}"
\begin{code}
  eval : Tree -> Nat
  eval = treeCata tAlg
    where
      tAlg : TreeAlg
      tAlg = record { A = Nat  ;  TipA = id  ;  NodeA = \_+\_ }
\end{code}
%}


\subsection{Zipper}\label{subsec:zipper}

  Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any leaf of a
  binary tree can be represented as a pair of the natural number it holds and
  the path from the root of the tree to the position it occupies.

\begin{code}
  UZipper : Set
  UZipper = Nat * Stack
\end{code}

  At each |Node| constructor, the path has to record whether the leaf occurs in
  the left or the right subtree. Moreover, from a value of \emph{Zipper} we
  should be able to reconstruct the original tree thus each time the path choses
  between left or right it has to keep track of the remaining subtree.

\begin{code}
  Stack : Set
  Stack = List (Tree U+ Tree)
\end{code}

  In \cref{fig:zipperexample}, there are two examples of \emph{Zipper} where the
  leaf in focus is marked with a box $\Box$. The \emph{Zipper} shown on the
  bottom is a tuple with the path to the leaf and the natural number. In the
  path, a left arrow {\color{red}$\leftarrow$} (correspondingly a right arrow
  {\color{green}$\rightarrow$}) represents that the rest of the path points to a
  leaf in the left (right) subtree of the |Node|.

\begin{figure}[h]
\begin{center}
  \includegraphics[scale=0.06]{images/zipperexample}
  \caption{Example of \emph{Zipper}}
  \label{fig:zipperexample}
\end{center}
\end{figure}

  If we were able to freeze a traversal from left to right over a binary tree, a
  value of type \emph{Zipper} would represent a concrete state of this
  procedure. At each leaf, everything that has already been traversed appears to
  the left of the |Stack| while the parts of the tree that still have to be
  processed show up on the right.

\begin{figure}[h]
\begin{center}
  \includegraphics[scale=0.04]{images/zippertraversal}
  \caption{Example of freezing a traversal}
  \label{fig:zippertraversal}
\end{center}
\end{figure}

  In order to represent the state of folding a binary tree from left to right,
  we can enrich the type of the |Stack| save not only the left subtrees (in case
  the path points to the right {\color{green}$\rightarrow$}) but also the value
  it evaluates (using the catamorphism) to and a proof of this equality.

  The rest of the constructions we are going to show assume there is an ambient
  tree algebra and that it is constant across all definitions and proofs. To
  achieve this in \Agda, we create a new module parametrized by a |TreeAlg|.

\begin{code}
  module _ (tAlg : TreeAlg) where

    open TreeAlg tAlg
\end{code}

  By |open|ing |tAlg| we bring into scope the type |A| and the fields |TipA| and
  |NodeA| without need to make any further reference to |tAlg|. The type of
  |Stack| is now defined as follows.

%{
%format a  = "\AB{a}"
%format t  = "\AB{t}"
%format eq = "\AB{eq}"

\begin{code}
  Stack : Set
  Stack = List (Tree U+ Sigma A lambda a  -> Sigma Tree lambda t
                                          -> treeCata tAlg t == a)

  pattern Left   t       = inj1 t
  pattern Right  a t eq  = inj2 (a , t , eq)
\end{code}

  The only piece of information required to compute the catamorphism of a |Tree|
  are the |a| values that come from evaluating the subtrees that appear to the
  left of the position under focus. However, as we will show later in
  \todo{ref}, it is neccesary for proving termination to keep around the |Tree|
  where the value came from. We say that |t| and the equality proof in
  |Stack| are computationally irrelevant. However, in \Agda~we cannot express
  such fact\footnote{In other systems like Coq the Tree would live in Prop}.
%}

  Given a |Stack| and a |Tree| (we can always embed a |Nat| into a |Tree| using
  |Tip|), the original |Tree| can be reconstructed by recursing over the
  |Stack|. At each step, it is known to which subtree the position belongs.

%{
%format t  = "\AB{t}"
%format t1 = "\AB{t\ensuremath{_1}}"
%format s  = "\AB{s}"
\begin{code}
    plugD : Tree → Stack → Tree
    plugD t []                  = t
    plugD t (Left t1 :: s)       = Node (plugD t s) t1
    plugD t (Right _ t1 _ :: s)  = Node t1 (plugD t s)
\end{code}

  Until now, we have only considered that the |Stack| represents the path from
  the root of the tree way down to the focused leaf. We can instead reverse the
  |Stack| part of the \emph{Zipper} so the path travels bottom-up from the leaf
  up to the root of the tree.

\begin{figure}[h]
\begin{center}
  \includegraphics[scale=0.05,angle=270]{images/zipperbuvstd}
  \caption{Bottom-Up versus Top-Down \emph{Zipper}}
  \label{fig:zipperbuvstd}
\end{center}
\end{figure}

  Under this view, we can reconstruct the original |Tree| from the
  |Stack|.

\begin{code}
  plugU : Tree -> Stack -> Tree
  plugU t (Left   t1 :: s)      = plugU (Node t t1) s
  plugU t (Right  _ t1 _ :: s)  = plugU (Node t1 t) s
  plugU t []                   = t
\end{code}
%}

  The only difference between both interpretations of the \emph{Zipper} is that
  to translate from one to the other we just need to reverse the |Stack|. We can
  show that indeed the original |Tree| is preserved by the conversion.

%{
%format plugU-to-plugD = plugU "\AF{-to-}" plugD
%format plugD-to-plugU = plugD "\AF{-to-}" plugU
%format reverse = "\AF{reverse}"
%format t = "\AB{t}"
%format s = "\AB{s}"
%format z = "\AB{z}"

\begin{code}
    plugU-to-plugD : forall t s -> plugU t s == plugD t (reverse s)
    plugU-to-plugD  t  s = cdots

    plugD-to-plugU : forall t s -> plugD t s == plugU t (reverse s)
    plugD-to-plugU t  s = cdots
\end{code}

\subsection{One-step of a fold}\label{subsec:onestep}

  The \emph{Zipper} type represents a snapshot of the internal state of a
  catamorphism over a binary tree. From one value of \emph{Zipper} we can write
  a pair of functions, |load| and |unload| that combined together perform one
  step of the fold.

\begin{code}
    load : Tree -> Stack -> UZipper U+ A
    load (Tip x) s       = inj1 (x , s)
    load (Node t₁ t₂) s  = load t₁ (Left t₂ ∷ s)

    unload : (t : Tree) → (a : A) → (eq : treeCata tAlg t) ≡ a -> Stack -> UZipper U+ A
    unload t a eq []                     = inj2 a
    unload t a eq (Left t′ ∷ s)          = load t′ (Right a t eq :: s)
    unload t a eq (Right a′ t′ eq′ ∷ s)  = unload  (Node t′ t) (NodeA a′ a) (cong₂ NodeA eq′ eq) s
\end{code}

  The function |unload| traverses the |Stack| combining all the results of
  evaluating the subtrees that were on the left of the position until either
  reaches a |Node| that has an unevaluated subtree on the right (|Left|
  constructor) or the |Stack| is empty and the |Tree| has been fully evaluated.
  When the former case occurs the |load| function is in charge of traversing the
  subtree on the right to find the leftmost leaf.

  \todo{maybe talk about irrelevance of t and eq?}

  A folding step just consists of calling |unload| passing appropiate arguments.

\begin{code}
    step : UZipper -> UZipper U+ A
    step (n , s) = unload (Tip n) (TipA n) refl s
\end{code}

  More graphically, the proccess of folding the tree one step is depicted in in
  \cref{fig:onestep},

\begin{figure}[h]
\begin{center}
  \includegraphics[scale=0.05,angle=180]{images/onestep}
  \caption{One step of fold}
  \label{fig:onestep}
\end{center}
\end{figure}
%}

\subsection{Folding a |Tree|}

  From the machinery we have developed so far one would be inclined to think
  that in order to fold a |Tree| it will suffice to find a fixed point of the
  function |step|.

\begin{code}
  foldTree : Tree -> Nat
  foldTree t with load t []
  ... | inj2 n = n
  ... | inj1 z = rec z
    where
      rec : UZipper -> Nat
      rec z with step z
      ... | inj1 z'  = rec z'
      ... | inj2 n   = n
\end{code}

  However, it does not work. \Agda's termination checker is right when it warns
  that the |z'| passed as an argument to the recursive call on |rec| is not
  structurally smaller than |z| and therefore the fixed point of |step| might
  not exists\footnote{|rec| loops forever}.

  From an outer perspective, it is fair to assert that for any possible input of
  type |UZipper|, the function |rec| has a fixed point. A value of |UZipper|
  focus on the position of a concrete leaf in a value of type |Tree|, and the
  function |step| refocuses the to the next leaf on the right. Because there are
  finitely many leaves on a |Tree|, the function |rec| must always terminate.

  In order to solve this problem, in the next subsections we will develop the
  notion of indexed \emph{Zipper} and show how it allows us to define an order
  relation between positions (\emph{Zipper}s) of the same |Tree|. This will be
  the key to define |rec| by structural recursion.

\subsection{Indexed \emph{Zipper}}\label{subsec:ixzipper}

  The current type of \emph{Zipper}, |UZipper| does not encode too much
  information. Given a value, it is not possible to statically know the |Tree|
  from which it represents a position. If we are to compare a pair of |UZipper|
  we need them to represent positions on the same |Tree| otherwise it does not
  make sense.

  We can address this shortcoming in the current representation by creating a
  new type wrapper over |UZipper| that is type indexed by the |Tree| where it is
  a position.

\begin{code}
  plugZD : UZipper -> Tree
  plugZD (t , s) = plugD (Tip t) s
\end{code}

\begin{code}
  data ZipperD (t : Tree) : Set where
    _,_ : (z : UZipper) -> plugZD z == t -> ZipperD t
\end{code}

  From an indexed \emph{Zipper} we can forget the extra information and recover
  the original |UZipper|.

\begin{code}
    forgetD : ∀ {t : Tree} -> (z : ZipperD t) -> UZipper
    forgetD (z , _) = z
\end{code}
%}
\subsection{\emph{Well founded} recursion}

\subsection{Catamorphism}
\subsection{Correctness}
\subsection{Discussion}

%   Any tree-like datatype shares a common branching structure with the type of
%   skeleton binary trees. We will use this type as the basis of our work.

%   \InsertCode{Proposal/Tree/Base.tex}{Tree}

%   Following Huet's idea of a \emph{Zipper}\cite{Huet97thezipper}, any position
%   in the tree can be represented as a pair of a subtree and a stack that holds
%   all the trees, to the left and to the right, in the path to the root.

%   \InsertCode{Proposal/Tree/Base.tex}{Stack}

%   Given a value of type \AD{Zipper} it is possible to \emph{plug} the subtree
%   and the stack together to reconstruct the original tree.

%   \InsertCode{Proposal/Tree/Base.tex}{BUPlug}

%   Navigating one position to the right in the tree can be easily defined in a
%   tail-recursive manner.

%   \InsertCode{Proposal/Tree/Base.tex}{BURight}

%   However, it is not possible to write a function that calculates the rightmost
%   position of the tree by iterating the \AF{right} function until it yields
%   \AI{nothing}.

%   \InsertCode{Proposal/Tree/Base.tex}{BUIterate}

%   Pattern matching on the result of \AF{right}\AS{}\AB{z} does not reveal any
%   structural relation between the input \AB{z} and \AB{z₁}. Thus \Agda~'s
%   termination checker rightfully classifies the function as non-terminating. It
%   does not know in which sense the recursive call is made on a smaller argument.

% \subsection{Setting the stage}
% \label{subsec:preparing}

%   To be able to define \AF{rightmost}, we should find the structure
%   that decreases with each call to the function \AF{right} so \AF{rightmost} can
%   be defined by \emph{well founded} recursion over it.

%   Any position in the tree has a finite number of positions to the right of
%   itself. A value of type \AD{Zipper} represents a position in the tree and for
%   this reason each time we apply the function \AF{right} to some input the
%   number of positions to the right decreases.

%   Using \emph{well founded} recursion, as explained in \cref{sec:termination},
%   we can define a relation \AD{\_<\_} over elements of \AD{Zipper} that exposes
%   the decreasing structure of moving to the right.

%   Additionally, by proving \textit{well foundedness} of the relation and the
%   property that whenever the evaluation of \AF{right} \AB{z} yields a
%   \AI{just}\AS{}\AB{z₁} then \mbox{\AB{z₁}\AS{}\AD{<}\AS{}\AB{z}}, we will be
%   able to define \AF{rightmost} by structural recursion on the accessibility
%   predicate of \AD{\_<\_}.

%   \InsertCode{Proposal/Tree/Base.tex}{Skeleton}

%   The purpose of the following subsections is to show how we can fill
%   the open holes and the definition of \AD{\_<\_}.

% \subsection{Defining the relation}

%   The relation we need shall consider positions on the left subtree of a
%   \AI{Node} bigger than the \AI{Node} itself which at the same time is bigger
%   than any position in its right subtree.

%   Following Huet's idea, we regard the \AD{Stack} type as a path going
%   \textit{backwards} from the position of the subtree up to the root. The
%   relation has to be inductively defined on the \AD{Stack} part of the
%   \AD{Zipper}.  Removing a constructor from the \AD{Stack} means moving up a
%   position on the tree.

%   For any two arbitrary positions on the tree, it is unknown a priori what is
%   the order of removing constructors from the stack, that has to be followed to
%   reach one of the base cases.
%   Because of this, the relation has to be able to handle all possible situations
%   which effectively will lead to a relation that allows us to prove that any two
%   elements are related in both directions. Needless to say that such relation
%   is just useless for our mission: a change of representation is needed.

%   As an alternative, we can consider the \AD{Stack} as the \textit{forward} path
%   from the root to the position where the subtree is located. A \emph{plug} operator
%   that reconstruct the tree from the root can also be defined.

%   \InsertCode{Proposal/Tree/Base.tex}{TDPlug}

%   The new representation for positions is better suited for defining the
%   relation where positions to the right are considered smaller than positions to
%   the left. However, for our purpose of traversing the tree tail recursively,
%   the \textit{backward} representation is a more natural fit.

%   For this reason it is convenient to keep both representations and have a means
%   of converting from one to the other. The conversion amounts to reverse the
%   \AD{Stack}. To be sure that both representations are equivalent we can prove
%   that plugging in one should yield the same tree as converting and plugging in
%   the other.

%   \InsertCode{Proposal/Tree/Base.tex}{Convert}

%   We are ready to define the relation between elements of type \AD{Zipper}. The
%   main idea of the relation is to look in the \AD{Stack} part of the \AD{Zipper}
%   for the point where both \AD{Stack}s diverge.

%   Once this happens, the \AD{Stack} that has a \AI{Left} constructor on top
%   indicates that its position is located in the left subtree of the \AI{Node} and
%   therefore should be always considered smaller than the \AI{Node} itself and
%   than any position that is in the right subtree.

%   When the topmost constructor of the \AD{Stack} is \AI{Right} this means that
%   the location is in the right subtree. This position is smaller than the
%   \AI{Node} itself and any other position on the left subtree.

%   The relation we defined is formalized in \Agda~as follows.

%   \InsertCode{Proposal/Tree/Base.tex}{TDRel}

%   Two values of type \AD{Zipper} related by \AD{\_<\_} should represent
%   positions in the same tree. By including the information of how the subtrees
%   are reconstructed from the \AD{Tree} and \AD{Stack} on the other side of the
%   relation this invariant is enforced in the type level.
%   We can indeed prove that any two related elements when \emph{plugged} yield
%   the same tree.

%   \InsertCode{Proposal/Tree/Base.tex}{Related}

% \subsection{Proving \textit{well foundedness}}

%   The relation itself would be useless if we cannot prove that it is \emph{well
%   founded}. As it was explained in \cref{subsec:wf}, the \emph{well foundedness}
%   property for a relation requires us to exploit the recursive structure of either
%   the input, in the base cases, or the proof, in the inductive cases. If
%   we are not able to show \Agda's termination checker that the argument is
%   --obviously-- structurally smaller then we would not be able to use recursion
%   to prove \emph{well foundedness}.

%   The naive approach to the proof fails because in general pattern matching on
%   the \AD{\_<\_} proof does not reveal any information about the structure of
%   the tree of which the two \AD{Zipper}s are a decomposition.

%   In the base cases, the structure we need to perform recursion is exactly the
%   subtrees of the original tree, however this is not explicit in the proof.

%   This realisation motivates us to define a new relation over \AD{Zipper} that
%   makes the tree explicit. Even though we proved that related \AD{Zipper} values
%   are positions of the same tree we include the proofs that both trees
%   reconstruct to the same tree in the relation so during the proof we can refine
%   the structure of the tree by pattern matching. This is the crucial step that
%   allows the proof of \emph{well foundedness} to succeed.

%   \InsertCode{Proposal/Tree/Base.tex}{TDRelIx}

%   Because the new relation is indexed by a \AD{Tree} the definition of what it
%   means for this relation to be \emph{well founded} has to change accordingly. The
%   relation is \emph{well founded} if for any \AD{Tree} any position of it,
%   \AD{Zipper}, is accessible.

%   \InsertCode{Proposal/Tree/Base.tex}{WF}

%   The full proof is omitted but can be found in the accompanying code. It works
%   by induction on the \AD{\_<\_} structure as before, but it uses the equality
%   proofs to discover the smaller structure on which perform recursion.

% \subsection{Navigating through the tree}

%   Finally we have developed the necessary machinery to fill the holes of the
%   program we proposed in \cref{subsec:preparing}. The definition of \AF{rightmost}
%   is more complex than we originally devised due to the change of representation
%   that we use. Moreover, the full proof that \AF{right} yields a smaller element
%   involves a lot of auxiliary lemmas and a lot of rewriting regarding the
%   properties of list concatenation and reversal.

%   \InsertCode{Proposal/Tree/Base.tex}{Right-preserves}
%   \vspace*{-0.5cm}
%   \InsertCode{Proposal/Tree/Base.tex}{to-right}
%   \vspace*{-0.5cm}
%   \InsertCode{Proposal/Tree/Base.tex}{Rightmost}

% \subsection{From traverse to fold}\label{subsec:traverse-to-fold}

%   Once we have shown how it is possible to prove in \Agda~ that the traversal of
%   a tree from left to right in a tail recursive fashion terminates we are ready
%   to extend the work to show that the tail recursive counterpart of a fold also
%   terminates.

%   In this subsection we build the basis for the work on the thesis that will
%   allow us to prove the termination of a tail recursive fold. As a more interesting
%   example we will use the type of binary trees with natural numbers in the
%   leaves which resemble arithmetic expressions.

%   \InsertCode{Proposal/Tree/Fold.tex}{Tree}

%   The fold requires that the stack records both the subtrees that still need to
%   be traversed and the intermediate results that have not yet been consumed.  For
%   this reason, the \AD{Stack} datatype now becomes:

%   \InsertCode{Proposal/Tree/Fold.tex}{Stack}

%   In the case of the trees we are using, we can define an analogous
%   \emph{plugging} operator for both the \textit{backwards} and \textit{forwards}
%   view of the \AD{Stack}. Because the \AD{Stack} does not represent a path on
%   the original tree but is just a partial image of how the evaluation proceeds, we
%   embed the intermediate results as leaves to be able to output a full tree.

%   \InsertCode{Proposal/Tree/Fold.tex}{Plug}

%   As opposed to McBride's example as explained in \cref{subsec:problem} we
%   will not consider the tail recursive version of a fold as a pair of functions,
%   \AF{load} and \AF{unload}. Instead we will define a function that performs
%   only one step of the computation at a time. This will be needed to prove that
%   each step of the computation decreases regarding the relation thus it is
%   possible to define the tail recursive fold using \emph{well founded} recursion.

%   \InsertCode{Proposal/Tree/Fold.tex}{load-unload}

%   If we define a suitable relation over \AD{Zipper} we should be able to define
%   fold by iterating \AF{load/unload} until it yields a natural number.

%   \InsertCode{Proposal/Tree/Fold.tex}{fold}

%   The relation is not as straightforward to define as it was in the case of
%   traversing the tree with a \AD{Zipper} because now the structure of the tree
%   changes during the folding process.

%   Two related elements by \AD{\_<\_} need not to reconstruct to the same tree
%   but instead they reconstruct to a \textbf{partial image} of the original tree
%   where some full subtrees have been replaced by the values they denote.
