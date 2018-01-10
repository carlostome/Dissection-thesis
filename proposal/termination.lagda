%include proposal.fmt
%include lhs2TeX.fmt

\section{Termination}
\label{sec:termination}

\Agda~is a language of total functions. General recursive functions are not
allowed as they would render the logic inconsistent. To ensure that any defined
function terminates, \Agda~uses a termination checker based on foetus
\cite{Abel98foetus}, that syntactically checks whether the recursive calls of a
function are performed in \textbf{structurally} smaller arguments.

Many functions that we would like to define do not conform to the pattern of
recursing over some argument that is evidently structurally smaller. In the rest
of the section, we will explore several available techniques that overcome this
limitation: \emph{sized types}, \emph{Bove-Capretta} predicates and \emph{well
founded} recursion.

%{
%format quickSort   = "\AF{quickSort}"
%format filter   = "\AF{filter}"
%format not      = "\AF{not}"
%format quickSortN  = "\nonterm{" quickSort "}"
%format A           = "\AD{A}"
%format x           = "\AB{x}"
%format xs          = "\AB{xs}"

As a running example, we will use the quicksort function:

  \begin{code}
    quickSortN : forall {A : Set} -> (A -> A -> Bool) -> List A -> List A
    quickSortN p [] = []
    quickSortN p (x :: xs) =  quickSortN p (filter (p x) xs)
                                ++ [ x ] ++
                              quickSortN p (filter (not . (p x)) xs)
  \end{code}

Because the recursive call is not made on a structurally smaller list, |xs|, we need
to do extra work to convince the termination checker.
%}

\subsection{Sized types} \label{subsec:sized}

Sized types \cite{abel2010miniagda} is a type system extension that allows to
track structural information on the type level. Terms can be annotated with a
type index that represents an \textbf{upper bound} of the actual \textit{size}
of the term being annotated. By \textit{size} of an inductive datatype we
understand the number of constructors used to build a value of the type.

Functions can quantify over size variables to relate the \textit{size} of their
input arguments to the \textit{size} of the result. The type system ensures
during type checking that the \textit{size} of the values conform with its type.

\medskip

\begin{example}
  We can define the type of \textit{sized} lists in \Agda~by adding a new index
  to the usual type of cons lists that tracks size information. Both the
  \AI{Nil} and \AI{Cons} constructors now explicitly state their
  \textit{size}.

  \InsertCode{Proposal/Sized/List.tex}{List}

  The filter function on lists does not add any new constructor to its input,
  thus we can declare it as a \textit{size} preserving function.

  \InsertCode{Proposal/Sized/List.tex}{Filter}

  The definition of quicksort is as follows.

  \InsertCode{Proposal/Sized/List.tex}{QS}

  Pattern matching on the different constructors refines the \textit{size}
  argument that combined with the knowledge that \AF{filter} does not increase
  the \textit{size} ensures that the recursive call after \AF{filter} will
  terminate.

  Quick sort is a \textit{size} preserving function but we mark the \textit{size} of the
  output type to be \AP{ω}. The concatenation function used in the definition of
  quicksort is typed as.

  \InsertCode{Proposal/Sized/List.tex}{append}

  Sized types in \Agda~are somewhat limited and currently it is not possible to
  express on the type that the output \textit{size} should be
  \mbox{\AB{i}\AS{}\AP{+}\AS{}\AB{j}}. The closest approximation is to use the
  type \AP{ω} which subsumes any other \textit{size} value. It means that we do
  not know anything about the \textit{size} of the output.

\end{example}

\subsection{Bove-Capretta predicate}\label{subsec:bove}

%{
%format f = "\AF{f}"
%format A = "\AD{A}"
%format B = "\AD{B}"

Even though a function may not recurse on structurally smaller arguments, we can
make it structurally recursive by making its call graph explicit. The call graph
of any function |f : A -> B| structurally decreases in each recursive call thus
it can be used to define |f| by recursion over it instead of its input.

The call graph of |f| is defined as a inductive type indexed by the values of
the input type |A|. This new type, called the domain predicate\footnote{A
predicate in \Agda~is anything of type |A -> Set|} of |f|, intuitively outlines
the conditions for which the function terminates.

In order to show that the function terminates for any input, it is necessary to
provide a proof that it is possible to construct the domain predicate for any
possible input. Therefore, the termination issue is decoupled from the definition
of the function but still has to be proved.

%}
\begin{example}

  The domain predicate for the quicksort function is an \Agda~predicate type
  over lists, |List A -> Set|. The base case, when the list is empty, quicksort
  terminates. In the inductive case, quicksort terminates if it terminates both
  on the list that results from filtering out smaller elements and greater
  elements.

  \InsertCode{Proposal/Bove-Capretta/QuickSort.tex}{DP}

  A terminating quicksort is defined over the structure of the domain predicate
  which at each recursive call is structurally smaller, thus accepted by the
  termination checker.

  \InsertCode{Proposal/Bove-Capretta/QuickSort.tex}{BC}

  However, we are left now with the requirement of showing that the domain
  predicate holds for any possible list. In order to show it, we will have to
  resort to the method of \emph{well founded} recursion that will be explained in the
  next section.
\end{example}

%{
%format f = "\AF{f}"
%format A = "\AD{A}"
%format B = "\AD{B}"
%format x = "\AB{x}"
%format x1 = "\AB{x_1}"
%format x2 = "\AB{x_2}"
%format x3 = "\AB{x_3}"
%format _<_ = "\AF{\_<\_}"
%format <   = "\AF{<}"

\subsection{Well founded recursion}
\label{subsec:wf}

The essential idea of \emph{well founded} recursion is to define a relation over
terms of type |A|, and show that starting from any term of type |A| any
decreasing chain is finite.

Formally, given a binary relation |<| over |A|, | _<_ : A -> A -> Set |, an
element |x : A| is accessible if there is no infinite descending chain of the
form | x > x1 > x2 > x3 cdots |. A more constructive characterization of the
accessibility predicate due to Nordstr{\"o}m \cite{nordstrom1988terminating} is
the following type in \Agda.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{Acc}

An element of |A| is accessible if every element smaller than |A| by |<|
is also accessible. The relation |<| is then \emph{well founded} when every
element of |A| is accessible.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{WF}

The eliminator associated to this type serves us to define recursive functions
over a \emph{well founded} relation.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{Elim}

\begin{example}
  For encoding the quicksort function using \emph{well founded} recursion, we
  have to define a suitable relation over lists that we can use to show that the
  result of applying |filter| yields a smaller element. We can either use the
  eliminator for \emph{well founded} recursion or define the function by
  explicit recursion over the accessibility predicate. For this matter the proof
  that the relation is \emph{well founded} is mandatory.

  \InsertCode{Proposal/WellFounded/List.tex}{relation}

  We use the relation less-than over natural numbers to create a new relation
  over lists by appealing to their length. We can lift the proof that less-than
  is \emph{well founded}.

  \InsertCode{Proposal/WellFounded/List.tex}{WF}

  A couple of lemmas that relate the length of the input list
  to \AF{filter} with the length of the output are also needed.

  \InsertCode{Proposal/WellFounded/List.tex}{lemma1}
  \vspace*{-0.5cm}
  \InsertCode{Proposal/WellFounded/List.tex}{lemma2}

  Finally, we can describe quicksort using an auxiliary function that explicitly
  uses the accessibility as the structure in the recursion.

  \InsertCode{Proposal/WellFounded/List.tex}{QS}

\end{example}

\medskip

A non structurally recursive function,  |f : A -> B|,  can be defined in
\Agda~by giving an smaller-than relation over the input type and performing
structural recursion on the accessibility predicate. For this to work, the
recursive calls should be made over elements that, even though they might not be
structurally smaller than the input, they are smaller by the relation.

Then, for any input value we have to provide a proof that the value is accesible
by the relation, which means all descending chains starting from such element
are finite. If the relation is \emph{well founded}, then every element of the
input type is accesible by the relation giving us a means of constructing
automatically the required proof.

For this reason, defining a function by \emph{well founded} recursion critically
relies on showing that the relation itself is \emph{well founded} which is by no
means an easy task that lastly forces us to show \Agda~that something
structurally decreases.

\medskip

%{
%format 0   = "\AN{0}"
%format aux = "\AF{aux}"
%format Base = "\AD{Base}"
%format Step = "\AD{Step}"
%format succ = "\AD{succ}"
%format zero = "\AD{zero}"
%format y = "\AB{y}"
%format x = "\AB{x}"
%format p = "\AB{p}"
%format <2 = "\AI{\ensuremath{<_{2}}}"

\begin{example}

  Let us consider the natural numbers and two equivalent definitions of the |<|
  (strict less than) relation.
  \InsertCode{Proposal/WellFounded/Nat.tex}{Rel}
  In the first definition, constructors are peeled off from the first argument
  until there is a difference of one which constitutes the base case. On the
  other hand, the second defintion peels constructors from the left argument
  until it reaches |zero|.

  It should be clear that both definitions are equivalent. However, the first is
  more suitable to prove well foundedness due to the explicit structural relation
  between both arguments.
  \InsertCode{Proposal/WellFounded/Nat.tex}{Proof-1}
  Pattern matching on the proof allows us to refine both arguments. The
  recursive call to the well foundednees proof in the |Base| case is allowed
  because |y| is structurally smaller than |succ y|. In the step case
  we can recurse using |aux| because the proof |p| is structurally smaller than
  |Step p|.

  Things are not that easy with the second definition. As an attempt we might
  try the following:
  \InsertCode{Proposal/WellFounded/Nat.tex}{Incomplete}
  The |Base| case requires us to provide a proof of the well foundedness of
  |zero|.  However, we cannot use the well founded proof itself because |zero|
  is not structurally smaller than |succ x|. For the |Step| case we need to
  prove that |succ y| is accesible. We can resort to |aux| and fill the two
  first arguments. However, providing a proof of |succ y <2 succ x| from |p : y
  <2 x| means passing |p| as an argument to the constructors |Step|, the same
  that needed to be peeled in order to be structurally smaller.

  Because there is not a clear relation between the structure of both arguments
  in the proof we cannot use recursive calls and we are stuck.

  In order to solve the problem, we need to introduce an auxiliary lemma that
  relates the structure of both inputs in such a way that pattern matching
  on it refines the arguments clearing the path for the proof of well
  foundedness.

  The required lemma and the proof are as follows:

  \InsertCode{Proposal/WellFounded/Nat.tex}{Lemma}
  \vspace*{-0.75cm} % remove space between blocks
  \InsertCode{Proposal/WellFounded/Nat.tex}{Proof-2}
\end{example}
%}

% to add size annotations to the constructors of
% a type. The size of a value represents an upper bound on the number of
% constructors used in its definition.

% Size annoation are attached to inductive types to track the number of
% constructors used in the definition of a value of the type.

% Moreover, functions can be also an
% constructors that a value of a

% \subsection{Bove-Capretta domain predicate}

% Following the Curry-Howard correspondence, if types are to be interpreted as
% propositions and terms inhabiting them as their proofs then termination of terms
% is customary to keep the logic consistent. A non terminating term such as
% |non-term = non-term| could stand as a proof for any proposition (respectively
% as an inhabitanat of any type) thus even a false proposition would have a proof
% backing its truth!


% Moreover, in the dependently typed setting where types can and may depend on terms,
% termination of terms also ensures decidability of the typechecking
% procedure.\arewesure{decidability really depends on termination?}

% Systems based on different flavours of dependent type theory such as Agda or Coq
% \referenceneeded{Agda Coq}


% The traditional approach to ensure termination in systems implementing type
% theory is to restrict the kind of programs that would pass the typechecker.

% By only allowing the user to write function that when performing a recursive
% call this must be made in a structural smaller argument.


% where structural smaller means that a
% constructor or more must be peleed of before performing the recursive call.

% As a first example the implementation of Euclides algorithm for computing the
% greatest common division is analyzed. We state its definition in the following
% snippet.

% In the rest of this section we explore various techniques to approach the
% termination problem in type theory.


% Sized types are a type-based termination checkerk

% \subsection{Bove-Capretta}

% \section{Step back}

