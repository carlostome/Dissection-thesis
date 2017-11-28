%include proposal.fmt
%include polycode.fmt

\section{Termination}

\Agda~is a language of total functions. General recursive functions are not
allowed as they would render the logic inconsistent. In order to ensure
that any defined function terminates, \Agda~uses a termination checker, foetus
\cite{Abel98foetus}, that syntactically checks whether the recursive calls of a
function are performed in \textbf{structurally} smaller arguments.

Many functions that we would like to define do not conform to the pattern of
recursing over some argument that is evidently --\Agda~has factual evidence--
structurally smaller. In the rest of the section we will explore several
available techniques that overcome this limitation: sized types, Bove-Capretta
predicate and well founded recursion.

As a running example we will use the quick sort function whose definition
\Agda's termination checker classifies as non-terminating\footnote{With
\nonterm{this color} \Agda~warns that the termination checker fails.}

  % remember to tweak the .tex file with \nonterm
  \InsertCode{Proposal/QuickSort.tex}{QS}

\subsection{Sized types}

Sized types \cite{abel2010miniagda} is a type system extension that allows to
track structural information on the type level. Terms can be annotated with a
\textit{size} index that represents an \textbf{upper bound} of the actual
\textit{size} of the term being annotated. Functions can then quantify over size
variables to relate the \textit{size} of their input arguments to the
\textit{size} of the result.

% Because sized types are embedded into the type system, they not only serve to
% assist the termination checker but also they allow the programmer to specify
% more precisely how the function affects the \textit{size} of its argument.

\todo{say something else about what is Size (maybe not)}

\medskip

\begin{example}
  We can define the type of \textit{sized} lists in \Agda~by adding a new index
  to the usual type of cons lists that tracks size information. Both the
  \AI{Nil} and \AI{Cons} constructors need now to explicitly state their
  \textit{size}.

  \InsertCode{Proposal/Sized/List.tex}{List}

  The filter function on lists does not add any new constructor to its input,
  thus we can declare it as a \textit{size} preserving function.

  \InsertCode{Proposal/Sized/List.tex}{Filter}

  The definition of quick sort is as follows.

  \InsertCode{Proposal/Sized/List.tex}{QS}

  Pattern matching on the different constructors refines the \textit{size}
  argument that combined with the knowledge that \AF{filter} does not increase
  the \textit{size} ensures that the recursive call after \AF{filter} will
  terminate.

  Quick sort is a \textit{size} preserving function but we mark the \textit{size} of the
  output type to be \AP{ω}. The concatenation function used in the definition of
  quick sort is typed as.

  \InsertCode{Proposal/Sized/List.tex}{append}

  Sized types in \Agda~are somewhat limited and currently it is not possible to
  express on the type that the output \textit{size} should be \AB{i} \AP{+}
  \AB{j}. The closest approximation is to use the type \AP{ω} which means that
  we do not now anything about the size of the output.
\end{example}

\todo{say why sized types do not fit our purpose}

\subsection{Bove-Capretta predicate}

The call graph of a given recursive function $f$ of type \AD{A} to \AD{B}
(\AD{A}\AD{B} : |Set|) can be mechanically reified as a type indexed by
elements of the input type \AD{A}.

The domain predicate represents the information about the termination of the
function and enables us to define f by structural recursion on the predicate
rather than on its input.

\begin{example}[QuickSort]

  We can illustrate the use of \textit{domain} predicate with the quick sort
  function. Intuitively the domain predicate  states the termination conditions 
  of the function. 

  \InsertCode{Proposal/Bove-Capretta/QuickSort.tex}{DP}

  In the base case, the empty list, quick sort terminates. The inductive case
  on (x::xs) terminates if quick sort also terminates after filtering out
  both greater and smaller-or-equal than x elements from xs.

  It is possible now to define quick sort over the structure of its domain
  predicate which gets smaller in every recursive call.

  \InsertCode{Proposal/Bove-Capretta/QuickSort.tex}{BC}

  Because quick sort is a total function we can prove that the domain predicate
  holds for any list which means we can use this quicksor.

\end{example}

\subsection{Well founded recursion}

The essential idea of \emph{well founded} recursion is to define a relation over terms
of type \AD{A}, and show that starting from any value of \AD{A} it is possible to
reach the smallest element in the relation only using a finite number of steps.

Formally, given a binary relation $<$ over \AD{A}, | _<_ : ad( A ) -> ad(A) ->
Set |, an element $x$ of \AD{A} is accessible if there is no infinite descending
chain of the form $ x > x_1 > x_2 > x_3 \dots $. A more constructive
characterization of the accessibility predicate due to Nordstr{\"o}m
\cite{nordstrom1988terminating} is the following type in \Agda.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{Acc}

An element of \AD{A} is accessible if every element smaller than \AD{A} by |<|
is also accessible. The relation |<| is then \emph{well founded} when every
element of \AD{A} is accessible.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{WF}

The eliminator associated to this type serves us to define recursive functions
over a \emph{well founded} type.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{Elim}

\begin{example}
  QuickSort example

  \InsertCode{Proposal/WellFounded/List.tex}{QS}
  \InsertCode{Proposal/WellFounded/List.tex}{lemmas}

\end{example}

In order to be able to use the eliminator we must first prove that the relation
is well founded. The proof amounts to show \Agda~ that in there is some argument
that structurally decreases. It can either be the element of the relation or the
proof itself.

\begin{example}

  Let us consider the natural numbers and two equivalent definitions of the |<|
  (strict less than) relation.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Rel}

  In the first definition, constructors are peeled off from the first argument
  until there is a difference of one which constitutes the base case. On the
  contrary, in the second defintion peels constructors from the left argument
  until it reaches \AN{0}.

  It should be clear that both definitions are equivalent. However, the first is
  more suitable to prove well foundedness due to the explicit structural relation
  between both arguments.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Proof-1}

  Pattern matching on the proof allows us to refine both arguments. The
  recursive call to the well foundednees proof in the \AI{Base} case is allowed
  because \AB{y} is structurally smaller than \AI{succ} \AB{y}. In the step case
  we can recurse using \AF{aux} because the proof gets smaller.

  Things are not that easy with the second definition. As an attempt we might
  try the following.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Incomplete}

  The \AI{Base} case requires us to provide a proof of the well foundedness of
  \AN{0}.  However, we cannot use the well founded function itself because it is
  not clear how \AI{zero} is structurally smaller with respect to \AI{succ} \AB{y}.
  The hole in the \AI{Step} case has type which doesn't allow us either to use a
  recursive call on aux.

  Because there is not a clear relation between the structure of both arguments
  in the proof we cannot use recursive calls and we are stuck.

  In order to solve the problem, we need to introduce an auxiliary lemma that
  relates the structure of both inputs in such a way that pattern matching
  on it refines the arguments clearing the path to recursion again.

  The needed lemma and the proof are as follows.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Lemma}
  \vspace*{-0.75cm} % remove space between blocks
  \InsertCode{Proposal/WellFounded/Nat.tex}{Proof-2}
\end{example}

\todo{compare the three here?}




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

