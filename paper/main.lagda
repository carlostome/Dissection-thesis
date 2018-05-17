
%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For double-blind review submission, w/ CCS and ACM Reference
%\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For single-blind review submission, w/ CCS and ACM Reference
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission, w/ required CCS and ACM Reference
%\documentclass[sigplan,10pt]{acmart}\settopmatter{}

% TODO notes
\usepackage[draft]{todonotes}

%% Agda stuff
\usepackage[conor]{agda}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AY}{\AgdaSymbol}
\newcommand{\AN}{\AgdaNumber}
\newcommand{\AS}{\AgdaSpace}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AO}{\AgdaOperator}
\newcommand{\AI}{\AgdaInductiveConstructor}
\newcommand{\AC}{\AgdaCoinductiveConstructor}
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AL}{\AgdaField}
\newcommand{\AR}{\AgdaArgument}
\newcommand{\AT}{\AgdaIndent}
\newcommand{\ARR}{\AgdaRecord}
\newcommand{\AP}{\AgdaPostulate}
\newcommand{\APT}{\AgdaPrimitiveType}


\newcommand{\nonterm}[1]{\hspace*{-0.1cm}\colorbox{orange!25}{#1}}
\newcommand{\hole}[1]{\colorbox{yellow!50}{\ensuremath{\bigbox_{#1}}}}
%% Conference information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmConference[PL'17]{ACM SIGPLAN Conference on Programming Languages}{January 01--03, 2017}{New York, NY, USA}
\acmYear{2017}
\acmISBN{} % \acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%\citestyle{acmauthoryear}  %% For author/year citations
%\citestyle{acmnumeric}     %% For numeric citations
%\setcitestyle{nosort}      %% With 'acmnumeric', to disable automatic
                            %% sorting of references within a single citation;
                            %% e.g., \cite{Smith99,Carpenter05,Baker12}
                            %% rendered as [14,5,2] rather than [2,5,14].
%\setcitesyle{nocompress}   %% With 'acmnumeric', to disable automatic
                            %% compression of sequential references within a
                            %% single citation;
                            %% e.g., \cite{Baker12,Baker14,Baker16}
                            %% rendered as [2,3,4] rather than [2-4].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Note: Authors migrating a paper from traditional SIGPLAN
%% proceedings format to PACMPL format must update the
%% '\documentclass' and topmatter commands above; see
%% 'acmart-pacmpl-template.tex'.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%include paper.fmt

% fontsize of code snippets
\renewcommand\hscodestyle{%
   \setlength\leftskip{0.25cm}%
   \footnotesize
}

\begin{document}

%% Title information
\title[Short Title]{Full Title}         %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
\titlenote{with title note}             %% \titlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'
\subtitle{Subtitle}                     %% \subtitle is optional
\subtitlenote{with subtitle note}       %% \subtitlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{First1 Last1}
\authornote{with author1 note}          %% \authornote is optional;
                                        %% can be repeated if necessary
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{Position1}
  \department{Department1}              %% \department is recommended
  \institution{Institution1}            %% \institution is required
  \streetaddress{Street1 Address1}
  \city{City1}
  \state{State1}
  \postcode{Post-Code1}
  \country{Country1}                    %% \country is recommended
}
\email{first1.last1@@inst1.edu}          %% \email is recommended

%% Author with two affiliations and emails.
\author{First2 Last2}
\authornote{with author2 note}          %% \authornote is optional;
                                        %% can be repeated if necessary
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{Position2a}
  \department{Department2a}             %% \department is recommended
  \institution{Institution2a}           %% \institution is required
  \streetaddress{Street2a Address2a}
  \city{City2a}
  \state{State2a}
  \postcode{Post-Code2a}
  \country{Country2a}                   %% \country is recommended
}
\email{first2.last2@@inst2a.com}         %% \email is recommended
\affiliation{
  \position{Position2b}
  \department{Department2b}             %% \department is recommended
  \institution{Institution2b}           %% \institution is required
  \streetaddress{Street3b Address2b}
  \city{City2b}
  \state{State2b}
  \postcode{Post-Code2b}
  \country{Country2b}                   %% \country is recommended
}
\email{first2.last2@@inst2b.org}         %% \email is recommended


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
The functional programming paradigm encourages a style of programming based on
  the use of higher-order functions over inductively defined datatypes. A fold is
  the prototypical example of such a function. However, its use for computation
  comes at a price.  Folds for branching datatypes, such as binary trees, are by
  definition not tail recursive functions.

McBride has proposed a method called
  \emph{dissection}\cite{McBride:2008:CLM:1328438.1328474}, to transform a fold
  into its tail-recursive counterpart. Nevertheless, it is not clear why the
  resulting function terminates, nor it is clear that the transformation
  preserves the fold's semantics. In this paper we fill the gap by providing a
  fully machine checked proof of the construction using the proof assistant
  Agda.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{keyword1, keyword2, keyword3}  %% \keywords are mandatory in final camera-ready submission


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle


%{
%format Expr  = "\AD{Expr}"
%format Acc  = "\AD{Acc}"
%format Val   = "\AI{Val}"
%format Add   = "\AI{Add}"
%format acc   = "\AI{acc}"
%format eval  = "\AF{eval}"
%format tail-rec-eval  = "\AF{tail\text{-}rec\text{-}eval}"
%format correct = "\AF{correct}"
%format +     = "\AF{+}"
%format Stack = "\AD{Stack}"
%format Top   = "\AI{Top}"
%format Left  = "\AI{Left}"
%format Right = "\AI{Right}"
%format load  = "\AF{load}"
%format Well-founded  = "\AF{Well\text{-}founded}"
%format unload = "\AF{unload}"
%format reverse = "\AF{reverse}"
%format rec    = "\AF{rec}"
%format plugup   = "\AF{plug\ensuremath{\Uparrow}}"
%format Zipper = "\AD{Zipper}"
%format Zipperup = "\AD{Zipper\ensuremath{\Uparrow}}"
%format plugdown   = "\AF{plug\ensuremath{\Downarrow}}"
%format Zipperdown = "\AD{Zipper\ensuremath{\Downarrow}}"
%format plugZup = "\AF{plugZ\ensuremath{\Uparrow}}"
%format plugZdown = "\AF{plugZ\ensuremath{\Downarrow}}"
%format ??    = "\hole{0}"
%format ??1    = "\hole{1}"
%format ??2    = "\hole{2}"
%format ??3    = "\hole{3}"
%format plugdown-to-plugup  = plugdown "\AF{\text{-}to\text{-}}"  plugup
%format plugup-to-plugdown  = plugup "\text{-}to\text{-}"  plugdown
%format plusOp = "\AF{\_+\_}"
%format ltOp = "\AD{\_<\_}"
%format <-Right = "\AI{<\text{-}Right}"
%format <-Left = "\AI{<\text{-}Left}"
%format <-Right-Left = "\AI{<\text{-}Right\text{-}Left}"
%format < = "\AD{<}"
%format dotted = "\AS{.}\hspace*{-0.1cm}"

% Bound variables
%format n     = "\AB{n}"
%format r     = "\AB{r}"
%format z     = "\AB{z}"
%format z'     = "\AB{z''}"
%format e     = "\AB{e}"
%format v     = "\AB{v}"
%format v'     = "\AB{v''}"
%format stk   = "\AB{stk}"
%format e1    = "\AB{\ensuremath{e_1}}"
%format e2    = "\AB{\ensuremath{e_2}}"
%format t    = "\AB{\ensuremath{t}}"
%format eq    = "\AB{\ensuremath{eq}}"
%format t1    = "\AB{\ensuremath{t_1}}"
%format t2    = "\AB{\ensuremath{t_2}}"
%format s1    = "\AB{\ensuremath{s_1}}"
%format s2    = "\AB{\ensuremath{s_2}}"
%format t1'    = "\AB{\ensuremath{t_1}''}"
%format t2'    = "\AB{\ensuremath{t_2}''}"

\section{Introduction}

The type of binary trees is one of the most simple, yet widespread used,
datastructures in functional programming.  Beyond its elegance and simplicity,
in its definition lies an embarasing truth: a fold over a binary tree is not a
tail recursive function. In order to understand the problem, let us introduce
the type of binary trees.

\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}

We can write an evaluation function that maps binary trees to natural numbers if
we were to interpret the constructor |Add| as addition.

\begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
\end{code}

The function |eval| is compositional. The value of a node |Add| is computed by
adding the values denoted by its subexpressions. And here lies the problem. The
operator |plusOp| needs both of its parameters to be evaluated before it can further
reduce. If the expression we want to compute over is very big this poses a
problem during runtime as the execution stack grows linearly with the size of
the input.

\todo[inline]{Maybe include something about Optimization through tco => get rid of
intermediate steps}

In order to solve the problem, we can make the execution stack explicit and
write a function that performs tail recursion over it. The idea is that we can
use a list to store both intemediate results and the subtress that still need to
be processed. We can define such a stack as follows:

\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

Two mutually recursive functions that operate over the stack and tree are load
and unload. The former traverses a tree finding the leftmost leaf while the
latter dispathes over the stack by accumulating a partial result while looking
for the next subtree.

%{
%format loadN   = "\nonterm{" load "}"
%format unloadN = "\nonterm{" unload "}"
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unloadN (v' + v) stk
    unload v   (Left r stk)    = loadN r (Right v stk)
\end{code}
%}

A tail recursive version of |eval| can is defined by calling load with the empty
stack.

\begin{code}
  tail-rec-eval : Expr → Nat
  tail-rec-eval e = load e Top
\end{code}

The reader might have noticed that the names of unload and load are higlighted
with \nonterm{orange}. This is because Agda's termination checker flags the pair of
functions as possibly non-terminating. Indeed, the recursive calls are not
always performed over syntactically smaller arguments. If we assumed that it
terminates we still do not know if it is correct in the sense that for every
input |tail-rec-eval| and |eval| agree on the output.

\begin{code}
  correct : forall (e : Expr) -> eval e == tail-rec-eval e
  correct = ??
\end{code}

The main contribution of this paper is to show that we can both prove
termination and correctness of the construction in Agda. Specifically we show
how we can encode an ordering relation over stacks, show that the relation is
well founded and use it to define a tail recursive fold by structural recursion.
We discuss what are the main challenges that we have to overcome to convinde
Agda's termination checker that indeed something `goes smaller`. Moreover, our
approach allows us to get correctness almost for free.

McBride's insight is that we can calculate the type of stacks from the generic
description of a datatype by using Leibniz rules for derivatives. In later
sections of the paper, we discuss how to generalize our results to regular tree
datatypes and by doing so we show that McBride's intuition that the construction
is correct was true.

\section{Basic idea}

The functions |load| and |unload| are marked as non terminating because they are
not defined by structural recursion over their arguments. In particular, the
stack passed as an argument to the recursive call of |load| in the definition of
|unload| is structurally equal in size as the input stack.

Intuitively, |load| and |unload| fold the tree by traversing it from its
leftmost leaf to its rightmost using the stack to store both partial results and
the remaining subtrees to fold them as neccesary. The problem arises because the
stack is simply typed and any information about how the subtrees kept in the
stack relate to each other and to the original tree is lost once a subtree is
inserted onto the stack.

However, it is clear that virtually every node (either leaf or not) from the
original tree is visited at most twice during the computation. First when the
function |load| decomposes it looking for its leftmost leaf and a second time
when |unload| is accumulating over the stack searching for another subtree to
continue. This process is depicted in figure 1.

\begin{figure}[h]
  \includegraphics[scale=0.25]{figure1}
\end{figure}

We can argue that because there are finitely many nodes on a tree, |load| and
|unload| neccesarily terminate. The question is now, How can we encode this
information in such a way that Agda understand that the fold terminates?

The idea is that |load| and |unload| should not fold  the full input tree in one
go, but instead they will perform one step of the computation at a time.
Morover, by defining them by structural recursion over their arguments now they
are classified as terminating by the termination checker.

\begin{code}
  load : Expr -> Stack -> Nat * Stack
  load (Val n)      stk = (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)

  unload : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload v   Top             = inj2 v
  unload v   (Right v' stk)  = unload (v' + v) stk
  unload v   (Left r stk)    = inj1 (load r (Right v stk))
\end{code}

For example, if we take the same tree in figure 1, after |load| finds the
initial leftmost leaf we can apply one step of the new |unload| that will end up
in the next leaf to the right.


\begin{figure}[h]
  \includegraphics[scale=0.25]{figure2}
\end{figure}

A tail recursive fold corrensponds to repeatedly applying the function |unload|
until we find a |inj2| whose value is the result of folding the tree.

%{
%format nrec   = "\nonterm{" rec "}"
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top)
    where
      nrec : (Nat * Stack) -> Nat
      rec (n , stk) with unload n stk
      ... | inj1 z' = nrec z'
      ... | inj2 r = r
\end{code}
%}

The function |tail-rec-eval| still does not pass the termination checker, The
variable |z'| is not structurally smaller than |(n , stk)|. However, now we can
refine it by using well founded recursion to make it structurally recursive by
performing the recursion over the accessibility predicate instead of the pair
|Nat * Stack|.

\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = rec (load e Top) ??1
    where
      rec : (z : Nat * Stack) -> Acc ltOp z -> Nat
      rec (n , stk) (acc rs) with unload n stk
      ... | inj1 z' = rec z' (rs ??2)
      ... | inj2 r = r
\end{code}

For the function above to work, we need to find a suitable definition for the
relation |ltOp| over pairs of |Nat * Stack|, prove that applying |unload|
results in an smaller element by the relation and finally show that the relation
is |Well-founded|, so the call to |rec| can be made in the first place. Before
any of that, we need to revisit Huet's notion of \emph{Zipper} and show how it
relates to what we are trying to achieve.

\subsection{Zippers up, Zippers down}

Huet introduced \emph{Zippers} to allow a tree datastructure to be efficiently
updated in a purely functional way. The idea is that any location on a tree,
either an internal node or a leaf, can be represented by a path to the root and
the subtree that hangs downwards.

The pair |Nat * Stack| used to compute the tail recursive fold is nothing more
that a restricted version of the \emph{Zipper} where the locations can only be
leaves of the tree.

\begin{code}
  Zipper : Set
  Zipper = Nat * Stack
\end{code}

From a |Zipper| we have to be able to reconstruct the original |Expr| which
will be neccesary later on for the proof that the relation is well founded. For
this matter, we have to enhance the type of stacks to store not only the partial
results but also the expressions that where consumed in order to produce them.

\begin{code}
  Stack : Set
  Stack = List (Expr U+  (Sigma Nat lambda n ->
                          Sigma Expr lambda e -> eval e == n))
  pattern Left t        = inj1 t
  pattern Right n t eq  = inj2 (n , t , eq)
\end{code}

The original expression for which a |Nat * Stack| represents a position can be
reconstructed by forgeting that some part has already been evaluated.

\begin{code}
  plugup : Expr -> Stack -> Expr
  plugup e []                      = e
  plugup e (Left t        :: stk)  = plugup (Add e t) stk
  plugup e (Right n t eq  :: stk)  = plugup (Add t e) stk

  plugZup : (Nat * Stack) -> Expr
  plugZup (n , stk) = plugup (Val n) stk
\end{code}

Our goal is to impose an ordering relation over elements of |Zipper| such that
for any input the |unload| function delivers a |Zipper| that is smaller by the
relation when it does not terminate with a value. Because the folding happens
from left to right, we want the relation to order the leaves of the tree
accordingly, so the leftmost leaf is the greatest element and the rightmost the
smallest. Using the example from before, we number the leaves as follows:

\begin{figure}[h]
  \includegraphics[scale=0.25, angle=90]{figure3}
\end{figure}

Using the |Stack| as a path from the leaf to the root of the tree is difficult
if not impossible to encode a smaller than relation that does not relate any two
elements. Such relation has to be defined by induction on the |Stack| part of the
|Zipper|. But for any two given stacks a priori we cannot know how many layers
we have to peel in order to reach a case where one of them is obviously smaller
that the other.

We can approach the problem by understanding the |Stack| not as a path from the
leaf up to the root but from the root down to the leaf. This change of
perspective is realised with a new plug function that does the opposite of
|plugup|.

\begin{code}
  plugdown : Expr -> Stack -> Expr
  plugdown e []                     = e
  plugdown e (Left t       :: stk)  = Add (plugdown e stk) t
  plugdown e (Right n _ _  :: stk)  = Add t (plugdown e stk)

  plugZdown : (Nat * Stack) -> Expr
  plugZdown (n , stk) = plugdown (Val n) stk
\end{code}

It is clear that both views of the |Zipper| are related. Indeed, to transport
from one to the other we only have to reverse the stack. We show the equvalence
with the following lemma\footnote{The other way around only requires to use
BLABLA of |reverse|}:

\begin{code}
  plugdown-to-plugup  : forall (e : Expr) (stk : Stack)
                      → plugdown e stk ==  plugup e (reverse stk)
\end{code}


Why do we need this equivalence? The bottom up view of a |Zipper| is suitable
for defining the tail recursive fold, alas to prove termination we have to use
use the top down view to describe the relation we need.

\subsection{A relation on Zipper}

The relation over elements of |Zipper| is defined by induction on the |Stack|.
If we start in the root of the tree, we can navigate downwards both stacks in
parallel removing their common prefix. Once we find an |Add| where they
disagree then whether the first |Zipper| is located in the left or right
subtree fully determines if its bigger or smaller than the other |Zipper|.
The following type accounts for this explanation:

\begin{code}
  data ltOp : Zipper -> Zipper -> Set where
    <-Right  : (t1 , s1) < (t2 , s2)
             ->  (t1 , Right l n eq :: s1) < (t2 , Right l n eq :: s2)
    <-Left   : (t1 , s1) < (t2 , s2)
             ->  (t1 , Left r :: s1)       < (t2 , Left r :: s2)
    <-Right-Left  :   (t1' == plugdown (Tip t2) s2)
                  ->  (t2' == plugdown (Tip t1) s1)
                  ->  (t1 , Right n t1' eq :: s1) < (t2 , Left t2' :: s2)
\end{code}

Having the relation defined, we turn our focus to prove that it is well founded.
This is an important step towards filling the holes that were left open in the
function |tail-rec-eval|.

A relation is well founded iff all the descending chains starting from an
arbitrary element are finite. In a theorem prover such as Agda, an alternative
definition of well foundedness is used which is based on an accesibility
predicate.

We can try to prove that the relation is well founded by using an auxiliary
function that allows us to pattern match on the smaller than proof. When doing
so, the inputs are refined to concrete constructors. Normally the proof either
makes use of recursion over the proof or over the input, but in the case of the
|<-Right-Left| constructor we do not have either option, because the smaller
element is not structurally related to the bigger and the proof does not have
any recursive structure to use.

\begin{code}
 <-WF : Well-founded ltOp
 <-WF x = acc (aux x)
    where
      aux : ∀ (x : Zipper)
          -> ∀ (y : Zipper) -> y < x -> Acc ltOp y
      aux dotted(t2 , Left t1' :: s2) dotted(t1 , Right n t2' eq :: s1) (<-Right-Left eq1 eq2) = {!!}
      aux ...
\end{code}

The proof fails because in |aux| both Zippers |x| and |y| might very well be
locations of leaves belonging to different trees as far we know. Thanks to the
use of dependent types, the property that a Zipper represents a position inside a
concrete tree can be made explicit at the type level.

\begin{code}
  data Zipperdown (e : Expr) : Set where
    \_,\_ : (z : Zipper) -> plugZdown z == e -> Zipperdown e
\end{code}

We write a relation that is enforced to only relate Zippers beloging to the same
|Expr| by using a common value of that type as an of |Zipperdown|

\begin{code}
  data IxltOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set where
    ...
\end{code}

The concrete details of the relation follow very much the one we gave before,
with the exception that every case has attached a new piece of information
specifying the concrete |Expr| obtained by plugging both Zippers.

The new version of the relation is suitable for proving well foundedness because
we can pattern match on the equality included in the |Zipperdown| type to show how 
the overall structure decreases. This allows us to use the recursion we need to
complete the proof.
In particular, the case we were not able to prove before, now can be proven by learning that
|(t2 , s2)| is a position on the left subtree while |(t1 , s1)| is on the
right subtree of a common |Add| node.

\begin{code}
  <-WF : forall e -> Well-founded (IxltOp e)
  <-WF x = acc (aux e x)
    where
      aux : forall (e : Expr) -> forall (x : Zipperdown e)
          -> forall (y : Zipperdown e) -> y < x -> Acc (IxltOp e) y
      aux dotted(Add (plug )) dotted((t2 , Left t1' :: s2)) , refl) dotted((t1 , Right n t2' eq :: s1), eq2) 
          (<-Right-Left eq1 eq2) = {!!}
      aux ...
\end{code}

We have now the proof of well foundedness for the relation defined over top-down Zippers. We also have proven that
there is an equivalence between top-down and bottom-up Zippers. We exploit it by using the top-down encoding for
the termination proof while we use the bottom-up to actually compute in a tail recursive manner.

Thus we prove a lemma stating that if we apply unload to a bottom-up Zipper and this results in another
Zipper, then the result is smaller by the relation than the input. However, to show it we have to 
convert them to the top down representation. In overall, what we have is the following lemma:

\begin{code}
unload-ltop : forall n eq s t' s' -> unload (Tip n) (TipA n) eq s == inj₁ (t' , s') 
            -> (t' , reverse s') ltOp (n , reverse s) 
\end{code}

\subsection{Correctness}

Indexing the \emph{Zipper} with an expression allow us to prove correcness of
the transformation easily. The expression during the fold does not change, thus
in every step of the computation the result of its evaluation remains constant.

By using induction over the definition of unload, we can prove that when |unload| 
delivers a value, it corresponds to the result of evaluating of the input expression.
In order to do so, we enrich the type of |unload| to include the expression that has already
been folded and we have its result. 

\begin{code}
  unload : (e : Expr) -> (n : Nat) -> eval e == n -> Stack -> (Nat * Stack) U+ Nat

  unload-correct  : forall (e : Expr) (n : Nat) (eq : eval e == n) (s : Stack) (x : Nat)
                  -> unload e n eq s ≡ inj2 x -> eval e == x
\end{code}

Proving correctness of the whole transformation amounts to show that it holds for the
auxiliary recursor that we use to write the function |tail-rec-eval|. We use well founded 
recursion to do structural recursion over the accesibility predicate and use the lemma 
|unload-correct| in the base case.

\todo[inline]{STOP HERE}

\section{Regular universe}
  + Universe interpretation generic programming
  + Fixpoint
  + Example??
\section{Dissection}
  + Dissection in agda
  + Plug
  + Zipper up Zipper down
  + Make clear the separation between recursion in the functor level and
  the fix level
  + relation on dissection?
  
\section{Conclusion and future work}

%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This material is based upon work supported by the
  \grantsponsor{GS100000001}{National Science
    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
  conclusions or recommendations expressed in this material are those
  of the author and do not necessarily reflect the views of the
  National Science Foundation.
\end{acks}


%% Bibliography
\bibliography{main}



%% Appendix
\appendix
\section{Appendix}

Text of appendix \ldots

\end{document}
