\documentclass{beamer}
\usepackage{beamerthemeuucs}
% \setbeamercovered{transparent} 

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{bbold} %% Font for fancy math letters
\usepackage{dsfont} %% Font for fancy math letters
\usepackage{scalerel}
\usepackage{graphicx}
% \usepackage{enumitem}
% \usepackage{showframe}

%% Agda stuff
\usepackage[conor]{agda}
\usepackage[draft]{todonotes}
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

\usepackage{tikz}
\usetikzlibrary{arrows,snakes,backgrounds,calc}
\newcommand{\pgftextcircled}[1]{
    \setbox0=\hbox{#1}%
    \dimen0\wd0%
    \divide\dimen0 by 2%
    \begin{tikzpicture}[baseline=(a.base)]%
        \useasboundingbox (-\the\dimen0,0pt) rectangle (\the\dimen0,1pt);
        \node[circle,draw,outer sep=0pt,inner sep=0.1ex] (a) {\textbf{#1}};
    \end{tikzpicture}
}

%include presentation.fmt

\renewcommand\hscodestyle{%
   \setlength\leftskip{0.1cm}%
   \small
}
\title{Verified tail-recursive folds through dissection}
% \subtitle{TyDe'18}
\author{Carlos Tomé Cortiñas}
\date{9 November 2018\\

}


\begin{document}
\frame{\titlepage}

%{ beginning of part1
%include part1.fmt

\frame{
  \frametitle{To put it another way ...}
  \begin{center}
    {\Large{\emph{\textbf{From Algebra to Abstract Machine:\\ A Verified Generic
    Construction}}}}\\
    \vspace{1em}

    {\large TyDe'18}\\
    \vspace{1em}
    {\large Carlos Tomé Cortiñas and Wouter Swierstra}
  \end{center}
}

\section{Motivation}

\frame{
  \frametitle{Motivation}

  We start with a small |Expr|ession language

  \pause

  \begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
  \end{code}

  \pause

  and we write an |eval|uator for it.

  \pause

  \begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
  \end{code}
}


\frame{
  \frametitle{A Problem with |eval|}

  \begin{code}
    > eval (Add (Add (Add ... (Add (Val 1) (Val 2))))) -- large expression
  \end{code}
  \pause
  \vspace*{-1cm}
  \begin{code}
    *** Exception: stack overflow
  \end{code}

  \pause

  What happened? \pause A \textbf{well-typed} program \textit{went wrong}.

  \pause

  \begin{itemize}[<+->]
    \setlength\itemsep{1em}
    \item |eval| evaluates  \underline{both} subtrees before reducing |plusOp|
      further.
    \item Record unevaluated subtrees on the stack.
    \item On large inputs, the \textbf{stack} might \textbf{overflow}.
  \end{itemize}
}

\frame{
  \frametitle{A solution to the problem}

  \pause
  \begin{center}
    \Large{Write a \textbf{tail-recursive} evaluator.}
  \end{center}

  \pause
  We proceed in \textit{three steps}:

  \pause

  \begin{itemize}[<+->]
    \setlength\itemsep{1em}
    \item Make the underlying stack \underline{explicit}.
    \item Define a \textit{tail-recursive} function over the stack.
    \item Show that it is equivalent to |eval|.
  \end{itemize}
}


\frame{
  \frametitle{A tail-recursive evaluator}

  \begin{code}
    data Stack : Set where
      Top    : Stack
      Left   : Expr  -> Stack -> Stack
      Right  : Nat   -> Stack -> Stack
  \end{code}

  \pause
  \vspace*{-0.5cm}
  \begin{code}
  mutual
    load : Expr -> Stack -> Nat
    load (Val n)      stk = unload1 n stk
    load (Add e1 e2)  stk = load e1 (Left e2 stk)

    unload1 : Nat -> Stack -> Nat
    unload1 v   Top             = v
    unload1 v   (Left e stk)    = load e (Right v stk)
    unload1 v   (Right v' stk)  = unload1 (v' + v) stk
  \end{code}
  \pause
  \vspace*{-1cm}
  \begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = load e Top
  \end{code}
}

%{
%format Top   = "\underline{\AI{Top}}"
%format Left  = "\underline{\AI{Left}}"
%format Right = "\underline{\AI{Right}}"

\frame {
  \frametitle{|tail-rec-eval| in action}

  \begin{center}
    \only<1>{\Large|load (Add (Val 1) (Add (Val 2) (Val 2))) Top|}
    \only<2>{\Large|load (Val 1) (Left (Add (Val 2) (Val 2)) Top)|}
    \only<3>{\Large|unload1 1 (Left (Add (Val 2) (Val 2)) Top)|}
    \only<4>{\Large|load (Add (Val 2) (Val 2)) (Right 1 Top)|}
    \only<5>{\Large|load (Val 2) (Left (Val 2) (Right 1 Top))|}
    \only<6>{\Large|unload1 2 (Left (Val 2) (Right 1 Top))|}
    \only<7>{\Large|load (Val 2) (Right 2 (Right 1 Top))|}
    \only<8>{\Large|unload1 2 (Right 2 (Right 1 Top))|}
    \only<9>{\Large|unload1 (2 + 2) (Right 1 Top)|}
    \only<10>{\Large|unload1 4 (Right 1 Top)|}
    \only<11>{\Large|unload1 (1 + 4) Top|}
    \only<12>{\Large|unload1 5 Top|}

    \input{figure}
  \end{center}
}
%}

\frame{
  \frametitle{Problem solved?}

  \begin{center}
    {\large Have we \textbf{actually} solved the problem?}
  \end{center}

  \pause

  Is \textbf{really} |tail-rec-eval| \textit{equivalent} to |eval|? \pause Can we \underline{prove} it?

  \pause

  \begin{code}
    mutual
      loadN : Expr -> Stack -> Nat
      ...

      unloadN : Nat -> Stack -> Nat
      unload1 v   Top             = v
      unload1 v   (Left e stk)    = loadN e (Right v stk)
      unload1 v   (Right v' stk)  = unloadN (v' + v) stk
  \end{code}

  \pause

  We \textbf{lost} termination guarantees.
}

\section{Contributions}

\frame{
  \frametitle{Contributions}
  \begin{itemize}[<+->]
    \setlength\itemsep{2em}
    \item[\textbf{Termination}] We \textbf{construct} a tail-recursive evaluator that terminates
        for every input.
    \item[\textbf{Correctness}] We \textbf{prove} it equal to the original |eval| function.
    \item[\textbf{Generalization}]<0> We generalize our result to any
      \textit{catamorphism} and any \textit{algebra} over any \textbf{regular} datatype.
  \end{itemize}
}

\frame{
  \frametitle{That's not all}
  |eval| is an example of a \textit{fold} over the |Expr| datatype.

  \pause

  \begin{code}
    foldExpr : (a -> a -> a) -> (Nat -> a) -> Expr -> Nat
    foldExpr phi1 phi2 (Val n)      = phi2 n
    foldExpr phi1 phi2 (Add e1 e2)  = phi1 (foldExpr phi1 phi2 e1) (foldExpr phi1 phi2 e2)
  \end{code}

  \pause

  Both versions of the function are \underline{the same}.

  \pause

  \begin{code}
    forall (e : Expr) -> eval e == foldExpr plusOp id e
  \end{code}

  \pause

  Moreover:

  \pause

  \begin{itemize}[<+->]
     \item |Expr| is an example of a \textbf{regular} type.
     \item |foldExpr| is an instance of a \textbf{catamorphism}.
  \end{itemize}
}

\frame{
  \frametitle{Contributions}
  \hspace{3em\hspace{3em}}\begin{itemize}
    \setlength\itemsep{2em}
    \item[\textbf{Termination}] We \textbf{construct} a tail-recursive evaluator that terminates
        for every input.
    \item[\textbf{Correctness}] We \textbf{prove} it equal to the original |eval| function.
    \pause
    \item[\textbf{Generalization}] We generalize our result to any
      \textit{catamorphism} and any \textit{algebra} over any \textbf{regular} datatype.
  \end{itemize}

  \pause

  \hspace{1em}\Large{Everything is machine-checked by \textit{Agda}}.
}


\section{Solving the problem}

\frame{
  \frametitle{Plan of attack}
  \begin{enumerate}[<+->]
    \setlength\itemsep{1em}
    \item Break down the |mutual| recursion in |load| and |unload1|.
    \item Use |unload| to iterate through an |Expr| to get a value.
    \item Show that |unload| delivers something ``smaller``, thus the iteration
      terminates.
    \item Prove that the resulting function is equivalent to |eval|.
  \end{enumerate}
}

\frame{
  \frametitle{Breaking down mutual recursion}

 \begin{code}
   unload : (Nat * Stack) -> (Nat * Stack) U+ Nat
   unload (v ,  Top           )  = inj2 v
   unload (v ,  Right v' stk  )  = unload (v' + v , stk)
   unload (v ,  Left e stk    )  = load e (Right v stk)
 \end{code}

 \pause

 \begin{code}
   load : Expr -> Stack -> (Nat * Stack) U+ Nat
   load (Val n)      stk = inj1 (n , stk)
   load (Add e1 e2)  stk = load e1 (Left e2 stk)
 \end{code}

 \pause
 Now, both functions \emph{obviously} terminate.
}


\frame{
  \frametitle{A step back}

  \begin{center}
    \only<1-3>{\large |unload : (Nat * Stack) -> (Nat * Stack) U+ Nat|}
    \only<4>{\large |unload : ZipperType -> ZipperType U+ Nat|}
  \end{center}
  \pause
  \begin{itemize}[<+->]
    \setlength\itemsep{1em}
    \item |unload| is the ``step`` function of an \underline{abstract machine}!

    \item Configurations: |ZipperType = Nat * Stack|
  \end{itemize}
}

\frame{
  \frametitle{Well-founded recursion}
    \begin{itemize}[<+->]
    \setlength\itemsep{1.25em}
      \item Function |f : a -> a| \textbf{not} defined by structural recursion.
      \item A relation |LtOp : a -> a -> Set|, such that |f' a < a|.
      \item No infinitely long \textbf{decreasing chains}\\
        \hspace*{5em} $\Longrightarrow$ recursion eventually
        \underline{terminates}.
      \item In \textit{Agda}, the \emph{accessibility predicate}.
      \item A relation is \textbf{well-founded} if every element is accessible.
    \end{itemize}
}


\frame{
  \frametitle{Another tail-recursive evaluator}

  Iterate |unload| until a value is produced.

  \pause

  \begin{code}
    tail-rec-eval : Expr -> Nat
    tail-rec-eval e with load e Top
      ... | inj1 z  = rec (<-Well-founded z) z
      where
        rec : (z : ZipperType) -> Acc LtOp z -> Nat
        rec z (acc rs) with unload z
        ... | inj1 z'  = rec (rs ...) z'
        ... | inj2 r   = r
  \end{code}

  \pause

  Still, we have to:

  \pause
  \begin{itemize}[<+->]
      \item |LtOp : ZipperType -> ZipperType -> Set|
      \item |forall (z z' : ZipperType) -> unload z == inj1 z' -> z' < z|
      \item |Well-founded LtOp|
  \end{itemize}
}


\frame{
  \frametitle{The relation}
  \begin{itemize}[<+->]
    \setlength\itemsep{1em}
    \item |ZipperType| \textit{uniquely} represents a leaf in an |Expr|ession.

    \item Order configurations left to right.

    \item Inductive relation on the |Stack|.

    \pause[\thebeamerpauses]

  \begin{code}
    data LtOp : ZipperType -> ZipperType -> Set where
     <-StepR  : (t1 , s1) < (t2 , s2)
              ->  (t1 , Right l n eq s1) < (t2 , Right l n eq s2)
     <-StepL  : (t1 , s1) < (t2 , s2)
              ->  (t1 , Left r s1) < (t2 , Left r s2)
     <-Base   : (t1 , Right n e1 eq s1) < (t2 , Left e2 s2)
  \end{code}
  \end{itemize}
}

\frame{
  \frametitle{The details}

  \begin{itemize}
    \item Two distinct values of |ZipperType| \textbf{can} represent folds over different |Expr|essions.

    \pause
      \begin{code}
        data Zipperdown (e : Expr) : Set where
          _,_ : (z : ZipperType) -> plugZdown z == e -> Zipperdown e
      \end{code}

    \pause
    \item A \textbf{type-indexed} relation to enforce the \underline{invariant}.

    \pause
      \begin{code}
         IxLtOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set
      \end{code}
    \pause
    \item It is \underline{needed} to show the relation is \textbf{well-founded}.
  \end{itemize}
}

\frame{
  \frametitle{The rest (omitted)}
  \begin{itemize}[<+->]
    \setlength\itemsep{1em}
    \item \underline{Proof of \textbf{well-foundedness}:} not too hard.
    \item \underline{Proof that |unload| delivers a smaller result:} tedious but
      easy.
    \item \underline{Proof of correctness:} follows from well-founded recursion.
  \end{itemize}
}
%}
%{
%include part2.fmt

\section{Generalization}
\frame{
  \frametitle{Generalization}
    \begin{itemize}[<+->]
      \setlength\itemsep{1em}
      \item Universe of \textbf{regular} datatypes of which |Expr| is an instance.
      \item McBride's \underline{dissection} to calculate generic |Stack3|s.
      \item Generalize |load| and |unload|.
      \item Generic \underline{well-founded} relation.
      \item |unload| decreases.
      \item Assemble everything together.
    \end{itemize}
  }
\renewcommand\hscodestyle{%
   \setlength\leftskip{-0.1cm}%
   \small
}
\frame{
  \frametitle{\textbf{regular} universe}
\begin{minipage}[c]{0.5\textwidth}
\begin{code}
  data Reg : Set1 where
    Zero  : Reg
    One   : Reg
    I     : Reg
    K     : (A : Set) -> Reg
    O+Op  : (R Q : Reg)  -> Reg
    O*Op  : (R Q : Reg) -> Reg
\end{code}
\end{minipage}
\begin{minipage}[c]{0.4\textwidth}
\pause
\begin{code}
  interp : Reg -> (Set -> Set)
  interpl Zero interpr X       = Bot
  interpl One interpr X        = Top
  interpl I interpr X          = X
  interpl (K A) interpr X      = A
  interpl (R O+ Q) interpr X   = interpl R interpr X U+ interpl Q interpr X
  interpl (R O* Q) interpr X   = interpl R interpr X * interpl Q interpr X
\end{code}
\end{minipage}
  \pause
  \begin{code}
     data mu (R : Reg) : Set where
         In : interpl R interpr (mu R) -> mu R
  \end{code}
  \pause
  \vspace*{-1.5em}
  \begin{code}
    cata : (R : Reg) -> (interpl R interpr X -> X) -> mu R -> X
    cata R alg (In r) = alg (fmap R (cata R alg) r)
 \end{code}
}

\frame{
  \frametitle{By example}

  \begin{itemize}[<+->]
      \item Original type:
    \begin{code}
    data Expr : Set where
      Val  :  Nat   -> Expr
      Add  :  Expr  -> Expr -> Expr
    \end{code}

     \item Generic representation:

    \begin{code}
    expr : Reg
    expr = K Nat O+ (I O* I)
    \end{code}

     \item Isomorphism:

    \begin{code}
    Expr ~= mu expr
    \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Dissections}
  \begin{itemize}[<+->]
      \item ``One hole`` context of a functor.

    \begin{code}
      nabla : (R : Reg) -> (Set -> Set -> Set)
      nabla Zero      X Y  = Bot
      nabla One       X Y  = Bot
      nabla I         X Y  = Top
      nabla (K A)     X Y  = Bot
      nabla (R O+ Q)  X Y  = nabla R X Y U+ nabla Q X Y
      nabla (R O* Q)  X Y   =            (nabla R X Y           * interpl Q interpr Y   ) U+  (interpl R interpr X   * nabla Q X Y           )
    \end{code}


     \item By example:

    \begin{code}
      Stack3 ~= List (nabla expr Nat (mu expr))
    \end{code}
  \end{itemize}
}

\section{Conclusion}
\frame{
  \frametitle{Our results}
  \pause
    A generic tail-recursive evaluator

    \begin{code}
        tail-rec-cata : (R : Reg) -> (alg : interpl R interpr X -> X) -> mu R -> X
    \end{code}

  \pause
    and its correctness proof.

    \begin{code}
    correctness  : forall (R : Reg) (alg : interpl R interpr X -> X) (t : mu R)
                 -> catamorphism R alg t == tail-rec-cata R alg t
    \end{code}

  \pause
  Still a lot of details to fill in:
  \begin{itemize}[<+->]
      \item What is a leaf, generically?
      \item How do we compare generic configurations?
      \item Generic relation and its well-foundedess proof
      \item ...
  \end{itemize}
  }

% \frame{
%   \frametitle{Conclusion}
%   \hspace{3em\hspace{3em}}\begin{itemize}
%     \setlength\itemsep{2em}
%     \item[\textbf{Termination}] We \textbf{construct} a tail-recursive evaluator that terminates
%         for every input.
%     \item[\textbf{Correctness}] We \textbf{prove} it equal to the original |eval| function.
%     \item[\textbf{Generalization}] We generalize our result to any
%       \textit{catamorphism} and any \textit{algebra} over any \textbf{regular} datatype.
%   \end{itemize}


%   \hspace{1em}\Large{Everything is machine-checked by \textit{Agda}}.
% }

% \frame{
%   \frametitle{Contributions}
%   \begin{itemize}
%     \setlength\itemsep{2em}
%     \item[\textbf{Termination}] We \textbf{construct} a tail-recursive evaluator that terminates
%         for every input.
%     \item[\textbf{Correctness}] We \textbf{prove} it equal to the original |eval| function.
%     \item[\textbf{Generalization}] We generalize our result to any \textit{catamorphism} over any
%                         datatype expressible in the \textbf{regular} universe.
%   \end{itemize}
% }

\frame{
  \centering
  {\Large For more technical details:}\\
  \vspace{1em}

  {\Large My \underline{master's thesis} (long) or the \textbf{paper} (short)}\\
  \vspace{1em}

  {\Large and the \textit{Agda code}.}\\
  \vspace{2em}

  \pause

  {\Large \emph{Thank you} very much for your attention!}
}

\end{document}
