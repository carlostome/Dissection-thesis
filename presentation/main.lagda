\documentclass[notes]{beamer}
\usepackage{beamerthemeuucs}
\setbeamercovered{transparent} 
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{bbold} %% Font for fancy math letters

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

\title{Verified tail-recursive folds through dissection}
\subtitle{Thesis defense}
\author{Carlos Tomé Cortiñas}
\date{\today}
\begin{document}
\frame{\titlepage}
\section{Introduction}
\subsection{Motivation}

\frame{
  \frametitle{|Expr|ession language\footnote{Hutton's razor}}
  \begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
  \end{code}

  \pause

  \begin{center}
  \begin{columns}[b]
    \begin{column}{0.5\textwidth}
      \begin{code}
        expr1 : Expr
        expr1 = Add  (Val 1) 
                     (Add  (Val 2) 
                           (Val 2))
      \end{code}
    \end{column}
    \begin{column}{0.5\textwidth}
      \input{figures/figure1}
    \end{column}
  \end{columns}
  \end{center}
}


\frame{
  \frametitle{Evaluating |Expr|essions}
  \begin{code}
    eval : Expr -> Nat
    eval (Val n)      = n
    eval (Add e1 e2)  = eval e1 + eval e2
  \end{code}

  \pause 
  \vspace*{-0.5cm}
  \begin{code}
    prop1 : eval expr1 == 5
    prop1 = refl
  \end{code}

  \pause

  {\Large Is there a \textbf{problem} with |eval|?}

}

\frame{
  \frametitle{Evaluating |Expr|essions (2)}

  \begin{code}
    eval : Expr -> Nat
    eval (Val n)      = n
    eval (Add e1 e2)  = eval e1 + eval e2
  \end{code}

  |eval  (Add (Val 1) (Add  (Val 2)  (Val 2))|

  \pause

  \vspace*{-1em}
  \begin{center}
    \begin{itemize}
      \setlength{\itemindent}{2em}
      \uncover<2>{\item[|~>|] | eval (Val 1)  + eval (Add  (Val 2)  (Val 2))|}
      \uncover<3>{\item[|~>|] | 1             + eval (Add (Val 2) (Val 2))|}
      \uncover<4>{\item[|~>|] | 1             + (eval (Val 2) + eval (Val 2))|}
      \uncover<5>{\item[|~>|] | 1             + (2 + eval (Val 2)) ...|}
    \end{itemize}
  \end{center}
        
}

\frame{
  \frametitle{Evaluating |Expr|essions (3)}

  \begin{code}
    Add (Val 1) (Add (Val 2) (Add (Val 3) (Add (Val 4) ...
  \end{code}

  \pause

  \begin{code}
    1 + (2 + (3 + (4 + ...
  \end{code}
        
  \pause

  \hspace{1cm} {\large \textbf{Yes}, |eval| \underline{is not} a \textit{tail-recursive} function}

  \pause

  \begin{itemize}[<+->]
    \item The execution \textit{stack} grows linearly with the size of the |Expr|
    \item \alert{Stack Overflow} 
  \end{itemize}

  \pause[\thebeamerpauses]

  \begin{center}
    {\Large A \textbf{well-typed} program \textit{went wrong}\footnote{Robin
    Milner does not approve}}
  \end{center}
}

\frame{
  \frametitle{Can we solve the problem?}

  \begin{itemize}[<+->]
    \item Make the \textit{stack} explicit
    \item Write a \textit{tail-recursive} function that recurses over it
  \end{itemize}

  \pause[\thebeamerpauses]
\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

}

\frame{
  \frametitle{Can we solve the problem? (2)}

\begin{code}
  mutual
    load : Expr -> Stack -> Nat
    load (Val n)      stk = unload n stk
    load (Add e1 e2)  stk = load e1 (Left e2 stk)

    unload : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unload (v' + v) stk
    unload v   (Left e stk)    = load e (Right v stk)
\end{code}

\pause

\vspace*{-1em}
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = load e Top
\end{code}

}

\frame{
  \frametitle{Can we solve the problem? (3)}

  \begin{center}
    \only<1>{|load (Add (Val 1) (Add (Val 2) (Val 2))) Top|}
    \only<2>{|load (Val 1) (Left (Add (Val 2) (Val 2)) Top)|}
    \only<3>{|unload 1 (Left (Add (Val 2) (Val 2)) Top)|}
    \only<4>{|load (Add (Val 2) (Val 2)) (Right 1 Top)|}
    \only<5>{|load (Val 2) (Left (Val 2) (Right 1 Top))|}
    \only<6>{|unload 2 (Left (Val 2) (Right 1 Top))|}
    \only<7>{|load (Val 2) (Right 2 (Right 1 Top))|}
    \only<8>{|unload 2 (Right 2 (Right 1 Top))|}
    \only<9>{|unload (2 + 2) (Right 1 Top)|}
    \only<10>{|unload 4 (Right 1 Top)|}
    \only<11>{|unload (1 + 4) Top|}
    \only<12>{|unload 5 Top|}

    \input{figures/figure2}
  \end{center}
}

\frame{
  \frametitle{Can we solve the problem? (4)}
  {\Large Have we \textbf{actually} solved the problem?}
  \pause
  \begin{itemize}[<+->]
      \item It seems so, however ...
      \item How do we know that 
        
        \begin{center}
        |forall (e : Expr) -> tail-rec-eval e == eval e| ?
        \end{center}
      \item We \textbf{don't} know, we \textbf{don't} have a \textit{mathematical proof}
      \item Let's \textit{produce} it!
  \end{itemize}
}

\frame{
  \frametitle{Can we solve the problem? (5)}
  \begin{itemize}[<+->]
    \item Is \textbf{not} that easy
    \item Tail-recursion has come at a \textbf{price}
  \end{itemize}
  \pause[\thebeamerpauses]
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unloadN (v' + v) stk
    unload v   (Left e stk)    = loadN e (Right v stk)
\end{code}
}

\subsection{Contributions of this Master Thesis}
\frame{
  \frametitle{Contributions}
  \pause
  \begin{itemize}[<+->]
    \item We construct a provably \textbf{terminating} tail-recursive function \textit{similar} to |tail-rec-eval|
    \item We prove it \textbf{correct} with respect to |eval|
    \item We \textbf{generalize} our results to any fold over any (simple)
      algebraic datatype using McBride's notion of \textit{dissection}
  \end{itemize}
  \pause[\thebeamerpauses]
  \begin{center}
    We have formalized everything in \textbf{Agda}
  \end{center}
}

\section*{Outline}
\frame{\tableofcontents}

\section{A tail-recursive evaluator for |Expr|}

\subsection{Problem with |tail-rec-eval|}
\frame{
  \frametitle{Problematic call}
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unloadN (v' + v) stk
    unload v   (Left e stk)    = loadN e (Right v stk)
\end{code}
}

\frame{
  \frametitle{Traversing the |Expr|}
  \begin{itemize}[<+->]
      \item |load| and |unload| traverse the |Expr| left to right
      \item The functions use the |Stack| \underline{only} to store subexpressions
            of the input expression
      \item How do we convince \textbf{Agda} of this fact?
  \end{itemize}
}

\frame{
  \frametitle{Traversing the |Expr| (2)}
  \begin{itemize}[<+->]
    \item We rewrite |load| and |unload| to compute \textbf{one} step of the
      evaluation
  \end{itemize}
  \pause[\thebeamerpauses]
\begin{code}
  load : Expr -> Stack -> (Nat * Stack) U+ Nat
  load (Val n)      stk = inj1 (n , stk)
  load (Add e1 e2)  stk = load e1 (Left e2 stk)

  unload : Nat -> Stack -> (Nat * Stack) U+ Nat
  unload v   Top             = inj2 v
  unload v   (Right v' stk)  = unload (v' + v) stk
  unload v   (Left e stk)    = load e (Right v stk)
\end{code}
}

\section{A generic tail-recursive evaluator}
\section{Conclusions}
\end{document}
