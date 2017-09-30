\documentclass[a4paper]{article}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage[draft]{todonotes}
% \usepackage[disable]{todonotes}
\usepackage{framed,color}
% \usepackage{multirow}
\usepackage{alltt}
\usepackage{amsthm}

%% lhs2TeX stuff

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

%% Agda stuff

\usepackage[bw]{agda}
\usepackage{catchfilebetweentags}

\newcommand{\InsertCodeInline}[2]{
  % \codeinlinetrue
  \ExecuteMetaData[../src-tex/#1]{#2}
}
\newcommand{\InsertCode}[2]{
  % \codeinlinefalse
  \medskip
  \ExecuteMetaData[../src-tex/#1]{#2}
  \medskip
}

\usepackage{newunicodechar}

\title{}
\date{\today}
\author{}

\begin{document}

\maketitle

% \begin{flushright}
% \emph{Supervised by} Wouter Swierstra\\
% \emph{Second examiner} Johan Jeuring
% \end{flushright}

% \listoftodos
\input{introduction.tex}
\input{literature.tex}
% \input{prototype.tex}
% \input{overview.tex}
% \input{plan.tex}

\bibliographystyle{plain}
% \bibliographystyle{alpha}
% \bibliographystyle{apa}
\bibliography{main}

\end{document}
