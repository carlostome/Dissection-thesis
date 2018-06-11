%include lhs2TeX.fmt
%include background.fmt

\chapter{Background}

- Fold in a bigger context -> 

understood that semantics of a programming language Programming languages can be studied by writting interpretes for 
Metalanguages such as ML or Haskell Programming languages represented as AST in a meta
language.

duality between tail recursive functions and abstract machines?

- Denotational semantics of the language can be expresed as a fold in the
metalanguage.

- Danvy et al have managed to derive from a one step reduction function (small
step semantics) a tail recursive abstract machine in ML.

  -> They state that the problem of doing so in a simply typed metalanguage such as ML 
     is that the types are not as precise as they could be to rule out cases
     that cannot happen.

    Dependently typed programming to the rescue!

     that are imposible but the type system is not rich enough to  
  -> Problems is that is not easy to use a theorem prover to verify that the
  construction they make is correct wrt the initial reduction function.
  Their construction works in a series of steps that deliver a tail recursive fu

  - The first part of proving correctness amounts to prove that the function
    in the metalanguage that performs the reduction free evaluation terminates.
    The first action of finding the leftmost redex avaliable for reduction is
    not defined by structural recursion over its arguments thus termination
    checkers built in theore provers flag the function as non terminating. The
    overal problem resides is that during the process of doing depth-first search
    through the input tree where subtrees still to be visited are saved into a
    Stack (represented by a list) when the search arrives to a point that it has
    to retrieve a subtree from the stack to proceed with the search and store
    in the stack a value corresponding to a leaf that is stored in the left
    subtree of a node, the recursive call is made over a Stack that is not
    structurally smaller than the input.

    
    Moreover, 

    To put it another way, we can think of the stack used to perform the
    depth-first search over the tree as a execution stack. By making the execution
    stack explicit we lose the ability to connect the contents of the simply
    typed stack with the original tree and thus it requires us a great deal of
    work to use tools such as well founded recursion to convince the theorem
    prover that something is going smaller during the search.
