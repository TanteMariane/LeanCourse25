## Project 2: your own formalisation project

## Personal Info

Please fill out the following. Fill in the project topic once you have decided.
```
First & last name: Lasse Lenzing
Project topic: Cayleys Formula
Partner (optional):
```

## Contents of the project
Tried to prove the more general statement of Cayleys formula using the proof via recursion (see [book of proofs](https://link.springer.com/book/10.1007/978-3-662-57767-7)). It says that there are $kn^{n-k-1}$ labeled forests on $n$ vertices, rooted in a $k$-vertex-set $R$. Where rooted in $R$ means that in each connected component of the forest there is exactly one element of $R$.
### What's proven
* We have a forest $F$ rooted in the set $R$. When we remove one vertex $w$ of $R$ from $F$, we get a forest that is rooted in $(R \setminus \{w\} \cup \{\text{neighbors } w\})$.
* This is an injection from the set of forests rooted in $R$ to the forests rooted in $(R \setminus \{w\} \cup \{\text{neighbors } w\})$.
### Unfinished
* The other way around is unfinished. We have two vertex-sets $N, R$ with $w \notin N \cup R$ and a forest $F$ rooted in the set $R \cup N$. Now we add the vertex $w$, such that $w$ gets connected to all vertices in $N$. The resulting graph is a forest rooted in the set $R \cup \{w\}$.
* I defined the function for this procedure. But I didn't prove that the resulting graph is a forest, what are its roots, nor that it's an injection.
* What is left then, is to use these two injections to get a bijection FROM the set of forests rooted in $R$ where $w$ has neighborset $N$ TO the forests rooted in $(R \setminus \{w\} \cup \{\text{neighbors } w\})$. We know the size of the second set by induction and then we can sum up over all possible choices of the set $N$.

## References/sources
* Mathlib4 search
* I used GPT-4.1 for asking syntax questions about Lean, also for
  *  declare things as type or subset
  *  use of rcases
* Every piece of code is written by myself
