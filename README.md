# Lambda Calculus Formalization in Lean4

- [Lambda Calculus Formalization in Lean4](#lambda-calculus-formalization-in-lean4)
  - [A brief introduction to de Bruijn indices](#a-brief-introduction-to-de-bruijn-indices)
    - [Shifting and Unshifting](#shifting-and-unshifting)
    - [Substitution](#substitution)
    - [Beta reductions in redex](#beta-reductions-in-redex)
  - [TODO](#todo)

This repository contains code that formalizes the lambda calculus using de Bruijn indices. The main goal is to prove the Church–Rosser theorem, one of the most important and challenging results in lambda calculus.

Some lemmas required for key theorems were adapted from other lambda calculus formalizations, which are listed below:

- [LeanScratch](https://github.com/chenson2018/LeanScratch) — Created by Chris Henson. This repository was my main reference for obtaining several lemmas.  
- [A Formalization of Typed and Untyped λ-Calculi in Coq and Agda2](https://github.com/pi8027/lambda-calculus) — Created by Kazuhiko Sakaguchi, written in Rocq and Agda. I find this work particularly impressive.

## A brief introduction to de Bruijn indices

De Bruijn indices provide a way to represent lambda calculus terms without naming bound variables.  
Instead of using variable names, each variable is represented by a natural number that indicates how many binders ($\lambda$) separate it from its corresponding abstraction.

Formally, the syntax of lambda terms using de Bruijn indices is defined as:
$$
    \Lambda := \N \mid (\Lambda\ \Lambda) \mid (\lambda\ \Lambda).
$$

Here, variables are natural numbers, and each number refers to its binder according to its distance.  
For example:

| Standard                                                     | de Bruijn                                           |
| ------------------------------------------------------------ | --------------------------------------------------- |
| $\lambda x.\, x$                                             | $\lambda\, 0$                                       |
| $\lambda x.\, \lambda y.\, x$                                | $\lambda\, \lambda\, 1$                             |
| $\lambda x.\, \lambda y.\, x\, x\, y\, (\lambda z.\, z\, x)$ | $\lambda\, \lambda\, 1\, 1\, 0\, (\lambda\, 0\, 2)$ |

### Shifting and Unshifting

The shifting operation is defined as an adjustment that increases the indices of free variables whose values are greater than or equal to the context $c$.
$$
\begin{aligned}
    \uparrow_c^d n &=
    \begin{cases}
        n & \text{if } n < c, \\
        n + d & \text{otherwise},
    \end{cases} \\[1em]
    \uparrow_c^d(\lambda N) &= \lambda (\uparrow_{c + 1}^d N), \\[0.5em]
    \uparrow_c^d(N_1\ N_2) &= (\uparrow_c^d N_1)\ (\uparrow_c^d N_2).
\end{aligned}
$$
Here, $c$ is called the **context**, and $d$ the **displacement**.
Similarly, we define the **unshifting** operation, which behaves the same way except that it decreases the index by $d$ instead of increasing it:
$$
\begin{aligned}
    \downarrow_c^d n &=
    \begin{cases}
        n & \text{if } n < c, \\
        n - d & \text{otherwise},
    \end{cases} \\[1em]
    \downarrow_c^d (\lambda N) &= \lambda (\downarrow_{c + 1}^d N), \\[0.5em]
    \downarrow_c^d (N_1\ N_2) &= (\downarrow_c^d N_1)\ (\downarrow_c^d N_2).
\end{aligned}
$$

### Substitution

The substitution operation replaces all occurrences of a variable in a term with another term. Its formal definition is as follows:
$$
\begin{aligned}
    n[m := M]&=
    \begin{cases}
        M & \text{if } n = m, \\
        n & \text{otherwise},
    \end{cases} \\[1em]
    (\lambda N)[m := M] &= \lambda N[m + 1 := \uparrow_0^1 M], \\[0.5em]
    (N_1\ N_2)[m := M] &= (N_1 [m := M]) (N_2 [m := M]).
\end{aligned}
$$

In the case of an abstraction, we move one level deeper into the binding structure, so the context increases by one. That’s why we use **\( m + 1 \)**.

Additionally, we apply shifting ($\uparrow_0^1$) to the term $ M $ being substituted. This is necessary because $M$ is inserted into a context with one extra binder. Without shifting, the free variables of $N$ could become incorrectly bound, changing the meaning of the expression.  

### Beta reductions in redex

The following function expresses a beta reduction step of the term $(\lambda M) N$
$$
\texttt{beta}\ M\  N := \ \downarrow_0^1 (M[0 := \uparrow_0^1 N])
$$

The beta reduction replaces the bound variable inside the abstraction $M$ with the argument $N$. However, since $N$ is being inserted into the body of a $\lambda$-abstraction, its free variables must be adjusted to account for the new binding level. This is why we first shift $N$ by one position before performing the substitution.

After substitution, the abstraction disappears — we have exited one binding level. Therefore, we apply unshifting to the resulting term to restore the correct indices.

> _**Note:**_
> This function is used to inductively define the beta reduction relation.

## TODO

- [x] Write all definitions.
- [x] Define the beta reduction and beta reduction relations.
- [x] Show that parallel beta reduction satisfies the diamond property.
- [ ] Prove the Church-Rosser theorem.
- [ ] Writing a Blueprint.
