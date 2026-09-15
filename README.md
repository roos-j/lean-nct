# Formalization of norm-variation of multiple ergodic averages for commuting transformations

[![CI](https://github.com/roos-j/lean-nct/actions/workflows/publish-docs-and-graph.yml/badge.svg)](https://github.com/roos-j/lean-nct/actions/workflows/publish-docs-and-graph.yml)

[API documentation](https://pjroos.com/lean-nct/docs/) · [Blueprint](https://pjroos.com/lean-nct/blueprint/nct-blueprint.pdf) · [Dependency graph](https://pjroos.com/lean-nct/dependency_graph/)

This is a formalization of norm-variation of multiple ergodic averages for commuting transformations, including Tao's norm-convergence theorem.

This formalization is based on the blueprint also available on [arXiv](https://arxiv.org/abs/2608.27321).
The statements of the main theorems have been hand-formalized, while the proof was autoformalized during a one-week period using coding agents under human supervision. This produced roughly 107k lines of code (excluding comments and blank lines) and includes proofs of several prerequisite theorems currently not in mathlib such as multilinear complex interpolation, the Calderón transference principle, and properties of Wiener space functions.

## Main theorems

The definitions are in [LeanNct/Defs.lean](LeanNct/Defs.lean), and the main theorems are in [LeanNct/Theorems.lean](LeanNct/Theorems.lean).

For an $`n`$-tuple of functions $`\mathbf f=(f_j)_{0\le j\lt n}`$ and transformations $`(T_j)_{0\le j\lt n}`$, define the multiple ergodic averages, for positive integers $`N`$, by

```math
M_N(\mathbf f)(x)=\frac{1}{N}\sum_{i=0}^{N-1}\prod_{j=0}^{n-1}f_j(T_j^i x).
```

For a sequence $`a`$ in a normed space $`B`$, its $`r`$-variation seminorm is defined using increasing positive integers $`t_0,\ldots,t_J`$ by

```math
\|a\|_{V_r(B)}
=\sup_{J\in\mathbb N}\ \sup_{1\le t_0\lt\cdots\lt t_J}
\left(\sum_{j=0}^{J-1}\|a(t_{j+1})-a(t_j)\|_B^r\right)^{1/r}.
```

### Main ergodic theorem

**`nCT.main_ergodic_theorem`.** Let $`n\ge2`$ be an integer and let $`r>2^{n-1}`$, or $`r\ge2`$ if $`n=2`$. Let $`(X,\Sigma,\mu)`$ be a $`\sigma`$-finite measure space, let $`(T_j)_{0\le j\lt n}`$ be mutually commuting measure-preserving transformations on $`X`$, and let $`\mathbf f=(f_j)_{0\le j\lt n}`$ be complex-valued measurable functions with $`\|f_j\|_{L^{2n}(X)}\lt \infty`$ for every $`j`$.

Then $`M_N(\mathbf f)`$ is measurable with finite $`L^2(X)`$ norm for every positive integer $`N`$, and

```math
\big\|\big(M_N(\mathbf f)\big)_{N\ge1}\big\|_{V_r(L^2(X))}
\le C_{n,r}\prod_{j=0}^{n-1}\|f_j\|_{L^{2n}(X)},
```

where the constant defined in `nCT.C_main_ergodic_theorem` is

```math
C_{n,r}=\begin{cases}
2^{344}, & n=2,\\
2^{4n+337}\left(\dfrac{r}{r-2^{n-1}}\right)^{1/r}, & n\ge3.
\end{cases}
```

### Tao's norm-convergence theorem

**`nCT.tao_norm_convergence`.** Let $`n\ge1`$ be an integer. Let $`(X,\Sigma,\mu)`$ be a probability space, let $`(T_j)_{0\le j\lt n}`$ be mutually commuting invertible measure-preserving transformations on $`X`$, and let $`\mathbf f=(f_j)_{0\le j\lt n}`$ be complex-valued measurable functions with $`\|f_j\|_{L^\infty(X)}\lt \infty`$ for every $`j`$.

Then $`M_N(\mathbf f)`$ converges in $`L^2(X)`$ as $`N\to\infty`$. In other words, there exists a measurable complex-valued function $`g`$ with finite $`L^2(X)`$ norm such that

```math
\lim_{N\to\infty}\|M_N(\mathbf f)-g\|_{L^2(X)}=0.
```

The Lean statement also includes the trivial case $`n=0`$.

### Main twisted theorem

For real-valued functions $`\mathbf f=(f_i)_{0\le i\lt n}`$ on $`\mathbb R^n`$, a function $`\chi:\mathbb R\to\mathbb R`$, and $`t>0`$, define

```math
A_t(\chi,\mathbf f)(x)
=\int_{\mathbb R}t^{-1}\chi(t^{-1}s)\prod_{i=0}^{n-1}f_i(x+s e_i)\,ds,
```

where $`e_i`$ is the $`i`$th standard unit vector.

**`nCT.main_twisted_theorem`.** Let $`n\ge2`$ be an integer. For every $`J\in\mathbb N`$, positive real numbers $`t_0\lt t_1\lt \cdots\lt t_J`$, and $`n`$-tuple of real-valued Schwartz functions $`\mathbf f=(f_i)_{0\le i\lt n}`$ on $`\mathbb R^n`$ satisfying

```math
\|f_i\|_{L^{2^{\min(n,i+2)}}(\mathbb R^n)}=1
\qquad (0\le i\lt n),
```

we have

```math
\sum_{j=0}^{J-1}
\left\|A_{t_{j+1}}(\mathbf 1_{[0,1]},\mathbf f)
-A_{t_j}(\mathbf 1_{[0,1]},\mathbf f)\right\|_{L^2(\mathbb R^n)}^2
\le 2^{666}J^{1-2^{-n+2}}.
```

The case $`J=0`$ is allowed and the conclusion then holds trivially.

## Build instructions

Install Lean 4 following the instructions [here](https://lean-lang.org/install/), then run:

```sh
git clone https://github.com/roos-j/lean-nct
cd lean-nct
lake exe cache get!
lake build
```
