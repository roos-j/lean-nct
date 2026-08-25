# Formalization of norm-variation of multiple ergodic averages for commuting transformations

[API documentation](https://pjroos.com/lean-nct/docs/)

[Blueprint (PDF)](https://pjroos.com/lean-nct/blueprint/nct-blueprint.pdf)

[Dependency graph](https://pjroos.com/lean-nct/dependency_graph/)

### Comparator

You can check this formalization using Comparator, the gold standard for checking whether a formalization is correct. (This requires running a UNIX system.)
* Follow installation instructions here: https://github.com/leanprover/comparator
  * Make sure that both `comparator` and `lean4export` use the same version as specified by [`lean-toolchain`](lean-toolchain).
  * Make sure the programs are in the PATH by running
  `sudo cp .lake/build/bin/comparator /usr/local/bin/` and `sudo cp .lake/build/bin/lean4export /usr/local/bin/` in the respective repositories
* Run
```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory "$(pwd)" -- bash -c 'lake env comparator comparator.json'
```
You will see a message like `Your solution is okay!`, indicating that comparator accepts your solution.