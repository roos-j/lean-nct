# Formalization of norm-variation of multiple ergodic averages for commuting transformations

[API documentation](https://pjroos.com/lean-nct/docs/)

[Blueprint (PDF)](https://pjroos.com/lean-nct/blueprint/nct-blueprint.pdf)

[Dependency graph](https://pjroos.com/lean-nct/dependency_graph/)

### Comparator

You can check this formalization using Comparator, the gold standard for checking whether a formalization is correct. (This requires running a UNIX system, including WSL.)

For this you need to clone and build 3 repositories first (anywhere you'd like)

* Clone and build [`landrun`](https://github.com/Zouuup/landrun) using
```
git clone https://github.com/zouuup/landrun.git
cd landrun
go build -o landrun cmd/landrun/main.go
sudo cp landrun /usr/local/bin/
```
* Clone and build [`lean4export`](https://github.com/leanprover/lean4export/). The version of `lean4export` and `comparator` have to match the contents of `lean-toolchain` in this project.
```
git clone https://github.com/leanprover/lean4export.git
cd lean4export
git checkout v4.33.0-rc2
lake build
sudo cp .lake/build/bin/lean4export /usr/local/bin/
```
* Clone and build [`comparator`](https://github.com/leanprover/comparator)
```
git clone https://github.com/leanprover/comparator.git
cd comparator
git checkout v4.33.0-rc2
lake build
sudo cp .lake/build/bin/comparator /usr/local/bin/
```
* To actually run comparator, run (in the `lean-nct` directory)
```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory "$(pwd)" -- bash -c 'lake env comparator comparator.json'
```
You will see a message like `Your solution is okay!`, indicating that comparator accepts your solution.