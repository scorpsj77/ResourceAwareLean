# ThirdParty

Code in this directory is **not authored by this project**.

## `Graph.lean`

A local copy of the graph API proposed in
[CSLib PR #503](https://github.com/leanprover/cslib/pull/503).

Authors (as recorded in the file header): Basil Rohner,
Sorrachai Yingchareonthawornchai, Weixuan Yuan.

The copy is kept here, unmodified, until that pull request merges upstream,
at which point this directory's copy should be removed and
`ResourceAware/Foundations/Graph/GraphAdapters.lean` re-pointed at the
upstream module. Resource-aware algorithms should depend on
`ResourceAware.Foundations.Graph.Interface` rather than on this file
directly.
