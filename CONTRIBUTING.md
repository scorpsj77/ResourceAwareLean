# Contributing

This is a student research project on resource-aware textbook algorithms in
Lean 4. Issues and pull requests are welcome, with the caveat that the
maintainers are students and review may be slow.

## Building

```sh
lake --wfail build ResourceAware TextbookAlgorithms ThirdParty Examples
```

The toolchain is pinned in `lean-toolchain` and the Mathlib and CSLib
revisions are pinned in `lakefile.toml`; `lake build` will fetch them.

## Ground rules

- No `sorry`, `admit`, or custom `axiom` in contributed code.
- New Lean files carry the standard copyright/authorship header.
- Code in `ThirdParty/` is vendored third-party work and should not be
  modified here; changes belong upstream.
