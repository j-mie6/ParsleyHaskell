# Parsley Tests and Benchmarks
The tests and benchmarks are kept separate from Parsley itself, since they have a dependency on
the lift (and idioms) plugins, which themselves will soon have a dependency on `parsley` (to avoid
needing the `Garnish` module inside the codebase here!)

Additionally, it keeps the `dump-core` flag out of the main library, where it would otherwise be
distracting!