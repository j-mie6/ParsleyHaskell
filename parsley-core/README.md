# Parsley Internals

This package contains the internals for the [`parsley`](https://hackage.haskell.org/package/parsley-core) library. 

The version policy adheres to the regular Haskell PVP, but the two major versions are distinguished: 
the first is the _Public API_ major version, which represents backwards incompatible changes
in the regular PVP sense that effect the `parsley` package itself and its users; the second version is the
_Internal API_ major version, which would only effect users who use part of the internal parsley
modules. As such, for people that are **not** explicitly importing anything from `Parsley.Internal`, or
its submodules, the second major version does not matter: `0.2.0.0` and `0.3.0.0` would be compatible,
for instance.