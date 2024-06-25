
## Implementation


- [x] `Error.hs`
- [ ] `Explorer.hs`
- [ ] `HornSolver.hs`
- [ ] `HtmlOutput.hs`
- [x] `Logic.hs`
- [x] `Parser.hs`
- [x] `Pretty.hs`
- [x] `Program.hs`
- [x] `Resolver.hs`
- [ ] `SolverMonad.hs`
- [ ] `Synthesizer.hs`
- [x] `Tokens.hs`
- [x] `Type.hs`
- [ ] `TypeChecker.hs`
- [ ] `TypeConstraintSolver.hs`
- [x] `Util.hs`
- [x] `Z3.hs`

## Research

- [ ] Fixpoint solvers
- [ ] `de_brujns` <https://en.wikipedia.org/wiki/De_Bruijn_sequence>

## Correctness

- [ ] Go over all `instance`s in the Haskell code.
- [ ] Go over all uses of `head` and `tail` in the Haskell code.
- [ ] Set up unit tests for better understanding and correctness.

## Misc

- [x] Create proper wrapper types for enum variants and type aliases.
- [x] Replace all `.0` with `Deref` and `DerefMut` or equivalent.
- [x] Replace all `impl Debug`/`{:?}` with `impl Display`/`{}`?
- [ ] Replace all `Binary(..)` with the corresponding methods?
- [ ] Move all top-level functions into `impl` blocks.
- [ ] Proper naming (omg)
  - [ ] No more single-letter variables.
  - [ ] Rename all `let mut {vec,set,map}`.
- [ ] Syntax highlighting and formatting done after.
- [ ] Change all `.into` into `From::from`?

## Future work

- [ ] `TypeSkeleton::Gen(..)`
- [ ] `BareProgram::Pure(..)`
- [ ] `BareProgram::Bind(..)`
- [ ] Rejection sampling
  - [ ] Good for data types like red-black trees
  - [ ] Bad for large amounts of samples


## Optimizations

- [ ] Make sure `Forumla` is immutable, and cache all expensive functions.
- [ ] Check if safe to rewrite all `Vec<Id>` to `HashSet<Id>` (and maybe others).
- [ ] Reduce the use of `.clone()`.
  - [ ] But still prioritize shallow cloning over deep cloning.
  - [ ] `Cow` and `Rc` are last resorts.
- [ ] Try to reduce the size of integer values.
- [ ] Turn all immutable `String` into `Box<str>`.
- [ ] Convert `fn x(self, ..) -> Self` to `fn x(&mut self, ..) -> Self`.
  - [ ] Also look for `self.clone()`
