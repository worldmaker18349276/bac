# BAC

This package is for educational purposes, not for practical use, therefore we use the following strategies:

- propositions over efficiency:

    We focus on mathematical propositions we used, in which the forms and meanings of formula should be emphisasized.  So if the correct meaning cannot be shown, duplicates are not eliminated, or more efficient methods are not used.

- validate and contruct separately:

    To show the pre-condition of operations, we validate input arguments then construct the result separately, even though some validations can be done during constructions.  For efficiency, these validations should be checked implicitly before the operation.

- simple types and implicit conditions:

    Validation via the type system is the best practice in modern programming techniques.  However, some property, especially for our use, cannot be encoded into type system, also types that are too detailed interfere with the concept we care about.
    To simplify the formula and hide some unimportant information, we use simple and familiar types, such as `Int`, `List` and `Map`, to encode our concept.  As a consequence, many functions have some hidden conditions, which may fail on invalid conditions, or even silently return an incorrect result.  Haskell is used in this project because it is the most balanced in this sense.

- implementation and categorical algorithm:

    The code to implement operations are very different from the categorical algorithm described on the paper, which is due to the data structure we designed: the tree structure enforces us to write procedure codes, which enlarges the gap between the implementations and categorical algorithm.  Therefore, this package is not conducive to understanding the full details of the algorithm.  To minimize the gap, many comments are added for the categorical perspective.

## How To Build

To build this project, run:

```
cabal configure
cabal build && cabal haddock --haddock-hyperlink-source
```

To test, run:

```
cabal repl --with-ghc=doctest
```

## CLI Editor

Due to the complexity of this data structure, an interactive interface is needed to provide more convenient way to operate on it.

To use, run:

```
cabal run edit -- <bac_filepath> <bank_filepath>
```

Shortcuts:

- `Esc`: cancel, toggle command mode
- `Tab`: search tokens, auto complete
- `Alt-Left/Right`: swing a chain
- `Alt-Enter`: change the slot type (string <-> chain)
- `Alt-d`: duplicate a slot
- `Alt-j`: join chains/strings
- `Alt-i`: find an initial chain
- `Alt-s`: save BAC and bank
- `Alt-S`: save bank as another file
- `Alt-o`: open a bank
- `Alt-O`: append a bank

Operations:

- **Add/Remove/Alter an edge**
- **Remove a morphism/object**: will hint you which edges should be added, and ask you to select a set of equations, so that the chains in the bank can be converted.
- **Add a morphism**: will ask you to select a set of equations, which may still fail.
- **Add a object**
- **Interpolate an object**
- **Split a morphism**: will ask you to partition a set of morphisms which can be splitted.
- **Merge morphisms**: will ask you select a morphism to be merged.
- **Split an object on outgoing/incoming parts**: will ask you to partition a set of outgoing/incoming morphisms which can be splitted.  It will duplicate incoming/outgoing edges, whose tokens will be modified.
- **Merge objects on outgoing/incoming parts**: will ask you select an object to be merged, and select a set of equations to zip incoming/outgoing morphisms.

