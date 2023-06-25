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


## TODO

- [ ]  enhance documentation of BAC
    - [ ]  explain `printBAC`
    - [ ]  add more nontrivial examples; they should touch every cases in the code
- [ ]  interactive Hasse diagram
    - [ ]  html + js, canvas (or svg)
    - [ ]  tooltip, smooth transition, distribution algorithm
    - [ ]  graph edit script:
        - split edge, split node, add node, add edge, remove edge, remove node, merge node, merge edge
    - [ ]  use this to make animated slide: more natural and easy to understand for diagram explanation
