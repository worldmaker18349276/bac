# BAC

## TODO

- [ ]  improve code
    - [ ]  more precise on manipulation of `Map`
    - [ ]  more precise zip: `class Distribute`
    - [ ]  validate parameters → compute the derived propositions → construct data structure
    - [ ]  more comments, even not necessary; math sense is different from code sense
- [ ]  enhance documentation of BAC
    - [ ]  explain `printBAC`
    - [ ]  add comment to explain how algorithm works
    - [ ]  add more nontrivial examples; they should touch every cases in the code
- [ ]  explain implementation strategy
    - [ ]  explain difference between implementation approach and categorical approach
    - [ ]  validate and contruct separately for educational purposes
    - [ ]  less Maybe (which should only work for validation), more partial function (known complex condition is hard to encode into type system)
    - [ ]  propositions over efficiency (less reuse, more duplication)
    - [ ]  current problem: lack of test case, considered as unreliable
    - [ ]  add documentation: “this package is for/is not for”
- [ ]  interactive Hasse diagram
    - [ ]  html + js, canvas (or svg)
    - [ ]  tooltip, smooth transition, distribution algorithm
    - [ ]  graph edit script:
        - split edge, split node, add node, add edge, remove edge, remove node, merge node, merge edge
    - [ ]  use this to make animated slide: more natural and easy to understand for diagram explanation
