# Order Revealing Encryption

A simple implementation of the extended CLWW ORE scheme from the
paper [**Order-Revealing Encryption: New Constructions, Applications, and Lower Bounds**](./BlockORE.pdf),
available at https://www.cs.utexas.edu/~dwu4/papers/BlockORE.pdf (which builds on the CLWW ORE
from [**Practical Order-Revealing Encryption with Limited Leakage**](./PracticalORE.pdf)
available at https://www.cs.utexas.edu/~dwu4/papers/PracticalORE.pdf)

## Implementation Progress

* [x] implement the small domain block ore described in section 3
* [x] implement the extended domain ore described in section 4
* [x] range queries
    * [ ] support inclusive/exclusive endpoints for range
* [x] prefix queries
* [x] get_next query to support levenshtein matching via client-side automaton
    * theoretically possible to left-encrypt and transmit the automaton to be executed server side
* [x] mock for ground truth
* [ ] testing for correctness
* [ ] benchmarking
* [ ] optimization
* [ ] related work

## TODO: read these

* [**What Else is Revealed by Order-Revealing Encryption?**](https://eprint.iacr.org/2016/786.pdf)
* [**EncodeORE: Reducing Leakage and Preserving Practicality in Order-Revealing Encryption**](./EncodeORE.pdf)
  available at http://homepages.cs.ncl.ac.uk/changyu.dong/papers/TDSC_20.pdf