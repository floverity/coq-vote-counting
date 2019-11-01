Electronic vote counting as mathematical proof
------

This is the Coq code associated with my Honours thesis "Electronic vote counting as mathematical proof" (2016), supervised by [Dirk Pattinson](http://users.cecs.anu.edu.au/~dpattinson/index.html). It now also accompanies two papers. The code was written using version 8.4pl6 of [The Coq Proof Assistant](https://coq.inria.fr/coq-84).

Chapter 3
------
Contains the code for chapter 3 of the thesis, "The Majority Criterion", and the paper "Formally verified invariants of vote counting schemes". 

There is one file: 
   - 'STV_majority_criterion.v' - the Coq implementation of Simple STV (author Dirk Pattinson) described in section 3.1.2, also containing the proof of the invariant (at line 1449) and the majority criterion (at line 1629) described in section 3.2.2.

Chapter 4
------
Contains the code for chapter 4 of the thesis, "Generic Termination", and the paper "Modular synthesis of provable correct vote counting programs". 

There are five files:
  - `FPTP_generic.v' - the Coq implementation of first past the post (FPTP) in the generic framework, as described in section 4.2; 
  - `FPTPCode.hs' - the automatically extracted Haskell code from the implementation of FPTP in the generic framework;
  - `FPTPCount.hs' - the wrapper for FPTPCode.hs;
  - `STV_generic.v' - the Coq implementation of simple single transferrable vote (STV) in the generic framework, as described in section 4.3; and
  - `Union_generic.v' - the Coq implementation of the Union protocol in the generic framework, as described in section 4.4.2.
 
