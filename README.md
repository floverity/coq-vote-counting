README
------

Please find two folders:

1) 'Chapter 3' contains the code for chapter 3, The Majority Criterion. There is one file: 
     - 'STV_majority_criterion.v' - the Coq implementation of Simple STV described in section 3.1.2, also containing the proof of the invariant (at line 1449) and the majority criterion (at line 1629) described in section 3.2.2.

2) 'Chapter 4' contains the code for chapter 4, Generic Termination. There are five files:
  * `FPTP_generic.v' - the Coq implementation of FPTP in the generic framework, as described in section 4.2; 
  * `FPTPCode.hs' - the automatically extracted Haskell code from the implementation of FPTP in the generic framework;
  * `FPTPCount.hs' - the wrapper for FPTPCode.hs;
  * `STV_generic.v' - the Coq implementation of Simple STV in the generic framework, as described in section 4.3;
  * `Union_generic.v' - the Coq implementation of the Union protocol in the generic framework, as described in section 4.4.2;
 
The Coq code was written using version 8.4pl6 of The Coq Proof Assistant, bundled with the integrated development environment CoqIDE.
More information at https://coq.inria.fr/coq-84

Using CoqIDE:
Coq is an *interactive* theorem prover, and so the code is intended to be stepped through line by line. To do this, use the green up and down arrows at the top of the window, or place the cursor at the line of text you wish to move to and press the button with a green arrow and a yellow circle. Goals appear on the right-hand side in the upper box.
