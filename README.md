# ex-infinity
Verification of equations in a proof of the existence of a model structure on the category of simplicial sets

The paper can be found here:
http://arxiv.org/abs/1506.04887

## jrdefs.v
This contains the definitions of the maps from the paper. I make use of the fact that the maps can be defined without reference to $n$, so I eliminate one of the parameters and model each family of maps as having type $P \mathbb N \to P \mathbb N$. However, since each map preserves binary joins, I actually model each map as a relation $\mathbb N \to \mathbb N$.

## sflib.v
The useful 'Case' tactic. Makes proofs easier to read, but not really part of the verification.

## jreqns.v
Contains the proofs of the ten equations from the paper.  Requires the two files above.

## jrtests.v
Some simple tests of the definitions.
