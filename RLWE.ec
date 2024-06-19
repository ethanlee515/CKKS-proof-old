require import AllCore Distr DBool PolyReduce.
require import DiscreteGaussian.
require import Params.

clone import PolyReduceZp as PolyReduceZq with
  op n <- n,
  op p <- q
proof * by smt(gt0_n ge2_q).
import Zp.

module type Adversary = {
  proc distinguish(inst: polyXnD1 * polyXnD1) : bool
}.

module Game(A: Adversary) = {
  proc genRLWE(ds) = {
    var a, s, e, b;
    a <$ dpolyXnD1;
    s <$ ds;
    e <$ dpolyX (dmap (discrete_gaussian sigma) inzmod);
    b <- a * s + e;
    return (b, a);
  }

  proc genUniform() = {
    var a, b;
    a <$ dpolyXnD1;
    b <$ dpolyXnD1;
    return (b, a);
  }

  proc main(ds) = {
    var b, b', inst;
    b <$ {0,1};
    if(b) {
      inst <@ genRLWE(ds);
    } else {
      inst <@ genUniform();
    }
    b' <@ A.distinguish(inst);
    return (b = b');
  }
}.
