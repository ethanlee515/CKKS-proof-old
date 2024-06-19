require import AllCore CKKS RLWE.
import CKKS_FHE.
import PolyReduceZq.

section MainTheorem.

declare module A <: INDCPA_Adversary.

module Reduce(A : INDCPA_Adversary) : RLWE.Adversary = {
  proc distinguish(inst : polyXnD1 * polyXnD1) = {
    return true;
  }
}.

lemma test &m :
  Pr[CKKS_FHE.INDCPA_Game(CKKS_no_bootstrap, A).main() @ &m : res] <
  Pr[RLWE.Game(Reduce(A)).main(witness) @ &m : res].
proof. admitted.

end section MainTheorem.
