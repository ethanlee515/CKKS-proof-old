require import AllCore CKKS_Spec RLWE.
import CKKS_FHE.
import PolyReduceZq.

section MainTheorem.

declare module A <: INDCPA_Adversary.

module Reduce(A : INDCPA_Adversary) : RLWE.Adversary = {
  proc distinguish(inst : polyXnD1 * polyXnD1) = {
    return true;
  }
}.

op max_queries : int.
(* secret distribution.
 * some kinda short polynomials. *)
op ds : polyXnD1 distr.

lemma test &m :
  Pr[CKKS_FHE.INDCPA_Game(CKKS_without_bootstrap, A).main(max_queries) @ &m : res] <
  Pr[RLWE.Game(Reduce(A)).main(ds) @ &m : res].
proof. admitted.

end section MainTheorem.
