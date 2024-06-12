require import AllCore IntDiv List DList PolyReduce Distr DBool.
require import DiscreteGaussian.
require import Trigonometry.
import Biased.
require PKE_FHE.
require import StdBigop.
import Bigint.BIA.
require import RealExp.

(* poly degree *)
op n : {int | 0 < n} as gt0_n.
(* modulus *)
op q : {int | 0 < q} as gt0_q.
(* rescaling factor *)
op P : {int | 0 < P} as gt0_P.
(* max times for rescaling *)
op L : {int | 0 < L} as gt0_L.
(* stdev for discrete Gaussian *)
op sigma : { real | 0%r < sigma} as gt0_sigma.
(* hamming weight of secret key *)
op h : {int | 0 < h} as gt0_h.
(* upper bound of message *)
op nu0 : {real | 0%r < nu0} as gt0_nu0.
(* Gaussian tail cutoff *)
op tail_cutoff : { real | 0%r < tail_cutoff } as gt0_tail_cutoff.

op qL = q * P ^ L.
op sq_sigma = sigma * sigma.

(* Hard to use PolyReduceZq here.
 * Can't do modulus switch with it. *)
clone import PolyReduce as Cyclotomic with
  op n <- n,
  type BasePoly.coeff <- int,
  op BasePoly.Coeff.( + ) <- Int.( + ),
  op BasePoly.Coeff.( * ) <- Int.( * ),
  op BasePoly.Coeff.([ - ]) <- Int.([ - ]),
  op BasePoly.Coeff.zeror <- 0,
  op BasePoly.Coeff.oner <- 1,
  pred BasePoly.Coeff.unit <- mem [1; -1],
  op BasePoly.Coeff.invr <- idfun
  remove abbrev BasePoly.Coeff.( - )
  remove abbrev BasePoly.Coeff.( / )
proof * by smt(gt0_n).

import BasePoly.

type unary_operation = [ rescale of int ].
type binary_operation = [ add | mult ].
(* can't do this imperatively later *)
op dl o = with o = rescale i => i.

op eval_unary o (m : polyXnD1) = 
  polyLX (mkseq (fun i => m.[i] %/ q ^ (dl o)) n).

op eval_binary o (m1 m2 : polyXnD1) =
with o = add => m1 + m2
with o = mult => m1 * m2.

type public_key = polyXnD1 * polyXnD1.
(* beta, alpha, l, p, B) = vector, level, message bound, noise bound *)
type valid_ciphertext = polyXnD1 * polyXnD1 * int * real * real.
type ciphertext = valid_ciphertext option.
type evaluation_key = polyXnD1 * polyXnD1.

clone import PKE_FHE as CKKS_FHE with
  type public_key <- public_key,
  type evaluation_key <- evaluation_key,
  type secret_key <= polyXnD1,
  type plaintext <= polyXnD1,
  type ciphertext <= ciphertext,
  type unary_operation <= unary_operation,
  type binary_operation <= binary_operation,
  op evaluate_unary <= eval_unary,
  op evaluate_binary <= eval_binary
proof *.

(* misc utility functions *)

op dpolyX d = dmap (dpoly n d) pinject.
op polyXmap (p : polyXnD1) f = polyLX (mkseq (fun i => f p.[i]) n).
op polymod p m = polyXmap p (fun c => c %% m).

op random_round x =
  let ix = floor x in
  let p = x - ix%r in
  dmap (dbiased p) (fun b => if b then ix + 1 else ix).

op l1_norm (p : polyXnD1) = bigi predT (fun i => `|p.[i]|) 0 n.

op ZO1_pdf x =
  if x = 0 then 0.5 else
  if x = 1 then 0.25 else
  if x = -1 then 0.25 else 0%r.

lemma isdistr_ZO1 : isdistr ZO1_pdf.
proof. by apply (isdistr_finP [-1; 0; 1]) => /#. qed.

op ZO1 = mk ZO1_pdf.
op ZO = dpolyX ZO1.
op de = dpolyX (discrete_gaussian sq_sigma).

op bks = 8%r * sigma * n%r / sqrt 3%r.
op bscale = sqrt (n%r / 3%r) * (3%r + 8%r * sqrt h%r).
op bmult (l : int) = 1%r / P%r * q%r * P%r ^ l * bks + bscale.

module CKKS_no_bootstrap : Scheme = {
  proc keygen() = {
    var pk, evk, sk, a, e, b;
    var a', e', b';
    sk <$ dcond (dpolyX (duniform [-1; 0; 1])) (fun p => l1_norm p = h);
    a <$ dpolyX (drange 0 (qL - 1));
    e <$ de;
    b <- polymod (-a * sk + e) qL;
    pk <- (b, a);
    a' <$ dpolyX (drange 0 (qL * P - 1));
    e' <$ de;
    b' <- polymod (-a' * sk + e' + P ** sk * sk) (P * qL);
    evk <- (b', a');
    return (pk, evk, sk);
  }

  proc encrypt(pk: public_key, m) = {
    var nu, e0, e1, b, a;
    nu <$ ZO;
    e0 <$ de;
    e1 <$ de;
    b <- polymod (nu * pk.`1 + m + e0) qL;
    a <- polymod (nu * pk.`2 + e1) qL;
    return Some (b, a, L, nu0, tail_cutoff * sigma);
  }

  proc decrypt(sk, c: ciphertext) = {
    var a, b, l, nu, w;
    var e;
    var result;
    if(c = None) {
      result <- zeroXnD1;
    } else {
      (b, a, l, nu, w) <- oget c;
      (* added noise for IND-CPA+ *)
      e <$ dpolyX (discrete_gaussian (sq_sigma * w * w));
      result <- polymod (b + a * sk + e) (q * P ^ l);
    }
    return result;
  }

  proc eval_add(c1: ciphertext, c2: ciphertext) = {
    var a1, b1, l1, nu1, w1;
    var a2, b2, l2, nu2, w2;
    (b1, a1, l1, nu1, w1) <- oget c1;
    (b2, a2, l2, nu2, w2) <- oget c2;
    return if l1 = l2 then Some (b1 + b2, a1 + a2, l1, nu1 + nu2, w1 + w2) else None;
  }

  proc eval_mult(evk: evaluation_key, c1: ciphertext, c2: ciphertext) = {
    var a1, b1, l1, nu1, w1;
    var a2, b2, l2, nu2, w2;
    var d0, d1, d2;
    var br, ar, b, a;
    (b1, a1, l1, nu1, w1) <- oget c1;
    (b2, a2, l2, nu2, w2) <- oget c2;
    d0 <- b1 * b2;
    d1 <- a1 * b2 + a2 * b1;
    d2 <- a1 * a2;
    br <$ djoinmap random_round (mkseq (fun i => (d2 * fst evk).[i]%r / P%r) n);
    ar <$ djoinmap random_round (mkseq (fun i => (d2 * snd evk).[i]%r / P%r) n);
    b <- polymod (d0 + polyLX br) (q * P ^ l1);
    a <- polymod (d1 + polyLX ar) (q * P ^ l1);
    return if l1 = l2 then
      Some (b, a, l1, nu1 * nu2, nu1 * w2 + nu2 * w1 + w1 * w2 + bmult l1)
      else None;
    }

  proc evaluate1(evk: evaluation_key, o: unary_operation, c: ciphertext) = {
    var b, a, l, nu, w;
    var b', a', nu', w';
    (b, a, l, nu, w) <- oget c;
    (* rescaling *)
    b' <$ djoinmap random_round (mkseq (fun i => b.[i]%r / (q ^ dl o)%r) n);
    a' <$ djoinmap random_round (mkseq (fun i => a.[i]%r / (q ^ dl o)%r) n);
    nu' <- nu / (q ^ dl o)%r;
    w' <- w / (q ^ dl o)%r + bscale;
    return Some (polyLX b', polyLX a', l - dl o, nu', w');
  }

  proc evaluate2(evk: evaluation_key, o: binary_operation, c1: ciphertext, c2: ciphertext) = {
    var result;
    if(o = add) {
      result <@ eval_add(c1, c2);
    } else {
      result <@ eval_mult(evk, c1, c2);
    }
    return result;
  }
}.
