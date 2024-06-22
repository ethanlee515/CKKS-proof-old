require import AllCore IntDiv List DList PolyReduce Distr DBool.
require import DiscreteGaussian.
require import Trigonometry.
import Biased.
require ApproxFHE.
require import StdBigop.
import Bigint.BIA.
require import RealExp.
require import Params.
require Subtype.

(* Integer polynomials mod X^n + 1.
 *
 * Hard to use `PolyReduceZq` from the standard library here.
 * Can't do modulus switching with it. *)
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

op dpolyX d = dmap (dpoly n d) pinject.

(* Manual bookkeeping for finite field modulus.
 * This might be annoying since we still need to show that this is a normed space.
 * Might need some funny-looking norm, like adding a large penalty term if modulos don't match.
 * Alternatively, maybe we can just have a pseudonorm? *)
op polymod (p : polyXnD1) m = polyLX (mkseq (fun i => p.[i] %% m) n).

type poly_mod_ql = {
  modded_poly: polyXnD1;
  ql: int }.

abbrev "_.[_]" (m : poly_mod_ql) (i : int) = (modded_poly m).[i].

abbrev ( + ) p1 p2 = {|
  modded_poly = polymod (modded_poly p1 + modded_poly p2) (ql p1);
  ql = ql p1 |}.

abbrev ( * ) p1 p2 = {|
  modded_poly = polymod (modded_poly p1 * modded_poly p2) (ql p1);
  ql = ql p1 |}.

abbrev ( ** ) c p = {|
  modded_poly = c ** modded_poly p;
  ql = ql p |}.

abbrev ([ - ]) p = {|
  modded_poly = - modded_poly p;
  ql = ql p |}.

(* sampling a polynomial by iid sampling its coefficients *)
op dpolyXQ d ql = dmap (dpolyX d) (fun p => {|
  modded_poly = p;
  ql = ql |}).

op mod_ql p ql = {|
  modded_poly = polymod p ql;
  ql = ql |}.

op mod_qL p = mod_ql p qL.
op mod_PqL p = mod_ql p (P * qL).

(* list to poly *)
op polyLQ coeffs ql = mod_ql (polyLX coeffs) ql.

(* CKKS supported operations: arithmetic circuits and "rescaling".
 * For security we don't consider operations that are compositions of these. *)

type unary_operation = [ rescale of int ].
type binary_operation = [ add | mult ].
op dl o = with o = rescale i => i.

(* This is necessarily deterministic.
 * No random rounding here.
 * Otherwise IND-CPA+ is trivially broken. *)
op eval_unary o (m : poly_mod_ql) =
  let d = q ^ (dl o) in
  polyLQ (mkseq (fun i => m.[i] %/ d) n) (ql m %/ d).

op eval_binary o (m1 m2 : poly_mod_ql) =
with o = add => m1 + m2
with o = mult => m1 * m2.

type public_key = poly_mod_ql * poly_mod_ql.
type ciphertext = {
  encryption: poly_mod_ql * poly_mod_ql;
  level: int;
  msg_bound : real;
  noise_bound : real }.

(* The modulus of evaluation key is treated inconsistently.
 * We will just take the integer value. *)
type evaluation_key = polyXnD1 * polyXnD1.

clone import ApproxFHE as CKKS_FHE with
  type pk_t <- public_key,
  type evk_t <- evaluation_key,
  type sk_t <= polyXnD1,
  type msg <= poly_mod_ql,
  type ct_t <= ciphertext,
  type op1 <= unary_operation,
  type op2 <= binary_operation,
  op interp1 <= eval_unary,
  op interp2 <= eval_binary
proof *.

(* misc utility functions *)

op random_round x =
  let ix = floor x in
  let p = x - ix%r in
  dmap (dbiased p) (fun b => if b then ix + 1 else ix).

op random_round_list lst = djoinmap random_round lst.

op divide_and_round (p : polyXnD1) d = dmap
  (random_round_list (mkseq (fun i => p.[i]%r / d%r) n))
  polyLX.

(* hamming weight for "short" vectors *)
op l1_norm (p : polyXnD1) = bigi predT (fun i => `|p.[i]|) 0 n.

op ZO1_pdf x =
  if x = 0 then 0.5 else
  if x = 1 then 0.25 else
  if x = -1 then 0.25 else 0%r.

lemma isdistr_ZO1 : isdistr ZO1_pdf.
proof. by apply (isdistr_finP [-1; 0; 1]) => /#. qed.

op ZO1 = mk ZO1_pdf.
op ZO = dpolyX ZO1.
op ZO_L = dmap ZO mod_qL.
op de = dpolyX (discrete_gaussian sq_sigma).
op de_L = dmap de mod_qL.

(* These might need to be adjusted. *)
op bks = 8%r * sigma * n%r / sqrt 3%r.
op bscale = sqrt (n%r / 3%r) * (3%r + 8%r * sqrt h%r).
op bmult (l : int) = 1%r / P%r * q%r * P%r ^ l * bks + bscale.

module CKKS_without_bootstrap : Scheme = {
  proc keygen() = {
    var pk, evk, sk, a, e, b;
    var a', e', b';
    sk <$ dcond (dpolyX (duniform [-1; 0; 1])) (fun p => l1_norm p = h);
    a <$ dpolyX (drange 0 (qL - 1));
    e <$ de;
    b <- -a * sk + e;
    pk <- (mod_qL b, mod_qL a);
    a' <$ dpolyX (drange 0 (qL * P - 1));
    e' <$ de;
    b' <- -a' * sk + e' + P ** sk * sk;
    evk <- (polymod b' (P * qL), a');
    return (pk, evk, sk);
  }

  proc encrypt(pk: public_key, m) = {
    var nu, e0, e1, b, a;
    nu <$ ZO_L;
    e0 <$ de_L;
    e1 <$ de_L;
    b <- nu * pk.`1 + m + e0;
    a <- nu * pk.`2 + e1;
    return if ql m = qL then Some {|
      encryption = (b, a);
      level = L;
      msg_bound = nu0;
      noise_bound = tail_cutoff * sigma
    |} else None;
  }

  proc dec(sk, c: ciphertext) = {
    var a, b;
    var result;
    (b, a) <- encryption c;
    result <- b + a * mod_ql sk (q * P ^ level c);
    return result;
  }

  proc eval_add(c1: ciphertext, c2: ciphertext) = {
    var a1, b1;
    var a2, b2;
    (b1, a1) <- encryption c1;
    (b2, a2) <- encryption c2;
    return if level c1 = level c2 then Some {|
      encryption = (b1 + b2, a1 + a2);
      level = level c1;
      msg_bound = msg_bound c1 + msg_bound c2;
      noise_bound = noise_bound c1 + noise_bound c2
    |} else None;
  }

  proc eval_mult(evk: evaluation_key, c1: ciphertext, c2: ciphertext) = {
    var a1, b1, nu1, w1;
    var a2, b2, nu2, w2;
    var d0, d1, d2;
    var br, ar, b, a;
    (b1, a1) <- encryption c1;
    (b2, a2) <- encryption c2;
    d0 <- b1 * b2;
    d1 <- a1 * b2 + a2 * b1;
    (* Modeling next step using integer polys.
     * The spec itself isn't clear on which term is modulo what anyways.
     * Results should (hopefully) be consistent anyways? *)
    d2 <- modded_poly (a1 * a2);
    br <$ divide_and_round (d2 * fst evk) P;
    ar <$ divide_and_round (d2 * snd evk) P;
    b <- d0 + mod_ql br 0;
    a <- d1 + mod_ql ar 0;
    nu1 <- msg_bound c1;
    nu2 <- msg_bound c2;
    w1 <- noise_bound c1;
    w2 <- noise_bound c2;
    return if level c1 = level c2 then Some {|
      encryption = (b, a);
      level = level c1;
      msg_bound = nu1 * nu2;
      noise_bound = nu1 * w2 + nu2 * w1 + w1 * w2 + bmult (level c1)
    |} else None;
  }

  proc eval_rescale(c: ciphertext, dl: int) = {
    var b, a;
    var b', a';
    var d, ql;
    var newlevel;
    newlevel <- level c - dl;
    d <- P ^ dl;
    (b, a) <- encryption c;
    b' <$ divide_and_round (modded_poly b) d;
    a' <$ divide_and_round (modded_poly a) d;
    ql <- q * P ^ newlevel;
    return if 0 <= newlevel then Some {|
      encryption = (mod_ql b' ql, mod_ql a' ql);
      level = newlevel;
      msg_bound = msg_bound c / d%r;
      noise_bound = noise_bound c / d%r + bscale
    |} else None;
  }

  proc eval1(evk: evaluation_key, o: unary_operation, c: ciphertext) = {
    var result;
    result <@ eval_rescale(c, dl o);
    return result;
  }

  proc eval2(evk: evaluation_key, o: binary_operation, c1: ciphertext, c2: ciphertext) = {
    var result;
    if(o = add) {
      result <@ eval_add(c1, c2);
    } else {
      result <@ eval_mult(evk, c1, c2);
    }
    return result;
  }
}.

(* TODO CKKS with bootstrapping should use the CKKS functions above. *)
