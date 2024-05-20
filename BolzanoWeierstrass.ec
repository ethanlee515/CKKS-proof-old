require import AllCore.
require import RealSeq StdOrder.
import IntOrder.

(* crutch for recursive functions *)
type peano = [ Z | S of peano ].

op peano_to_int p =
with p = Z => 0
with p = S p' => 1 + peano_to_int p'.

op int_to_peano i = iter i S Z.

lemma peano_to_intK p :
  int_to_peano (peano_to_int p) = p.
proof. admitted.

lemma int_to_peanoK i :
  0 <= i =>
  peano_to_int (int_to_peano i) = i.
proof. admitted.

lemma int_to_peano0 :
  int_to_peano 0 = Z.
proof. admitted.

lemma le0_int_to_peano i :
  i <= 0 =>
  int_to_peano i = Z.
proof. smt(iteri0). qed.

(* -- Bolzano-Weierstrass --
 * Every bounded sequence has a convergent subsequence *)

op real_subseq (s1 s2 : int -> real) =
  exists m, forall i,
  s1 i = s2 (m i) /\ i <= m i.

op is_peak (x_ : int -> real) (p : int) = 0 <= p /\ forall m, p < m => x_ m <= x_ p.

op is_peak_after (x_ : int -> real) (p' : int) (p : int) = is_peak x_ p /\ p' < p.

op peaks (x_ : int -> real) (i : peano) =
with i = Z => choiceb (is_peak x_) 0
with i = S i' => choiceb (is_peak_after x_ (peaks x_ i')) 0.

op no_peaks_after x_ (p : int) = 0 <= p /\ forall n, p <= n => !(is_peak x_ n).

op y_ x_ (i : peano) =
with i = Z => choiceb (no_peaks_after x_) 0
with i = S i' => choiceb (fun n => y_ x_ i' < n /\ x_ (y_ x_ i') <= x_ n) 0.

lemma ge0_incrSZ x_ :
  (exists p, no_peaks_after x_ p) =>
  0 <= y_ x_ Z.
proof. smt(choicebP). qed.

lemma ge0_y x_ :
  (exists p, no_peaks_after x_ p) =>
  0 <= y_ x_ (int_to_peano 0).
proof.
move => ?.
rewrite int_to_peano0.
exact ge0_incrSZ.
qed.

lemma ge0_y_le0 x_ i :
  i <= 0 =>
  (exists p, no_peaks_after x_ p) =>
  0 <= y_ x_ (int_to_peano i).
proof.
move => ?.
rewrite le0_int_to_peano //=.
exact ge0_incrSZ.
qed.

lemma y_increasing x_ i :
  (exists p, no_peaks_after x_ p) =>
  y_ x_ (int_to_peano i) <= y_ x_ (int_to_peano (i + 1)).
proof.
admitted.

lemma int_to_peanoS i :
  0 < i =>
  int_to_peano i = S (int_to_peano (i - 1)).
proof. admitted.

lemma y_subseq x_ i :
  (exists p, no_peaks_after x_ p) =>
  i <= y_ x_ (int_to_peano i).
proof.
move => [p [ge0_p H]].
case (0 < i) => ?; last first.
- apply (StdOrder.IntOrder.ler_trans 0).
  + smt().
  by apply ge0_y_le0 => /#.
apply (intind (fun i => i <= y_ x_ (int_to_peano i))); last smt().
- move => //=.
  by apply ge0_y_le0 => /#.
move => //= j ge0_j.
rewrite (int_to_peanoS (j + 1)) /=; first smt().
move => ?.
pose P := (fun (n : int) =>
  y_ x_ (int_to_peano j) < n /\ x_ (y_ x_ (int_to_peano j)) <= x_ n).
suff: exists n, P n.
+ move => ?.
  have [??]: P (choiceb P 0).
  * exact choicebP.
  suff: j < choiceb P 0.
  * admit.
  exact (StdOrder.IntOrder.ler_lt_trans (y_ x_ (int_to_peano j))).
print is_peak.
print no_peaks_after.
admit.
qed.

(*
lemma fi_diverge : !(converge (%r)).
proof.
suff: converge (%r) => false by smt().
move => [y ?].
have [N ?]: exists (N : int), forall n, N <= n => `|n%r - y| < 0.5 by smt().
pose n := max N (ceil y) + 1.
have ?: `|n%r - y| < 1%r / 2%r by smt().
smt().
qed.
*)

lemma diverge_superlinear (f : int -> real) :
  (forall i, i%r <= f i) => !(converge f).
proof.
move => f_superlinear.
suff: converge f => false by smt().
move => [y ?].
have [N ?]: exists (N : int), forall n, N <= n => `|f n - y| < 0.5 by smt().
pose n := max N (ceil y) + 1.
have ?: `|f n - y| < 1%r / 2%r by smt().
smt(ceil_ge).
qed.

lemma subseq_superlinear s' s :
  real_subseq s' s =>
  (forall i, i%r <= s i) =>
  forall i, i%r <= s' i.
proof. smt(). qed.

op finite_peaks x_ = exists p, no_peaks_after x_ p.

op peaks_vals x_ = x_ \o peaks x_ \o int_to_peano.

lemma peaks_decreasing x_ :
  forall (m n : int), m <= n =>
  peaks_vals x_ n <= peaks_vals x_ m.
proof. admitted.

lemma peaks_subseq x_ :
  !(finite_peaks x_) =>
  real_subseq (peaks_vals x_) x_.
proof. admitted.

lemma Bolzano_Weierstrass x_ (a b : real) :
  (forall i, a <= x_ i) =>
  (forall i, x_ i <= b) =>
  (exists x_', real_subseq x_' x_ /\ converge x_').
proof.
move => lb_x ub_x.
case (exists p, no_peaks_after x_ p) => ?.
- exists (x_ \o (y_ x_) \o int_to_peano).
  (* this should be increasing *)
  split.
  + exists (y_ x_ \o int_to_peano).
    rewrite /(\o) /= => i.
    exact y_subseq.

  print cnv_bmono_from.
  print real_subseq.

  admit.
- exists (x_ \o (peaks x_) \o int_to_peano).

  (* this should be decreasing *)
  print cnvtoN.
  admit.
qed.
