require import AllCore RealFLub RealLub RealSeq.
require import StdOrder.
import RealOrder.

(* TODO some belongs in RealLub instead of RealFlub *)

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

lemma ler_sum_lub (E1 E2 E3 : real -> bool) :
  nonempty E1 => has_lub E2 => has_lub E3 =>
  (forall x1 x2, E1 x1 => E2 x2 => exists x3, E3 x3 /\ x1 + x2 <= x3) =>
  lub E1 + lub E2 <= lub E3.
proof.
move => ?? lub2 lub3.
have lub1: has_lub E1.
- split; first smt().
  exists (lub E3 - lub E2).
  move => x1 E1x1.
  suff: forall eps, 0%r < eps => x1 + (lub E2 - eps) <= lub E3.
  + move => ?.
    pose eps' := (lub E3 - lub E2 - x1) / 2%r.
    have ?: x1 + (lub E2 - eps') <= lub E3 by smt().
    smt().
  move => eps gt0_eps.
  have [x2 ?] : exists x2, E2 x2 /\ lub E2 - eps < x2.
  + exact lub_adherent.
  smt(lub_upper_bound).
suff: forall eps, 0%r < eps => (lub E1 - eps) + (lub E2 - eps) <= lub E3.
- move => ?.
  pose eps' := (lub E1 + lub E2 - lub E3) / 4%r.
  have ?: lub E1 - eps' + (lub E2 - eps') <= lub E3 by smt().
  smt().
move => eps gt0_eps.
have [x1 ?]: exists x1, E1 x1 /\ lub E1 - eps < x1.
- exact lub_adherent.
have [x2 ?]: exists x2, E2 x2 /\ lub E2 - eps < x2.
- exact lub_adherent.
apply (ler_trans (x1 + x2)); first smt().
have [x3 ?] : exists x3, E3 x3 /\ x1 + x2 <= x3 by smt().
smt(lub_upper_bound).
qed.

(* flub in a closed interval *)

op flub_in (f : real -> real) (x0 x1 : real) = flub (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0).

op has_fub_in (f : real -> real) (x0 x1 : real) = has_fub (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0).

lemma has_fub_in_subset (f : real -> real) (x0 x0' x1 x1' : real) :
  x0 <= x0' =>
  x1' <= x1 =>
  has_fub_in f x0 x1 =>
  has_fub_in f x0' x1'.
proof. smt(). qed.

lemma ler_flub_in f g (x0 x1 : real) :
  x0 <= x1 =>
  has_fub_in g x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f x <= g x) =>
  flub_in f x0 x1 <= flub_in g x0 x1.
proof.
move => le_x0_x1 has_fub_g le_f_g.
apply ler_flub => /#.
qed.

op is_fub_in f (x0 x1 r : real) = is_fub (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0) r.

lemma flub_in_le_ub f x0 x1 r :
  is_fub_in f x0 x1 r => flub_in f x0 x1 <= r.
proof. smt(flub_le_ub). qed.

lemma flub_in_upper_bound f (x0 x1 x : real) :
  x0 <= x =>
  x <= x1 =>
  has_fub_in f x0 x1 =>
  f x <= flub_in f x0 x1.
proof. smt(flub_upper_bound). qed.

lemma flub_in_subset f (x0 x1 x0' x1' : real) :
  x0 <= x0' =>
  x0' <= x1' =>
  x1' <= x1 =>
  has_fub_in f x0 x1 =>
  flub_in f x0' x1' <= flub_in f x0 x1.
proof.
move => ???.
rewrite /has_flb_in /flub_in /(\o) /has_fub_in /flub /has_fub /is_fub /=.
move => [r?].
apply ler_lub => /#.
qed.

(* greatest lower bound *)

op glb (xs : real -> bool) = - (lub (xs \o Real.([ - ]))).

op is_flb (f : 'a -> real) (r : real) = forall x, r <= f x.

op is_flb_in (f : real -> real) (x0 x1 r : real) =
  is_flb (fun x => if x0 <= x /\ x <= x1 then f x else f x0) r.

lemma is_flb_in_negate f x0 x1 r :
  is_flb_in f x0 x1 r <=> is_fub_in (Real.([-]) \o f) x0 x1 (-r).
proof. smt(). qed.

op has_flb (f : 'a -> real) = exists r, is_flb f r.

lemma has_flb_negate (f : 'a -> real) :
  has_fub (Real.([ - ]) \o f) <=> has_flb f.
proof.
split => [[r H] | [r H]].
- exists (-r); smt().
- exists (-r); smt().
qed.

op fglb (f: 'a -> real) = glb (fun r => exists a, f a = r).

lemma fglb_negate (f : real -> real) :
  fglb f = - flub (Real.([ - ]) \o f).
proof.
rewrite /fglb /flub /glb /=.
congr; congr; smt(fun_ext).
qed.

op has_flb_in (f : real -> real) (x0 x1 : real) = has_flb (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0).

lemma has_flb_in_negate (f : real -> real) (x0 x1 : real) :
  has_flb_in f x0 x1 <=> has_fub_in (Real.([ - ]) \o f) x0 x1.
proof. smt(has_flb_negate). qed.

lemma has_flb_in_subset (f : real -> real) (x0 x0' x1 x1' : real) :
  x0 <= x0' =>
  x1' <= x1 =>
  has_flb_in f x0 x1 =>
  has_flb_in f x0' x1'.
proof. smt(). qed.

op fglb_in (f : real -> real) (x0 x1 : real) = fglb (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0).

lemma fglb_in_negate f x0 x1 :
  has_flb_in f x0 x1 =>
  fglb_in f x0 x1 = - (flub_in (Real.([ - ]) \o f) x0 x1).
proof.
move => [r ?].
rewrite /fglb_in /flub_in.
rewrite fglb_negate.
congr; congr; smt(fun_ext).
qed.

lemma ler_has_flb (f g : real -> real) (x0 x1 : real) :
  (forall x, x0 <= x => x <= x1 => f x <= g x) =>
  has_flb_in f x0 x1 =>
  has_flb_in g x0 x1.
proof.
case (x0 > x1) => [/# | ?].
rewrite !has_flb_in_negate => le_f_g.
rewrite /has_fub_in.
apply ler_has_fub => /#.
qed.

lemma ler_fglb_in f g (x0 x1 : real) :
  x0 <= x1 =>
  has_flb_in f x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f x <= g x) =>
  fglb_in f x0 x1 <= fglb_in g x0 x1.
proof.
move => ???.
rewrite !fglb_in_negate //=.
- exact (ler_has_flb f).
smt(has_flb_in_negate ler_flub_in).
qed.

lemma fglb_in_lower_bound f (x0 x1 x : real) :
  x0 <= x =>
  x <= x1 =>
  has_flb_in f x0 x1 =>
  fglb_in f x0 x1 <= f x.
proof.
move => ???.
rewrite fglb_in_negate //.
pose g := Real.([-]) \o f.
suff: g x <= flub_in g x0 x1 by smt().
apply flub_in_upper_bound => //=.
by rewrite -has_flb_in_negate.
qed.

lemma fglb_in_subset f (x0 x1 x0' x1' : real) :
  x0 <= x0' =>
  x0' <= x1' =>
  x1' <= x1 =>
  has_flb_in f x0 x1 =>
  fglb_in f x0 x1 <= fglb_in f x0' x1'.
proof.
move => ????.
rewrite !fglb_in_negate //.
- smt(has_flb_in_subset).
have H: forall (a b : real), a <= b => -b <= -a by smt().
apply H; clear H.
apply flub_in_subset => //=.
by rewrite -has_flb_in_negate.
qed.

lemma fglb_in_ge_lb f x0 x1 r :
  is_flb_in f x0 x1 r =>
  r <= fglb_in f x0 x1.
proof.
move => ?.
rewrite fglb_in_negate; first by exists r.
have H: forall (a b : real), a <= -b => b <= -a by smt().
apply H; clear H.
apply flub_in_le_ub.
by rewrite -is_flb_in_negate.
qed.

lemma flgb_in_const x0 x1 c :
  fglb_in (fun (_: real) => c) x0 x1 = c.
proof.
rewrite fglb_in_negate.
- exists c => /#.
rewrite /(\o) /flub_in /=.
by rewrite flub_const.
qed.
