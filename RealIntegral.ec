require import AllCore Real List StdBigop.
import RField.
import Bigreal Bigreal.BRA.
require import StdOrder.
import RealOrder.
require import RealLub RealFLub RealSeq.
require import BolzanoWeierstrass.

(* -- misc library extensions -- *)

lemma mem_last (w : 'a) xs :
  xs <> [] <=> last w xs \in xs.
proof.
rewrite -nth_last.
smt(mem_nth size_ge0).
qed.

lemma mem_head (w : 'a) xs :
  xs <> [] <=> head w xs \in xs.
proof. smt(). qed.

lemma mask_sorted (e : 'a -> 'a -> bool) m xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  size m = size xs =>
  sorted e xs =>
  sorted e (mask m xs).
proof.
move => ??.
apply subseq_sorted => //.
apply subseqP.
by exists m.
qed.

lemma sorted_take (e : 'a -> 'a -> bool) xs n :
  sorted e xs =>
  sorted e (take n xs).
proof. move: n; elim xs; smt(). qed.

lemma sorted_drop (e : 'a -> 'a -> bool) xs n :
  sorted e xs =>
  sorted e (drop n xs).
proof. move: n; elim xs; smt(). qed.

lemma sorted_from_nth (dfl : 'a) e xs :
  (forall i, 0 <= i => i < size xs - 1 => e (nth dfl xs i) (nth dfl xs (i + 1))) =>
  sorted e xs.
proof.
elim xs => //.
move => x_head x_tail sorted_xs.
move => ? /=.
suff: sorted e x_tail.
- case (x_tail = []) => [//=| H ?].
  apply (head_behead _ dfl) in H.
  rewrite -H /path /=.
  smt(size_ge0).
apply sorted_xs => i ge0_i ub_i.
smt(size_ge0).
qed.

lemma sorted_upper_bounded e dfl ub x xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  sorted e xs =>
  x \in xs =>
  e (last dfl xs) ub =>
  e x ub.
proof. by move: x; elim xs; smt(). qed.

lemma sorted_lower_bounded e dfl lb x xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  sorted e xs =>
  x \in xs =>
  e lb (head dfl xs) =>
  e lb x.
proof. by move: x; elim xs; smt(). qed.

lemma cat_take_drop_pick (dfl : 'a) n s :
  0 <= n =>
  n < size s =>
  take n s ++ [nth dfl s n] ++ drop (n + 1) s = s.
proof. smt(cat_take_drop catA drop_nth). qed.

lemma mem_mask_range m (a b i : int) :
  a <= i =>
  i < b =>
  size m = (b - a) =>
  i \in mask m (range a b) <=>
  nth false m (i - a).
proof.
move => ???.
have ->: range a b = range a i ++ [i] ++ range (i + 1) b.
- smt(range_cat size_range rangeS).
rewrite -{1}(cat_take_drop_pick false (i - a) m); 1,2: smt().
rewrite !mask_cat; 1,2: smt(size_take size_cat size_range).
rewrite !mem_cat; smt(mem_mask mem_range).
qed.

lemma sorted_from_cons (e : 'a -> 'a -> bool) x xs :
  sorted e (x :: xs) =>
  sorted e xs.
proof. by elim xs => /#. qed.

lemma mem_subseq1 (x : 'a) xs :
  x \in xs =>
  subseq [x] xs.
proof.
rewrite (nthP witness).
move => [i [rg_i H]].
apply subseqP.
exists (nseq i false ++ [true] ++ nseq (size xs - i - 1) false).
split; first smt(size_nseq size_cat).
rewrite -{2}(cat_take_drop_pick witness i xs); 1,2:smt().
rewrite !mask_cat; 1,2: smt(size_nseq size_cat size_take).
rewrite !mask_false /#.
qed.

lemma subseq_range xs a b :
  sorted Int.(<) xs =>
  a <= head 0 xs =>
  last 0 xs < b =>
  subseq xs (range a b).
proof.
elim xs.
move => ???.
- apply subseqP.
  exists (nseq (b - a) false).
  smt(size_nseq size_range mask_false).
move => x xs iH'.
move => ???.
case (xs = []) => ?.
- subst => /=.
  apply mem_subseq1.
  smt(mem_range).
have iH {iH'}: subseq xs (range a b).
- by apply iH'; smt(sorted_from_cons head_behead).
rewrite -subseqP in iH.
case iH => m [? is_mask_xs].
pose hx := head 0 xs.
have ?: hx < b.
- by apply (sorted_upper_bounded Int.(<) 0 b hx (x :: xs)) => /#.
rewrite (range_cat hx); 1, 2: smt().
apply subseqP.
exists (nseq (x - a) false ++ [true] ++ nseq (hx - x - 1) false ++ drop (hx - a) m).
split; first smt(size_cat size_nseq size_range size_drop).
rewrite mask_cat; first smt(size_cat size_nseq size_range size_drop).
rewrite -cat1s; congr.
- have ->: range a hx = range a x ++ range x (x + 1) ++ range (x + 1) hx.
  + smt(range_cat).
  rewrite !mask_cat; 1,2: smt(size_nseq size_cat size_range).
  rewrite !mask_false cat0s cats0.
  by rewrite rangeS.
rewrite is_mask_xs.
have {1} ->: m = (take (hx - a) m ++ drop (hx - a) m).
- by rewrite cat_take_drop.
have {1} ->: range a b = range a hx ++ range hx b.
- smt(range_cat).
rewrite mask_cat; first smt(size_range size_take).
suff: mask (take (hx - a) m) (range a hx) = [].
- by move => ->; exact cat0s.
apply mem_eq0 => i.
case (i < a \/ hx <= i) => ?.
- smt(mem_mask mem_range).
rewrite mem_mask_range; 1,2,3:smt(size_take size_range).
rewrite nth_take; 1,2: smt().
suff: !(i \in xs).
- move => ?.
  rewrite -(mem_mask_range m a b); smt(size_range).
suff: forall j, j \in xs => i < j by smt().
move => j mem_j.
apply (sorted_lower_bounded Int.(<) 0 i j xs); smt(sorted_from_cons).
qed.

lemma sorted_behead (e : 'a -> 'a -> bool) xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  sorted e xs =>
  sorted e (behead xs).
proof.
move => ?.
case (xs = []) => ?; first smt().
apply subseq_sorted => //=.
apply subseqP.
exists (false :: nseq (size xs - 1) true).
split; first smt(size_nseq size_ge0).
rewrite -{3}(head_behead xs witness) //.
rewrite mask_cons /b2i /=.
rewrite nseq0 cat0s.
rewrite mask_true /#.
qed.

lemma sorted_nth (dfl : 'a) e xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall i, 0 <= i => i < size xs - 1 => e (nth dfl xs i) (nth dfl xs (i + 1))) <=>
  sorted e xs.
proof.
move => ?.
split; first by exact sorted_from_nth.
move => sorted_xs i ge0_i ub_i.
suff: sorted e [nth dfl xs i; nth dfl xs (i + 1)] by smt().
apply (subseq_sorted e _ _ xs) => //.
rewrite -{3}(map_nth_range dfl xs).
pose get_ith := nth dfl xs.
have ->: [nth dfl xs i; nth dfl xs (i + 1)] = map get_ith [i; i + 1].
- smt().
apply map_subseq.
by apply subseq_range => /#.
qed.

(* TODO naming is maybe bad.
 * The proof should be cleaned up too... *)
lemma sorted_nth_gapped (dfl : 'a) e xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall i j, 0 <= i => i < j => j < size xs => e (nth dfl xs i) (nth dfl xs j)) <=>
  sorted e xs.
proof.
move => ?.
split; first smt(sorted_nth).
elim xs; first smt().
move => /= x xs iH H i j ???.
case (xs = []) => ?; first smt().
case (i = 0); last smt().
have -> /=: j <> 0 by smt().
move => ?.
have ?: e x (head dfl xs) by smt(head_behead).
case (j = 1) => ?; first smt().
suff: e (head dfl xs) (nth dfl xs (j - 1)).
- smt().
rewrite -nth0_head.
apply iH => /#.
qed.

lemma sorted_rcons dfl (e : 'a -> 'a -> bool) xs x :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  sorted e xs =>
  (xs <> [] => e (last dfl xs) x) =>
  sorted e (rcons xs x).
proof.
move => ???.
case (xs = []) => [/#|?].
apply (sorted_from_nth dfl) => i ge0_i ub_i.
rewrite size_rcons /= in ub_i.
case (i < size xs - 1) => ?.
- rewrite !nth_rcons.
  rewrite ub_i /=.
  have -> /=: i + 1 < size xs by smt().
  smt(sorted_nth).
have -> /=: i = size xs - 1 by smt().
rewrite !nth_rcons.
have -> /=: size xs - 1 < size xs by smt().
smt(last_nth).
qed.

lemma sorted_cons dfl (e : 'a -> 'a -> bool) xs x :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  sorted e xs =>
  (xs <> [] => e x (head dfl xs)) =>
  sorted e (x :: xs).
proof. smt(). qed.

lemma sorted_cat (dfl : 'a) e xs1 xs2 :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  xs1 <> [] =>
  xs2 <> [] =>
  sorted e xs1 =>
  sorted e xs2 =>
  e (last dfl xs1) (head dfl xs2) =>
  sorted e (xs1 ++ xs2).
proof.
move => ??????.
apply (sorted_from_nth dfl) => i ge0_i ub_i.
rewrite size_cat in ub_i.
case (i < size xs1 - 1) => [?|?].
- rewrite !nth_cat.
  have -> /=: i < size xs1 by smt().
  have -> /=: i + 1 < size xs1 by smt().
  suff: sorted e [nth dfl xs1 i; nth dfl xs1 (i + 1)] by smt().
  apply (subseq_sorted e _ _ xs1) => //.
  rewrite -{3}(map_nth_range dfl xs1).
  apply (map_subseq (nth dfl xs1) [i; i + 1]).
  apply subseq_range => /#.
case (i = size xs1 - 1) => [?|?].
- rewrite !nth_cat.
  have -> /=: i < size xs1 by smt().
  have -> /=: !(i + 1 < size xs1) by smt().
  smt(nth_last).
rewrite !nth_cat.
have -> /=: !(i < size xs1) by smt().
have -> /=: !(i + 1 < size xs1) by smt().
suff: sorted e [nth dfl xs2 (i - size xs1); nth dfl xs2 (i + 1 - size xs1)] by smt().
apply (subseq_sorted e _ _ xs2) => //.
rewrite -{3}(map_nth_range dfl xs2).
apply (map_subseq (nth dfl xs2) [i - size xs1; i + 1 - size xs1]).
apply subseq_range => /#.
qed.

lemma uniq_irreflexive_sorted (e : 'a -> 'a -> bool) xs :
  (forall (y x z : 'a), e x y => e y z => e x z) =>
  (forall x, !(e x x)) =>
  sorted e xs =>
  uniq xs.
proof.
move => ??.
elim xs => // x xs iH.
move => H /=.
split; last smt().
suff: (x \in xs) => false by smt().
move => contr.
rewrite (nthP witness) in contr.
case contr => [i [rg_i ?]].
have ?: (i + 1) < size (x :: xs) => e (nth witness (x :: xs) 0) (nth witness (x :: xs) (i + 1)).
- by apply sorted_nth_gapped => /#.
smt().
qed.

lemma mem_take_from_nth (dfl : 'a) x xs i j :
  x \in xs =>
  x = nth dfl xs j =>
  0 <= j =>
  j < i =>
  i < size xs =>
  x \in take i xs.
proof. move: i j; elim xs; smt(). qed.

lemma mem_drop_from_nth (dfl : 'a) x xs i j :
  x \in xs =>
  x = nth dfl xs j =>
  0 <= i =>
  i < j =>
  j < size xs =>
  x \in drop i xs.
proof.
move => ?????.
apply (nthP dfl).
exists (j - i); smt(size_drop nth_drop).
qed.

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

(* -- Extending RealFlub -- *)

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

(* standard delta-epsilon definition of limits and continuity *)

op is_lim (f : real -> real) (x y : real) =
  forall dy, 0%r < dy =>
  (exists dx, 0%r < dx /\ forall x', x' <> x => `|x' - x| < dx => `|f x' - y| < dy).
op lim_exists f x = exists y, is_lim f x y.
op lim f x = choiceb (is_lim f x) 0%r.
op slope (f : real -> real) (x dx : real) = (f (x + dx) - f x) / dx.
op derive f x = lim (slope f x) 0%r.
op differentiable_at f x = lim_exists (slope f x) 0%r.
op continuous_at f x = (lim_exists f x /\ lim f x = f x).
op continuous f = forall x, continuous_at f x.

lemma lim_unique f x y0 y1 :
  is_lim f x y0 => is_lim f x y1 => y0 = y1.
proof.
move => is_lim_y0 is_lim_y1.
apply (absurd true) => [ne_ys /=|//].
pose eps := `|y0 - y1| / 4%r.
have is_lim_y0': exists dx, 0%r < dx /\ forall x', x' <> x => `|x' - x| < dx => `|f x' - y0| < eps.
- by apply is_lim_y0 => /#.
have is_lim_y1': exists dx, 0%r < dx /\ forall x', x' <> x => `|x' - x| < dx => `|f x' - y1| < eps.
- by apply is_lim_y1 => /#.
clear is_lim_y0 is_lim_y1.
case is_lim_y0' => [dx0 [gt0_dx0 is_lim_y0]].
case is_lim_y1' => [dx1 [gt0_dx1 is_lim_y1]].
pose x0 := x + minr dx0 dx1 / 2%r.
have ?: `|f x0 - y0| < eps by smt().
have ?: `|f x0 - y1| < eps by smt().
smt().
qed.

lemma continuous_flub (f : real -> real) (x eps : real) :
  0%r < eps =>
  continuous_at f x =>
  exists dx,
  0%r < dx /\
  has_fub_in f (x - dx) (x + dx) /\
  flub_in f (x - dx) (x + dx) < f x + eps.
proof.
move => ??.
have [dx [gt0_dx H]]:
  exists dx, 0%r < dx /\ forall x', x' <> x => `|x' - x| < dx => `|f x' - f x| < eps / 2%r.
- have H: is_lim f x (f x) by smt(choicebP).
  apply (H (eps / 2%r)) => /#.
exists (dx / 2%r).
split; first smt().
split.
- exists (f x + eps) => /#.
apply (ler_lt_trans (f x + eps / 2%r)); last smt().
apply flub_in_le_ub => /#.
qed.

lemma continuous_flub_fglb (f : real -> real) (x eps : real) :
  0%r < eps =>
  continuous_at f x =>
  exists dx,
  0%r < dx /\
  has_fub_in f (x - dx) (x + dx) /\
  flub_in f (x - dx) (x + dx) < f x + eps /\
  has_flb_in f (x - dx) (x + dx) /\
  fglb_in f (x - dx) (x + dx) > f x - eps.
proof.
move => ??.
have [dx [gt0_dx H]]:
  exists dx, 0%r < dx /\ forall x', x' <> x => `|x' - x| < dx => `|f x' - f x| < eps / 2%r.
- have H: is_lim f x (f x) by smt(choicebP).
  apply (H (eps / 2%r)) => /#.
exists (dx / 2%r).
split; first smt().
split.
- exists (f x + eps) => /#.
split.
- apply (ler_lt_trans (f x + eps / 2%r)); last smt().
  apply flub_in_le_ub => /#.
split.
- exists (f x - eps) => /#.
apply (ltr_le_trans (f x - eps / 2%r)); first smt().
apply fglb_in_ge_lb => /#.
qed.

lemma continuous_at_negate f x :
  continuous_at f x =>
  continuous_at (Real.([ - ]) \o f) x.
proof.
move => [[y y_is_lim] lim_fx].
suff: is_lim (Real.([-]) \o f) x (- f x).
- move => H; split.
  + by exists (-f x).
  apply (lim_unique (Real.([-]) \o f) x).
  + apply (choicebP (is_lim (Real.([-]) \o f) x) 0%r).
    by exists (- f x).
  rewrite /(\o) in H.
  by rewrite /(\o).
move => dy gt0_dy.
have [dx ?]: exists (dx : real),
  0%r < dx /\
  forall (x' : real), x' <> x => `|x' - x| < dx => `|f x' - y| < dy.
- exact y_is_lim.
exists dx.
smt(choicebP lim_unique).
qed.

lemma continuous_negate f :
  continuous f =>
  continuous (Real.([ - ]) \o f).
proof.
rewrite /continuous => H x.
apply continuous_at_negate.
exact H.
qed.

lemma converge_continuous_map f xs :
  continuous f =>
  converge xs =>
  converge (f \o xs).
proof.
move => ? [lx converge_to_lx].
have H: continuous_at f lx by smt().
case H => [[ly is_lim_ly]?].
exists ly.
rewrite /(\o) /= => eps gt0_eps.
have [dx [gt0_dx ?]]:
  exists dx, 0%r < dx /\ forall x', x' <> lx => `|x' - lx| < dx => `|f x' - ly| < eps.
- exact is_lim_ly.
have [N ?]: exists (N : int), forall n, N <= n => `|xs n - lx| < dx.
- exact converge_to_lx.
exists N.
move => n geN_n.
case (xs n = lx); last smt().
move => ->.
suff: f lx = ly by smt().
suff: is_lim f lx (f lx) by smt(lim_unique).
smt(choicebP).
qed.

lemma continuous_has_fub_in f x0 x1 :
  continuous f =>
  has_fub_in f x0 x1.
proof.
move => continuous_f.
case (x0 < x1) => ?; first last.
- by exists (f x0) => /#.
suff: (forall r, exists x, x0 <= x /\ x <= x1 /\ r < f x) => false by smt().
move => ?.
pose s (i : int) := choiceb (fun x => x0 <= x /\ x <= x1 /\ i%r < f x) 0%r.
have [s' [[m ?] ?]] : exists s', real_subseq s' s /\ converge s'.
- by apply (Bolzano_Weierstrass s x0 x1); smt(choicebP).
have ?: converge (f \o s').
- exact converge_continuous_map.
suff: !(converge (f \o s')) by smt().
apply diverge_superlinear => i.
rewrite /(\o).
have ->: f (s' i) = f (s (m i)) by smt().
have H: (fun (x : real) => x0 <= x /\ x <= x1 /\ (m i)%r < f x) (s (m i)).
- apply choicebP => /#.
smt().
qed.

lemma continuous_has_flb_in f x0 x1 :
  continuous f =>
  has_flb_in f x0 x1.
proof.
move => continuous_f.
apply continuous_negate in continuous_f.
rewrite has_flb_in_negate.
exact continuous_has_fub_in.
qed.

(* -- Sums and integrals -- *)

op is_partition xs (x0 x1 : real) =
  sorted Real.(<) xs /\
  x0 < x1 /\
  head 0%r xs = x0 /\
  last 0%r xs = x1.

op make_intervals xs = map (fun i => (nth 0%r xs i, nth 0%r xs (i + 1))) (range 0 (size xs - 1)).

op lower_sum_ith f x0x1 =
  let (x0, x1) = x0x1 in
  fglb_in f x0 x1 * (x1 - x0).

op lower_sum f xs = big predT (lower_sum_ith f) (make_intervals xs).

op is_lower_sum f x0 x1 y =
  exists xs,
  is_partition xs x0 x1 /\
  lower_sum f xs = y.

lemma lt_make_interval xs x0 x1 xi xii :
  is_partition xs x0 x1 =>
  (xi, xii) \in make_intervals xs =>
  xi < xii.
proof.
move => [??] in_intervals.
suff: subseq [xi; xii] xs.
- move => ?.
  suff: sorted Real.(<) [xi; xii] by smt().
  apply (subseq_sorted Real.(<) _ _ xs) => //; smt().
rewrite -(map_nth_range 0%r xs).
pose get_ith := fun i => nth 0%r xs i.
rewrite /make_intervals mapP /= in in_intervals.
case in_intervals => [i [rg_i ?]].
rewrite mem_range in rg_i.
have ->: [xi; xii] = map get_ith [i; i + 1] by smt().
apply map_subseq.
by apply subseq_range => /#.
qed.

lemma mem_interval xs x0 x1 xi xii :
  is_partition xs x0 x1 =>
  (xi, xii) \in make_intervals xs =>
  xi \in xs /\ xii \in xs.
proof.
rewrite /make_intervals /= => is_partition_xs.
rewrite mapP /= => [[i [rg_i [-> ->]]]].
smt(mem_nth mem_range).
qed.

lemma mem_interval_lb xs x0 x1 xi xii :
  is_partition xs x0 x1 =>
  (xi, xii) \in make_intervals xs =>
  x0 <= xi.
proof.
rewrite /make_intervals /= => ?.
rewrite mapP /=.
move => [i [rg_i [->]]].
move => _.
rewrite mem_range in rg_i.
case (i = 0) => ?; first smt().
suff: sorted Real.( < ) (map (nth 0%r xs) [0; i]) by smt().
apply (subseq_sorted _ _ _ xs); 1,3: smt().
rewrite -{2}(map_nth_range 0%r xs).
apply map_subseq.
by apply subseq_range => /#.
qed.

lemma mem_interval_ub xs x0 x1 xi xii :
  is_partition xs x0 x1 =>
  (xi, xii) \in make_intervals xs =>
  xii <= x1.
proof.
move => is_partition_xs.
rewrite /make_intervals mapP /=.
move => [i [rg_i [??]]]; subst.
rewrite mem_range in rg_i.
case (i = size xs - 2) => ?; first smt(nth_last).
suff: sorted Real.( < ) (map (nth 0%r xs) [i + 1; size xs - 1]) by smt(nth_last).
apply (subseq_sorted _ _ _ xs); 1,3:smt().
rewrite -{3}(map_nth_range 0%r xs).
apply map_subseq.
by apply subseq_range => /#.
qed.

lemma adjacent_intervals xs x0 x1 i :
  is_partition xs x0 x1 =>
  0 <= i =>
  i < size xs - 2 =>
  let intervals = make_intervals xs in
  snd (nth (0%r, 0%r) intervals i) = fst (nth (0%r, 0%r) intervals (i + 1)).
proof.
move => is_partitions_xs ge0_i ub_i /=.
rewrite !(nth_map 0) /=; 1,2: smt(size_range).
by rewrite !nth_range /#.
qed.

lemma lower_sum_le (f1 f2 : real -> real) xs x0 x1 :
  is_partition xs x0 x1 =>
  has_flb_in f1 x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f1 x <= f2 x) =>
  lower_sum f1 xs <= lower_sum f2 xs.
proof.
move => is_partition_xs has_flb_f1 le_f1_f2.
rewrite /lower_sum.
apply ler_sum_seq => /= [[xi xii] mem_xi] _.
rewrite /lower_sum_ith /=.
suff: fglb_in f1 xi xii <= fglb_in f2 xi xii.
- smt(lt_make_interval).
have ?: x0 <= xi by smt(mem_interval_lb).
have ?: xii <= x1 by smt(mem_interval_ub).
apply ler_fglb_in.
- smt(lt_make_interval).
- by apply (has_flb_in_subset _ x0 _ x1); smt().
smt().
qed.

op split_partition_to (xs : real list) (x : real) =
  rcons (filter (fun a => a < x) xs) x.

op split_partition_from (xs : real list) (x : real) =
  x :: (filter (fun a => x < a) xs).

lemma sorted_split_partition_to xs x :
  xs <> [] =>
  x >= head 0%r xs =>
  sorted Real.(<) xs =>
  sorted Real.(<) (split_partition_to xs x).
proof.
move => ???.
rewrite /split_partition_to.
apply (sorted_rcons 0%r); 1,2: smt(sorted_filter).
pose ys := filter (fun a => a < x) xs.
move => ?.
suff: last 0%r ys \in ys by smt(mem_filter).
rewrite (last_nth 0%r 0%r ys).
smt(mem_nth size_ge0).
qed.

lemma head_split_partition_to xs x :
  xs <> [] =>
  x > head 0%r xs =>
  head 0%r (split_partition_to xs x) = head 0%r xs.
proof.
move => ??.
rewrite /split_partition_to -nth0_head.
rewrite nth_rcons size_filter -has_count.
have -> /=: has (fun a => a < x) xs.
- apply hasP; exists (head 0%r xs) => /#.
rewrite -{1}(head_behead xs 0%r) //.
by rewrite filter_cons /#.
qed.

lemma last_split_partition_to xs x :
  xs <> [] =>
  x < last 0%r xs =>
  last 0%r (split_partition_to xs x) = x.
proof.
move => ??.
rewrite /split_partition_to.
exact last_rcons.
qed.

lemma is_partition_split_to xs (x0 x1 x2 : real) :
  x0 < x1 =>
  x1 < x2 =>
  is_partition xs x0 x2 =>
  is_partition (split_partition_to xs x1) x0 x1.
proof.
move => ?? [?[?[??]]].
split; first by apply sorted_split_partition_to => /#.
split; first by smt().
split; first by rewrite head_split_partition_to /#.
by rewrite last_split_partition_to /#.
qed.

lemma sorted_split_partition_from xs x :
  xs <> [] =>
  x >= head 0%r xs =>
  sorted Real.(<) xs =>
  sorted Real.(<) (split_partition_from xs x).
proof.
move => ?? sorted_xs.
rewrite /split_partition_from.
apply (sorted_cons 0%r) => //.
- smt().
- by apply sorted_filter => /#.
move => ?.
suff: head 0%r (filter ((<) x) xs) \in filter ((<) x) xs.
- move => H.
  by rewrite mem_filter /# in H.
smt(mem_head).
qed.

lemma head_split_partition_from xs x :
  head 0%r (split_partition_from xs x) = x.
proof. smt(). qed.

lemma last_split_partition_from xs x :
  xs <> [] =>
  x < last 0%r xs =>
  last 0%r (split_partition_from xs x) = last 0%r xs.
proof.
move => ??.
pose ys := rev xs.
have ->: xs = rev ys by smt(revK).
rewrite last_rev.
rewrite last_cons.
rewrite filter_rev.
have ?: ys <> [] by smt(rev_nil revK).
have ?: x < head 0%r ys by smt(last_rev revK).
rewrite last_rev.
rewrite -{1}(head_behead ys 0%r) //.
rewrite filter_cons /#.
qed.

lemma is_partition_split_from xs (x0 x1 x2 : real) :
  x0 < x1 =>
  x1 < x2 =>
  is_partition xs x0 x2 =>
  is_partition (split_partition_from xs x1) x1 x2.
proof.
move => ???.
rewrite /is_partition.
split; first apply sorted_split_partition_from => /#.
split => //.
split; first apply head_split_partition_from => /#.
by rewrite last_split_partition_from /#.
qed.

lemma split_partition_mem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x \in xs =>
  xs = (filter (fun (a : real) => a < x) xs) ++ [x] ++ (filter (fun (a : real) => x < a) xs).
proof.
move => ? mem_x.
rewrite (nthP 0%r) in mem_x.
case mem_x => i [[??]<-].
rewrite -{1}(cat_take_drop_pick 0%r i xs) //=.
congr.
- congr => //.
  apply (eq_sorted Real.( < ) _ _); 1,2,3,4: smt(sorted_take sorted_filter).
  apply uniq_perm_eq.
  + apply (uniq_irreflexive_sorted Real.( < )) => /=; 1,2: smt().
    by apply sorted_take => /#.
  + apply filter_uniq.
    by apply (uniq_irreflexive_sorted Real.( < )) => /#.
  move => y.
  split.
  + rewrite (nthP 0%r).
    move => [j [H <-]].
    rewrite size_take //= in H.
    have [??] {H}: 0 <= j /\ j < i by smt().
    rewrite nth_take //.
    rewrite mem_filter //=.
    split; last smt(mem_nth).
    apply sorted_nth_gapped => /#.
  + rewrite mem_filter /=.
    move => [H mem_y].
    suff: exists j, 0 <= j /\ j < i /\ y = nth 0%r xs j by smt(mem_take_from_nth).
    rewrite (nthP 0%r) in mem_y.
    case mem_y => j [rg_j <<-].
    exists j => //.
    split; first smt().
    split => //.
    suff: i < j => false by smt().
    move => contr.
    suff: 0 <= i => i < j => j < size xs => nth 0%r xs i < nth 0%r xs j by smt().
    smt(sorted_nth_gapped).
- apply (eq_sorted Real.( < ) _ _); 1,2,3,4:smt(sorted_drop sorted_filter).
  apply uniq_perm_eq.
  + by apply (uniq_irreflexive_sorted Real.( < )); 1,2,3:smt(sorted_drop).
  + apply filter_uniq.
    by apply (uniq_irreflexive_sorted Real.( < )) => /#.
  move => y.
  split.
  + rewrite (nthP 0%r).
    move => [j [H <-]].
    rewrite size_drop //= in H; first smt().
    rewrite nth_drop; 1,2:smt().
    rewrite mem_filter //=.
    split; last smt(mem_nth).
    apply sorted_nth_gapped => /#.
  + rewrite mem_filter /=.
    move => [H mem_y].
    suff: y \in drop i xs by smt(drop_nth).
    suff: exists j, i < j /\ j < size xs /\ y = nth 0%r xs j by smt(mem_drop_from_nth).
    rewrite (nthP 0%r) in mem_y.
    case mem_y => j [rg_j ?].
    exists j => //.
    split; last smt().
    suff: i < j by smt().
    suff: j < i => false by smt().
    move => contr.
    suff: 0 <= j => j < i => i < size xs => nth 0%r xs j < nth 0%r xs i by smt().
    smt(sorted_nth_gapped).
qed.

lemma split_partition_nomem xs x0 x1 x :
  is_partition xs x0 x1 =>
  (* extraneous but w/e *) x0 < x => x < x1 =>
  ! (x \in xs) =>
  xs = (filter (fun (a : real) => a < x) xs) ++ (filter (fun (a : real) => x < a) xs).
proof.
move => [sorted_xs ?] ???.
pose lst1 := (filter (fun (a : real) => a < x) xs).
pose lst2 := filter (fun (a : real) => x < a) xs.
have ?: lst1 <> [] by smt().
have ?: lst2 <> [] by smt(mem_filter mem_last).
have ?: sorted Real.(<) (lst1 ++ lst2).
- apply (sorted_cat 0%r Real.( < )) => //.
  + smt().
  + apply sorted_filter => //.
  + smt().
  + apply sorted_filter => //.
  + smt().
  apply (ler_lt_trans x).
  + smt(mem_last mem_filter).
  have H: (head 0%r lst2 \in lst2) by smt().
  rewrite mem_filter /= in H.
  smt().
apply (eq_sorted Real.(<)) => //; 1,2: smt().
apply uniq_perm_eq => //.
- apply (uniq_irreflexive_sorted Real.( < )) => //#.
- apply (uniq_irreflexive_sorted Real.( < )) => //#.
smt(mem_cat mem_filter).
qed.

lemma eq_nth_interval_cat1 dfl lst1 lst2 i :
  0 <= i =>
  i < size lst1 - 1 =>
  nth dfl (make_intervals (lst1 ++ lst2)) i =
  nth dfl (make_intervals lst1) i.
proof.
move => ??.
case (lst1 = []) => ?; first smt().
case (lst2 = []) => ?; first smt(cats0).
rewrite (nth_map 0) /=.
- smt(size_cat size_range size_ge0).
rewrite nth_cat.
rewrite size_cat /=.
rewrite nth_range /=.
- smt(size_ge0).
have -> /=: i < size lst1 by smt().
rewrite (nth_map 0) /=.
- smt(size_cat size_range size_ge0).
rewrite nth_cat.
have -> /=: i + 1 < size lst1 by smt().
rewrite nth_range /#.
qed.

lemma eq_nth_interval_cat2 dfl lst1 lst1' lst2 i :
  size lst1 <= i =>
  i < size lst1 + size lst2 - 1 =>
  size lst1 = size lst1' =>
  nth dfl (make_intervals (lst1 ++ lst2)) i =
  nth dfl (lst1' ++ (make_intervals lst2)) i.
proof.
move => ???.
case (lst1 = []) => ?; first smt(size_eq0 cat0s).
have ?: lst1' <> [] by smt(size_eq0).
case (lst2 = []) => ?; first smt().
rewrite (nth_map 0) /=.
- smt(size_range size_cat size_ge0).
rewrite nth_cat.
rewrite size_cat.
rewrite nth_range /=.
- smt(size_range size_cat size_ge0).
have ->/=: !(i < size lst1) by smt().
rewrite nth_cat.
have ->/=:!(i + 1 < size lst1) by smt().
rewrite nth_cat.
have -> /=: !(i < size lst1') by smt().
rewrite (nth_map 0) /=.
- smt(size_range size_cat size_ge0).
rewrite nth_range.
- smt(size_range size_cat size_ge0).
- smt(size_range size_cat size_ge0).
qed.

lemma cat_split_intervals_mem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x \in xs =>
  make_intervals (split_partition_to xs x) ++
  make_intervals (split_partition_from xs x)
  = make_intervals xs.
proof.
move => ??.
apply eq_sym.
apply (eq_from_nth (0%r, 0%r)).
- rewrite {1}(split_partition_mem xs x0 x1 x) //=.
  rewrite !size_cat !size_map !size_cat !size_range /=.
  rewrite !size_rcons /split_partition_from /=.
  smt(size_ge0).
move => i rg_i.
rewrite {1}(split_partition_mem xs x0 x1 x) //.
case (i < size (make_intervals (split_partition_to xs x))) => /= H.
- have ->: filter (fun (a : real) => a < x) xs ++ [x] = split_partition_to xs x.
  + by rewrite /split_partition_to cats1.
  rewrite nth_cat H /=.
  apply eq_nth_interval_cat1.
  + smt().
  + smt(size_range size_map).
- have ->: filter (fun (a : real) => a < x) xs ++ [x] ++ filter ((<) x) xs =
    filter (fun (a : real) => a < x) xs ++ split_partition_from xs x.
  + rewrite /split_partition_from.
    rewrite -(cat1s x (filter (fun (a : real) => x < a) xs)).
    by rewrite catA /#.
  apply eq_nth_interval_cat2.
  + rewrite /make_intervals /split_partition_to /= in H.
    rewrite size_map size_range size_rcons in H.
    smt().
  + (* This shouldn't be this painful.
     * Either there's some algebra nonsense or I'm missing something *)
    have H2: xs = filter (fun (a : real) => a < x) xs ++ [x] ++ filter (fun (a : real) => x < a) xs.
    * exact (split_partition_mem xs x0 x1).
    have rg_i' {rg_i}: i < size (make_intervals
      (filter (fun (a : real) => a < x) xs ++ [x] ++ filter (fun (a : real) => x < a) xs)).
    * rewrite -H2 /#.
    rewrite size_map size_range /= in rg_i'.
    rewrite -catA in rg_i'.
    rewrite size_cat in rg_i'.
    have ->: split_partition_from xs x = [x] ++ filter ((<) x) xs.
    * rewrite cat1s.
      rewrite /split_partition_from.
      smt(fun_ext).
    rewrite size_cat /= in rg_i'.
    rewrite size_cat /=.
    have H3: max 0
         (size (filter (fun (a : real) => a < x) xs) +
          (1 + size (filter ((<) x) xs)) - 1) = 
         (size (filter (fun (a : real) => a < x) xs) +
          size (filter ((<) x) xs)).
    + have ->: (size (filter (fun (a : real) => a < x) xs) +
        (1 + size (filter ((<) x) xs)) - 1) =
        (size (filter (fun (a : real) => a < x) xs) +
        (size (filter ((<) x) xs))) by algebra.
      have fact: forall (a b : int), 0 <= a => 0 <= b => max 0 (a + b) = a + b by smt().
      apply fact; smt(size_ge0).
    have H4: i < size (filter (fun (a : real) => a < x) xs) + size (filter ((<) x) xs).
    + by rewrite -H3.
    have fact: forall (i a b : int), i < a + b => i < a + (1 + b) - 1 by smt().
    apply fact => //.
  + rewrite /make_intervals size_map.
    rewrite /split_partition_to size_rcons /=.
    rewrite size_range /=.
    smt(size_ge0).
qed.

lemma size_make_intervals lst :
  lst <> [] =>
  size (make_intervals lst) = size lst - 1.
proof. smt(size_map size_range size_ge0). qed.

lemma cat_split_intervals_nomem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x0 < x => x < x1 =>
  !(x \in xs) =>
  make_intervals (split_partition_to xs x) ++
  make_intervals (split_partition_from xs x) =
  let lst1 = filter (fun a => a < x) xs in
  let lst2 = filter (fun a => x < a) xs in
  make_intervals lst1 ++ [(last 0%r lst1, x); (x, head 0%r lst2)] ++ make_intervals lst2.
proof.
move => ????.
rewrite /split_partition_to /split_partition_from /=.
pose lst1 := filter (fun a => a < x) xs.
pose lst2 := filter (( < ) x) xs.
have ?: lst1 <> [] by smt().
have ?: lst2 <> [] by smt(mem_filter mem_last).
apply (eq_from_nth (0%r, 0%r)); first smt(size_cat size_make_intervals size_rcons).
move => i.
rewrite size_cat !size_make_intervals; 1,2:smt().
rewrite size_rcons /= => rg_i.
case (i < size (make_intervals lst1)) => ?.
- rewrite nth_cat.
  have -> /=: i < size (make_intervals (rcons lst1 x)).
  + smt(size_make_intervals size_rcons).
  rewrite -catA nth_cat.
  have -> /=: i < size (make_intervals lst1) by assumption.
  rewrite (nth_map 0) /=.
  + smt(size_range size_rcons size_make_intervals).
  rewrite (nth_map 0) /=.
  + smt(size_range size_rcons size_make_intervals).
  smt(nth_rcons nth_range size_make_intervals size_rcons).
case (i = size (make_intervals lst1)) => ?.
- rewrite nth_cat.
  have -> /=: i < size (make_intervals (rcons lst1 x)).
  + smt(size_make_intervals size_rcons).
  rewrite nth_cat.
  have -> /=: i < size (make_intervals lst1 ++ [(last 0%r lst1, x); (x, head 0%r lst2)]).
  + smt(size_make_intervals size_cat).
  rewrite nth_cat /=.
  have -> /=: !(i < size (make_intervals lst1)) by smt().
  have -> /=: i - size (make_intervals lst1) = 0 by smt().
  rewrite (nth_map 0) /=.
  + smt(size_range size_rcons size_make_intervals).
  rewrite size_rcons /=.
  rewrite nth_range /=.
  + smt(size_make_intervals).
  split; first smt(nth_last size_make_intervals nth_rcons).
  rewrite nth_rcons.
  have -> /=: !(i + 1 < size lst1) by smt(size_make_intervals).
  smt(size_make_intervals).
case (i = size (make_intervals lst1) + 1) => ?.
- rewrite nth_cat.
  have -> /=: !(i < size (make_intervals (rcons lst1 x))).
  + smt(size_make_intervals size_rcons).
  rewrite nth_cat.
  have -> /=: i < size (make_intervals lst1 ++ [(last 0%r lst1, x); (x, head 0%r lst2)]).
  + smt(size_make_intervals size_cat).
  rewrite nth_cat /=.
  have -> /=: !(i < size (make_intervals lst1)) by smt().
  have -> /=: !(i - size (make_intervals lst1) = 0) by smt().
  rewrite (nth_map 0) /=.
  + smt(size_range size_rcons size_make_intervals).
  rewrite nth_range /=.
  + smt(size_make_intervals size_rcons).
  smt(size_range size_rcons size_make_intervals).
(* Can't use eq_nth_interval_cat2...
 * Below is brute force unfortunately. *)
rewrite nth_cat.
have -> /=: !(i < size (make_intervals (rcons lst1 x))).
- smt(size_range size_rcons size_make_intervals).
rewrite nth_cat.
have -> /=: !(i < size (make_intervals lst1 ++ [(last 0%r lst1, x); (x, head 0%r lst2)])).
- smt(size_range size_rcons size_make_intervals size_cat).
rewrite (nth_map 0) /=.
- smt(size_range size_rcons size_make_intervals size_cat).
rewrite nth_range /=.
- smt(size_range size_rcons size_make_intervals size_cat).
have -> /=: !(i - size (make_intervals (rcons lst1 x)) = 0).
- smt(size_range size_rcons size_make_intervals size_cat).
have -> /=: !(i - size (make_intervals (rcons lst1 x)) + 1 = 0).
- smt(size_range size_rcons size_make_intervals size_cat).
rewrite (nth_map 0) /=.
- smt(size_range size_rcons size_make_intervals size_cat nth_range).
smt(size_range size_rcons size_make_intervals size_cat nth_range).
qed.

lemma split_intervals_nomem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x0 < x => x < x1 =>
  !(x \in xs) =>
  make_intervals xs =
  let lst1 = filter (fun a => a < x) xs in
  let lst2 = filter (fun a => x < a) xs in
  make_intervals lst1 ++ [(last 0%r lst1, head 0%r lst2)] ++ make_intervals lst2.
proof.
move => ???? /=.
pose lst1 := filter (fun a => a < x) xs.
pose lst2 := filter (Real.(<) x) xs.
have ?: lst1 <> [] by smt().
have ?: lst2 <> [] by smt(mem_filter mem_last).
rewrite {1}(split_partition_nomem xs x0 x1 x) //=.
have ->: filter (fun (a : real) => a < x) xs ++ filter ((<) x) xs = lst1 ++ lst2 by trivial.
apply (eq_from_nth (0%r, 0%r)); first smt(size_cat size_make_intervals).
move => i rg_i.
case (i < size (make_intervals lst1)) => ?.
- rewrite nth_cat.
  have -> /=: i < size (make_intervals lst1 ++ [(last 0%r lst1, head 0%r lst2)]).
  + smt(size_make_intervals size_cat size_ge0).
  rewrite nth_cat.
  have -> /=: i < size (make_intervals lst1).
  + smt(size_make_intervals size_cat size_ge0).
  rewrite eq_nth_interval_cat1; smt(size_make_intervals).
case (i = size (make_intervals lst1)) => ?.
- apply (eq_trans _ (last 0%r lst1, head 0%r lst2)); last first.
  + rewrite nth_cat.
    have -> /=: i < size (make_intervals lst1 ++ [(last 0%r lst1, head 0%r lst2)]) by smt(size_cat).
    rewrite nth_cat.
    smt(size_make_intervals).
  rewrite /make_intervals (nth_map 0) /=.
  + smt(size_range size_cat size_make_intervals).
  rewrite !nth_range /=.
  + smt(size_cat size_make_intervals).
  smt(nth_cat size_make_intervals nth_last).
apply eq_nth_interval_cat2; smt(size_make_intervals size_cat).
qed.

lemma lower_sum_ith_split f (x0 x1 x2 : real) :
  x0 < x1 =>
  x1 < x2 =>
  has_flb_in f x0 x2 =>
  lower_sum_ith f (x0, x2) <=
  lower_sum_ith f (x0, x1) + lower_sum_ith f (x1, x2).
proof. smt(fglb_in_subset). qed.

lemma partition_lb xs x0 x1 x :
  is_partition xs x0 x1 =>
  x \in xs =>
  x0 <= x.
proof.
move => ? mem_x.
rewrite (nthP 0%r) in mem_x.
case mem_x => [i [rg_i <-]].
have ->: x0 = nth 0%r xs 0 by smt().
case (i = 0) => [/#|?].
suff: sorted Real.( < ) (map (nth 0%r xs) [0; i]) by smt().
apply (subseq_sorted _ _ _ xs) => //; 1,3: smt().
rewrite -{2}(map_nth_range 0%r xs).
apply (map_subseq (nth 0%r xs)).
by apply subseq_range => /#.
qed.

lemma partition_ub xs x0 x1 x :
  is_partition xs x0 x1 =>
  x \in xs =>
  x <= x1.
proof.
move => ? mem_x.
rewrite (nthP 0%r) in mem_x.
case mem_x => [i [rg_i <-]].
have ->: x1 = nth 0%r xs (size xs - 1) by smt(nth_last).
case (i = size xs - 1) => [/#|?].
suff: sorted Real.( < ) (map (nth 0%r xs) [i; size xs - 1]) by smt().
apply (subseq_sorted _ _ _ xs) => //; 1,3: smt().
rewrite -{3}(map_nth_range 0%r xs).
apply (map_subseq (nth 0%r xs)).
by apply subseq_range => /#.
qed.

lemma split_lower_sum x f xs x0 x1 :
  is_partition xs x0 x1 =>
  x0 < x =>
  x < x1 =>
  has_flb_in f x0 x1 =>
  lower_sum f xs <= lower_sum f (split_partition_to xs x) + lower_sum f (split_partition_from xs x).
proof.
move => is_partition_xs lb_x ub_x has_flb_f.
rewrite -big_cat.
case (x \in xs) => [mem_x | not_mem_x].
- by rewrite /lower_sum -(cat_split_intervals_mem xs x0 x1 x).
rewrite /lower_sum (cat_split_intervals_nomem xs x0 x1 x) //=.
rewrite (split_intervals_nomem xs x0 x1 x) //=.
rewrite !big_cat.
have H: forall (a b b' c : real), b <= b' => a + b + c <= a + b' + c by smt().
apply H; clear H.
rewrite !big_cons !big_nil /predT /=.
apply lower_sum_ith_split.
- pose fxs := filter (fun (a : real) => a < x) xs.
  smt(mem_filter mem_last).
- pose fxs := filter ((<) x) xs.
  suff: head 0%r fxs \in fxs by smt(mem_filter).
  apply mem_head.
  smt(mem_filter mem_last).
apply (has_flb_in_subset f x0 _ x1) => //.
- suff: last 0%r (filter (fun (a : real) => a < x) xs) \in xs.
  + smt(partition_lb).
  pose fxs := filter (fun (a : real) => a < x) xs.
  smt(mem_filter mem_last).
- pose fxs := filter ((<) x) xs.
  suff: head 0%r fxs \in xs.
  + smt(partition_ub).
  suff: head 0%r fxs \in fxs by smt(mem_filter).
  apply mem_head.
  smt(mem_filter mem_last).
qed.

lemma lower_sum_const xs x0 x1 c :
  is_partition xs x0 x1 =>
  lower_sum (fun _ => c) xs = c * (x1 - x0).
proof.
move => ?.
rewrite /lower_sum big_mapT.
rewrite /(\o) /=.
pose h := fun i => c * nth 0%r xs i.
have ->: (fun x => lower_sum_ith (fun (_ : real) => c) (nth 0%r xs x, nth 0%r xs (x + 1))) =
  (fun i => h (i + 1) - h i).
- apply fun_ext => i.
  rewrite /lower_sum_ith /=.
  rewrite flgb_in_const /h.
  by algebra.
rewrite -telescoping_sum_down.
- smt(size_ge0).
smt(nth_last).
qed.

lemma has_lub_lower_sum f (x0 x1 : real) :
  x0 < x1 =>
  has_flb_in f x0 x1 =>
  has_fub_in f x0 x1 =>
  has_lub (is_lower_sum f x0 x1).
proof.
move => ???.
split; first by exists (lower_sum f [x0; x1]) => /#.
exists (flub_in f x0 x1 * (x1 - x0)) => y [xs [? <-]].
rewrite -(lower_sum_const xs) //=.
apply ler_sum_seq => [[xi xii] mem_x] _.
rewrite /lower_sum_ith /=.
apply ler_wpmul2r; first smt(lt_make_interval).
apply ler_fglb_in; first smt(lt_make_interval).
- apply (has_flb_in_subset _ x0 _ x1); smt(mem_interval_lb mem_interval_ub).
move => /= x lb_x ub_x.
apply flub_in_upper_bound; smt(mem_interval_lb mem_interval_ub).
qed.

op integral f x0 x1 = lub (is_lower_sum f x0 x1).

lemma lower_sum_le_integral (f : real -> real) (x0 x1 y : real) :
  x0 < x1 =>
  has_flb_in f x0 x1 =>
  has_fub_in f x0 x1 =>
  is_lower_sum f x0 x1 y =>
  y <= integral f x0 x1.
proof.
move => ????.
rewrite /integral.
apply lub_upper_bound => //.
exact has_lub_lower_sum.
qed.

lemma is_lower_sum_cat f (x1 x0 x2 aL aR : real) :
  x0 < x1 =>
  x1 < x2 =>
  is_lower_sum f x0 x1 aL =>
  is_lower_sum f x1 x2 aR =>
  is_lower_sum f x0 x2 (aL + aR).
proof.
move => ?? [xs0 [? <-]] [xs1 [? <-]].
exists (xs0 ++ behead xs1).
split.
- rewrite /is_partition.
  split.
  - apply (sorted_cat 0%r); smt(sorted_behead).
  split; first smt().
  split; first smt().
  rewrite last_cat /#.
rewrite /lower_sum -big_cat.
congr; apply (eq_from_nth (0%r, 0%r)).
- smt(size_cat size_map size_range size_ge0).
move => i rg_i.
rewrite size_map size_range size_cat /= in rg_i.
rewrite (nth_map 0) /=; first smt(size_range size_cat size_ge0).
rewrite nth_range /=; first smt(size_cat).
case (i < size xs0 - 1) => ?.
- rewrite !nth_cat.
  have -> /=: i < size xs0 by smt().
  have -> /=: i + 1 < size xs0 by smt().
  rewrite !size_map !size_range /=.
  have -> /=: i < max 0 (size xs0 - 1) by smt().
  rewrite (nth_map 0) /=; first smt(size_range size_ge0).
  by rewrite nth_range /#.
case (i = size xs0 - 1) => ?.
- rewrite !nth_cat.
  have -> /=: i < size xs0 by smt().
  have -> /=: !(i + 1 < size xs0) by smt().
  rewrite !size_map !size_range /=.
  have -> /=: !(i < max 0 (size xs0 - 1)) by smt().
  subst => /=.
  rewrite (nth_map 0) /=; first smt(size_range size_ge0).
  by rewrite nth_range; smt(size_ge0 last_nth).
rewrite !nth_cat.
have -> /=: !(i < size xs0) by smt().
have -> /=: !(i + 1 < size xs0) by smt().
rewrite !size_map !size_range /=.
have -> /=: !(i < max 0 (size xs0 - 1)) by smt().
rewrite (nth_map 0) /=; first smt(size_range size_ge0).
rewrite !nth_range /=; first smt().
smt(last_nth size_ge0).
qed.

lemma integral_const (c x0 x1 : real) :
  x0 < x1 =>
  integral (fun _ => c) x0 x1 = c * (x1 - x0).
proof.
move => ?.
rewrite /integral.
suff: is_lower_sum (fun (_ : real) => c) x0 x1 = pred1 (c * (x1 - x0)).
- move => ->.
  by rewrite lub1.
apply fun_ext => s /=.
rewrite /is_lower_sum /pred1.
case (s = (c * (x1 - x0))) => [-> | ?] /=.
- rewrite eqT.
  exists [x0; x1].
  split; first smt().
  apply lower_sum_const => /#.
suff: (forall xs, is_partition xs x0 x1 => lower_sum (fun _ => c) xs <> s) by smt().
move => xs ?.
rewrite (lower_sum_const xs x0 x1 c) /#.
qed.

lemma integral_le (f1 f2 : real -> real) (x0 x1 : real) :
  x0 < x1 =>
  has_flb_in f1 x0 x1 =>
  has_fub_in f2 x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f1 x <= f2 x) =>
  integral f1 x0 x1 <= integral f2 x0 x1.
proof.
move => ? has_flb_f1 has_fub_in_f2 le_f1_f2.
apply ler_lub.
- move => _ [xs [? <-]].
  exists (lower_sum f2 xs).
  split; first smt().
  exact (lower_sum_le f1 f2 xs x0 x1).
- smt(has_lub_lower_sum ler_has_flb).
- exists (lower_sum f1 [x0; x1]) => /#.
qed.

lemma integral_lb f (x0 x1 : real) :
  x0 < x1 =>
  has_flb_in f x0 x1 =>
  has_fub_in f x0 x1 =>
  fglb_in f x0 x1 * (x1 - x0) <= integral f x0 x1.
proof.
move => le_x0_x1 has_lb_f has_ub_f.
rewrite -(integral_const (fglb_in f x0 x1) x0 x1) //=.
apply integral_le => //=.
- by exists (fglb_in f x0 x1) => /#.
move => x lb_x ub_x /=.
exact fglb_in_lower_bound.
qed.

lemma integral_ub f (x0 x1 : real) :
  x0 < x1 =>
  has_flb_in f x0 x1 =>
  has_fub_in f x0 x1 =>
  integral f x0 x1 <= flub_in f x0 x1 * (x1 - x0).
proof.
move => ???.
rewrite -(integral_const (flub_in f x0 x1) x0 x1) //=.
apply integral_le => //=.
- by exists (flub_in f x0 x1) => /#.
move => x lb_x ub_x /=.
exact flub_in_upper_bound.
qed.

lemma integral_split_le f (x1 x0 x2 : real) :
  x0 < x1 => x1 < x2 =>
  has_flb_in f x0 x2 =>
  has_fub_in f x0 x2 =>
  integral f x0 x2 <= integral f x0 x1 + integral f x1 x2.
proof.
move => le_x0_x1 le_x1_x2 has_flb_f has_fub_f.
apply lub_le_ub.
- by apply has_lub_lower_sum => /#.
move => s is_lower_sum_s.
case is_lower_sum_s => xs [is_partition_xs is_sum_xs].
subst.
apply (ler_trans (lower_sum f (split_partition_to xs x1) + lower_sum f (split_partition_from xs x1))).
- by apply (split_lower_sum x1 f xs x0 x2) => /#.
suff: lower_sum f (split_partition_to xs x1) <= integral f x0 x1 /\
  lower_sum f (split_partition_from xs x1) <= integral f x1 x2 by smt().
split.
- apply lower_sum_le_integral => //=.
  + apply (has_flb_in_subset _ x0 x0 x2 x1) => /#.
  + smt().
  exists (split_partition_to xs x1) => /=.
  exact (is_partition_split_to xs x0 x1 x2).
- apply lower_sum_le_integral => //=.
  + smt(has_flb_in_subset).
  + smt().
  exists (split_partition_from xs x1) => /=.
  exact (is_partition_split_from xs x0 x1 x2).
qed.

lemma integral_split_ge f (x1 x0 x2 : real) :
  x0 < x1 => x1 < x2 =>
  has_flb_in f x0 x2 =>
  has_fub_in f x0 x2 =>
  integral f x0 x2 >= integral f x0 x1 + integral f x1 x2.
proof.
move => lt_x0_x1 lt_x1_x2 ??.
apply ler_sum_lub.
- exists (lower_sum f [x0; x1]).
  by exists ([x0; x1]) => /#.
- by apply has_lub_lower_sum; smt(has_flb_in_subset).
- by apply has_lub_lower_sum => /#.
smt(is_lower_sum_cat).
qed.

lemma integral_split f (x1 x0 x2 : real) :
  x0 < x1 => x1 < x2 =>
  has_flb_in f x0 x2 =>
  has_fub_in f x0 x2 =>
  integral f x0 x2 = integral f x0 x1 + integral f x1 x2.
proof. smt(integral_split_le integral_split_ge). qed.

(* -- main lemma so far -- *)

lemma fundamental_theorem_of_calculus (f : real -> real) (x x0 : real) :
  x0 < x =>
  continuous f =>
  differentiable_at (integral f x0) x /\
  derive (integral f x0) x = f x.
proof.
move => order_xs continuous_f.
suff: is_lim (slope (integral f x0) x) 0%r (f x).
- smt(lim_unique choicebP).
move => dy gt0_dy /=.
pose dy' := minr dy 0.5.
have [dx0 [gt0_dx0 [?[?[??]]]]] : exists dx, 0%r < dx /\
  has_fub_in f (x - dx) (x + dx) /\
  flub_in f (x - dx) (x + dx) < f x + dy' /\
  has_flb_in f (x - dx) (x + dx) /\ 
 f x - dy' < fglb_in f (x - dx) (x + dx).
- smt(continuous_flub_fglb).
pose dx1 := dy' / (2%r * `|f x| + dy').
pose dx2 := x - x0.
exists (minr dx0 (minr dx1 dx2)).
split => [/#| h ne0_h small_h].
rewrite /slope.
case (0%r < h) => [gt0_h|le0_h].
- rewrite (integral_split f x) //=; 1,2,3:smt(continuous_has_flb_in continuous_has_fub_in).
  have ->: integral f x0 x + integral f x (x + h) - integral f x0 x = integral f x (x + h) by smt().
  rewrite /"`|_|".
  case (0%r <= integral f x (x + h) / h - f x) => /= _.
  + rewrite ltr_subl_addl ltr_pdivr_mulr //=.
    apply (ltr_le_trans ((f x + dy') * h)); last first.
    * by rewrite ler_pmul2r /#.
    apply (ler_lt_trans (flub_in f x (x + h) * (x + h - x))); last first.
    * have ->: x + h - x = h by algebra.
      rewrite ltr_pmul2r //=.
      apply (ler_lt_trans (flub_in f (x - dx0) (x + dx0))); last by smt().
      by apply flub_in_subset => /#.
    apply (integral_ub f x (x + h)) => //=.
    * smt().
    * smt(has_flb_in_subset).
    * smt(has_fub_in_subset).
  + apply ltr_oppl.
    rewrite ltr_subr_addl ltr_pdivl_mulr //.
    apply (ler_lt_trans ((f x - dy') * h)); first by smt().
    apply (ltr_le_trans (fglb_in f x (x + h) * h)).
    * smt(ler_pmul2r fglb_in_subset).
    have ->: fglb_in f x (x + h) * h = fglb_in f x (x + h) * (x + h - x) by algebra.
    by apply (integral_lb f x (x + h)); smt(has_flb_in_subset has_fub_in_subset).
- rewrite (integral_split f (x + h) x0 x) //=;
    1,2,3,4:smt(continuous_has_flb_in continuous_has_fub_in).
  have -> /=: integral f x0 (x + h) - (integral f x0 (x + h) + integral f (x + h) x) =
    - integral f (x + h) x by smt().
  case (0%r <= (- integral f (x + h) x) / h - f x).
  + suff: (- integral f (x + h) x) / h - f x < dy by smt().
    apply (ler_lt_trans (flub_in f (x + h) x - f x)); last smt(flub_in_subset).
    suff: (- integral f (x + h) x) / h <= (flub_in f (x + h) x) by smt().
    rewrite ler_ndivr_mulr /=; first smt().
    apply ler_oppr.
    have ->: - flub_in f (x + h) x * h = flub_in f (x + h) x * (x - (x + h)) by algebra.
    apply integral_ub; smt(has_flb_in_subset has_fub_in_subset).
  + suff: integral f (x + h) x / h + f x < dy by smt().
    apply (ler_lt_trans (- fglb_in f (x + h) x + f x)); last smt(fglb_in_subset).
    suff: integral f (x + h) x / h <= - fglb_in f (x + h) x by smt().
    apply ler_ndivr_mulr; first smt().
    have ->: (- fglb_in f (x + h) x) * h = fglb_in f (x + h) x * (x - (x + h)) by algebra.
    apply integral_lb; smt(has_flb_in_subset has_fub_in_subset).
qed.
