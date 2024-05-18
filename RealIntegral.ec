require import AllCore Real List StdBigop.
import RField.
import Bigreal Bigreal.BRA.
require import StdOrder.
import RealOrder.
require import RealLub RealFLub.

(* Extending RealFlub for closed intervals *)

op glb xs = - (lub (xs \o Real.([ - ]))).

op has_flb (f : real -> real) = has_fub (Real.([ - ]) \o f).

op flub_in (f : real -> real) (x0 x1 : real) = flub (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0).

op fglb_in f x0 x1 = - (flub_in (Real.([ - ]) \o f) x0 x1).

op has_fub_in (f : real -> real) (x0 x1 : real) = has_fub (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0).

lemma ler_flub_in f g (x0 x1 : real) :
  x0 <= x1 =>
  has_fub_in g x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f x <= g x) =>
  flub_in f x0 x1 <= flub_in g x0 x1.
proof.
move => le_x0_x1 has_fub_g le_f_g.
apply ler_flub => /#.
qed.

op has_flb_in (f : real -> real) (x0 x1 : real) = has_fub_in (Real.([ - ]) \o f) x0 x1.

lemma has_flb_in_subset (f : real -> real) (x0 x0' x1 x1' : real) :
  x0 <= x0' =>
  x1' <= x1 =>
  has_flb_in f x0 x1 =>
  has_flb_in f x0' x1'.
proof.
move => ?? [r H].
case (x0' > x1') => ?.
- rewrite /has_flb_in /has_flb /(\o) /=.
  exists (- f x0') => /#.
exists r => /#.
qed.

lemma has_flb_in_ge (f g : real -> real) (x0 x1 : real) :
  has_flb_in f x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f x <= g x) =>
  has_flb_in g x0 x1.
proof.
rewrite /has_flb_in /has_flb /(\o) /=.
move => ??.
smt(ler_has_fub).
qed.

op is_fub_in f (x0 x1 r : real) = is_fub (fun x =>
  if x0 <= x /\ x <= x1 then f x else f x0) r.

lemma flub_in_le_ub f x0 x1 r :
  is_fub_in f x0 x1 r => flub_in f x0 x1 <= r.
proof. smt(flub_le_ub). qed.

lemma ler_fglb_in f g (x0 x1 : real) :
  x0 <= x1 =>
  has_flb_in f x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f x <= g x) =>
  fglb_in f x0 x1 <= fglb_in g x0 x1.
proof. smt(ler_flub_in). qed.

lemma flub_in_upper_bound f (x0 x1 x : real) :
  x0 <= x =>
  x <= x1 =>
  has_fub_in f x0 x1 =>
  f x <= flub_in f x0 x1.
proof. smt(flub_upper_bound). qed.

lemma fglb_in_lower_bound f (x0 x1 x : real) :
  x0 <= x =>
  x <= x1 =>
  has_flb_in f x0 x1 =>
  fglb_in f x0 x1 <= f x.
proof. by rewrite /has_flb_in /fglb_in /(\o); smt(flub_in_upper_bound). qed.

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

lemma fglb_in_subset f (x0 x1 x0' x1' : real) :
  x0 <= x0' =>
  x0' <= x1' =>
  x1' <= x1 =>
  has_flb_in f x0 x1 =>
  fglb_in f x0 x1 <= fglb_in f x0' x1'.
proof. smt(flub_in_subset). qed.

(* standard delta-epsilon definition of a limit *)
op is_lim (f : real -> real) (x y : real) =
  forall dy, 0%r < dy =>
  (exists dx, 0%r < dx /\ forall x', x' <> x => `|x' - x| < dx => `|f x' - y| < dy).

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

op lim_exists f x = exists y, is_lim f x y.
op lim f x = choiceb (is_lim f x) 0%r.
op continuous_at f x = (lim_exists f x /\ lim f x = f x).
op continuous f = forall x, continuous_at f x.

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

lemma continuous_fglb (f : real -> real) (x eps : real) :
  0%r < eps =>
  continuous_at f x =>
  exists dx,
  0%r < dx /\
  has_flb_in f (x - dx) (x + dx) /\
  fglb_in f (x - dx) (x + dx) > f x - eps.
proof. admitted.

lemma continuous_flub_fglb (f : real -> real) (x eps : real) :
  0%r < eps =>
  continuous_at f x =>
  exists dx,
  0%r < dx /\
  flub_in f (x - dx) (x + dx) < f x + eps /\
  fglb_in f (x - dx) (x + dx) > f x - eps.
proof.
move => gt0_eps continuous_f.
(*
apply (continuous_flub f x eps) in H'.
case H' => [dx0 ?].
have H': continuous_at f x by assumption.
apply (continuous_fglb f x eps) in H'.
case H' => [dx1 ?].
exists (minr dx0 dx1).
smt(flub_in_subset fglb_in_subset).
qed.
*)
admitted.

lemma continuous_has_fub_in f x0 x1 :
  continuous f =>
  has_fub_in f x0 x1.
proof. admitted.

lemma continuous_has_flb_in f x0 x1 :
  continuous f =>
  has_flb_in f x0 x1.
proof. admitted.

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

(*
lemma mem_is_partition_xx xs x a :
  is_partition xs x x =>
  a \in xs =>
  a = x.
proof.
move => is_partition_xs mem_a.
rewrite (nthP 0%r) in mem_a.
case mem_a => [i [rg_i <-]].
case (i = 0) => [/#|ne0_i].
case (i = size xs - 1) => [->|not_last_i].
- by rewrite nth_last /#.
suff: sorted Real.(<=) [x; nth 0%r xs i; x] by smt().
apply (subseq_sorted Real.(<=) _ _ xs); 1,3: smt().
apply subseqP.
exists (true :: ((nseq (i - 1) false) ++ ([true] ++ ((nseq (size xs - i - 2) false) ++ [true])))).
split; first smt(size_cat size_nseq).
have {3} ->: xs = (head 0%r xs) ::
  (take (i - 1) (drop 1 xs) ++ ([nth 0%r xs i] ++
  ((take (size xs - i - 2) (drop (i + 1) xs)) ++ [last 0%r xs]))).
- apply (eq_from_nth 0%r); first smt(size_cat size_take size_drop).
  smt(nth_take nth_drop size_take size_drop nth_cat nth_last).
rewrite mask_cons nseq1 cat1s /=.
smt(mask_cat size_nseq size_take size_drop mask_false cat0s).
qed.

lemma is_lower_sum_xx f xs x :
  is_partition xs x x =>
  lower_sum f xs = 0%r.
proof.
move => is_partition_xs.
rewrite /lower_sum.
apply big1_seq => //=.
move => i [_ rg_i].
rewrite mem_range in rg_i.
suff: nth 0%r xs (i + 1) = x /\ nth 0%r xs i = x by smt().
by split; apply (mem_is_partition_xx xs); smt(mem_nth).
qed.
*)

(*
lemma subseq_range xs i j :
  sorted Int.(<) xs =>
  i <= head i xs =>
  last i xs < j =>
  subseq xs (range i j).
proof.
move => sorted_xs ge_xs_i lt_xs_j.
apply subseqP.
admitted.
*)

lemma lower_sum_le (f1 f2 : real -> real) xs x0 x1 :
  is_partition xs x0 x1 =>
  has_flb_in f1 x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f1 x <= f2 x) =>
  lower_sum f1 xs <= lower_sum f2 xs.
proof.
move => is_partition_xs has_flb_f1 le_f1_f2.
rewrite /lower_sum.
apply ler_sum_seq => /= [[x_i x_ii] mem_x_i] _.
print lower_sum_ith.
suff: fglb_in f1 x_i x_ii <= fglb_in f2 x_i x_ii.
- suff: x_i <= x_ii by smt().
  admit. (* Property of make_intervals and is_partition... *)
  (*
  suff: sorted Real.(<=) [nth 0%r xs i; nth 0%r xs (i + 1)] by smt().
  case is_partition_xs => [sortd_xs [lt_x0_x1 [??]]]; subst.
  apply (subseq_sorted _ _ _ xs) => //=; first smt().
  pose f := (nth 0%r xs).
  have ->: [nth 0%r xs i; nth 0%r xs (i + 1)] = map f [i; i + 1] by smt().
  have ->: xs = map f (range 0 (size xs)).
  + apply (eq_from_nth 0%r); first smt(size_map size_range size_ge0).
    move => j rg_j.
    rewrite (nth_map 0 0%r); first smt(size_map size_range size_ge0).
    by rewrite nth_range.
  apply map_subseq.
  by apply subseq_range; smt(mem_range).
  *)
have ?: (x_i >= x0).
- admit.
have ?: (x_ii <= x1).
- admit.
apply ler_fglb_in; last smt().
- admit.
exact (has_flb_in_subset _ x0 _ x1).
qed.

op split_partition_to (xs : real list) (x : real) =
  rcons (filter (fun a => a < x) xs) x.

op split_partition_from (xs : real list) (x : real) =
  x :: (filter (fun a => x < a) xs).

(*
lemma sorted_rcons dfl (e : 'a -> 'a -> bool) xs x :
  sorted e xs =>
  (xs <> [] => e (last dfl xs) x) =>
  sorted e (rcons xs x).
proof. admitted.
*)

(*
lemma filter_last (xs : 'a list) dfl f :
  f (last dfl xs) =>
  last dfl (filter f xs) = last dfl xs.
proof.
case (xs = []); first smt().
move => not_nil_xs f_last.
print filter.
admitted.
*)

lemma sorted_split_partition_to xs x :
  xs <> [] =>
  x >= head 0%r xs =>
  sorted Real.(<) xs =>
  sorted Real.(<) (split_partition_to xs x).
proof.
move => ???.
rewrite /split_partition_to.
(*
apply (sorted_rcons 0%r).
- apply sorted_filter => /#.
pose ys := filter (fun a => a <= x) xs.
move => ?.
suff: last 0%r ys \in ys by smt(mem_filter).
rewrite (last_nth 0%r 0%r ys).
smt(mem_nth size_ge0).
qed.
*)
admitted.

lemma head_split_partition_to xs x :
  xs <> [] =>
  x >= head 0%r xs =>
  head 0%r (split_partition_to xs x) = head 0%r xs.
proof. admitted.

lemma last_split_partition_to xs x :
  last 0%r (split_partition_to xs x) = x.
proof. admitted.

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
by rewrite last_split_partition_to.
qed.

lemma sorted_split_partition_from xs x :
  xs <> [] =>
  x >= head 0%r xs =>
  sorted Real.(<=) xs =>
  sorted Real.(<=) (split_partition_from xs x).
proof.
admitted.

lemma head_split_partition_from xs x :
  head 0%r (split_partition_from xs x) = x.
proof. admitted.

lemma last_split_partition_from xs x :
  xs <> [] =>
  x <= last 0%r xs =>
  last 0%r (split_partition_from xs x) = last 0%r xs.
proof. admitted.

lemma is_partition_split_from xs (x0 x1 x2 : real) :
  x0 < x1 =>
  x1 < x2 =>
  is_partition xs x0 x2 =>
  is_partition (split_partition_from xs x1) x1 x2.
proof. admitted.

lemma cat_split_intervals_mem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x \in xs =>
  make_intervals (split_partition_to xs x) ++
  make_intervals (split_partition_from xs x)
  = make_intervals xs.
proof. admitted.

lemma cat_split_intervals_nomem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x0 < x => x < x1 =>
  !(x \in xs) =>
  make_intervals (split_partition_to xs x) ++
  make_intervals (split_partition_from xs x) =
  let lst1 = filter (fun a => a < x) xs in
  let lst2 = filter (fun a => x < a) xs in
  make_intervals lst1 ++ [(last 0%r lst1, x); (x, head 0%r lst2)] ++ make_intervals lst2.
proof. admitted.

lemma split_intervals_nomem xs x0 x1 x :
  is_partition xs x0 x1 =>
  x0 < x => x < x1 =>
  !(x \in xs) =>
  make_intervals xs =
  let lst1 = filter (fun a => a < x) xs in
  let lst2 = filter (fun a => x < a) xs in
  make_intervals lst1 ++ [(last 0%r lst1, head 0%r lst2)] ++ make_intervals lst2.
proof. admitted.

lemma lower_sum_ith_split f (x0 x1 x2 : real) :
  x0 < x1 =>
  x1 < x2 =>
  has_flb_in f x0 x2 =>
  lower_sum_ith f (x0, x2) <=
  lower_sum_ith f (x0, x1) + lower_sum_ith f (x1, x2).
proof. admitted.

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
- admit.
- admit.
- admit.
qed.

lemma has_lub_lower_sum f x0 x1 :
  has_flb_in f x0 x1 =>
  has_lub (is_lower_sum f x0 x1).
proof.
print has_lub.
admitted.

op integral f x0 x1 = lub (is_lower_sum f x0 x1).

(*
lemma integral_xx f x :
  integral f x x = 0%r.
proof. admitted.
*)

lemma lower_sum_le_integral f x0 x1 y :
  is_lower_sum f x0 x1 y =>
  y <= integral f x0 x1.
proof.
print integral.
admitted.

lemma is_lower_sum_cat f (x1 x0 x2 aL aR : real) :
  x0 < x1 =>
  x1 < x2 =>
  is_lower_sum f x0 x1 aL =>
  is_lower_sum f x1 x2 aR =>
  is_lower_sum f x0 x2 (aL + aR).
proof.
admitted.

lemma integral_const_le (c x0 x1 : real) :
  x0 < x1 =>
  integral (fun _ => c) x0 x1 <= c * (x1 - x0).
proof.
move => ?.
admitted.

lemma integral_const_ge (c x0 x1 : real) :
  x0 < x1 =>
  integral (fun _ => c) x0 x1 >= c * (x1 - x0).
proof.
move => ?.
admitted.

lemma integral_const (c x0 x1 : real) :
  x0 < x1 =>
  integral (fun _ => c) x0 x1 = c * (x1 - x0).
proof.
move => ?.
suff: integral (fun _ => c) x0 x1 <= c * (x1 - x0) /\
  integral (fun _ => c) x0 x1 >= c * (x1 - x0) by smt().
split; first exact integral_const_le.
exact integral_const_ge.
qed.

lemma integral_le (f1 f2 : real -> real) (x0 x1 : real) :
  has_flb_in f1 x0 x1 =>
  (forall x, x0 <= x => x <= x1 => f1 x <= f2 x) =>
  integral f1 x0 x1 <= integral f2 x0 x1.
proof.
move => has_flb_f1 le_f1_f2.
apply ler_lub; 2,3:smt(has_lub_lower_sum has_flb_in_ge).
move => s is_lower_sum_s.
case is_lower_sum_s => [xs [??]].
exists (lower_sum f2 xs).
split; first smt().
subst.
exact (lower_sum_le f1 f2 xs x0 x1).
qed.

lemma integral_lb f (x0 x1 : real) :
  x0 < x1 =>
  fglb_in f x0 x1 * (x1 - x0) <= integral f x0 x1.
proof.
move => le_x0_x1.
rewrite -(integral_const (fglb_in f x0 x1) x0 x1) //=.
apply integral_le => /=.
 - admit. (* has_flb_in assumption *)
move => x lb_x ub_x /=.
apply fglb_in_lower_bound => //.
admitted.

lemma integral_ub f (x0 x1 : real) :
  x0 < x1 =>
  has_flb_in f x0 x1 =>
  integral f x0 x1 <= flub_in f x0 x1 * (x1 - x0).
proof.
move => ??.
rewrite -(integral_const (flub_in f x0 x1) x0 x1) //=.
apply integral_le => //= ???.
apply flub_in_upper_bound => //.
admitted.

op differential (f : real -> real) (x dx : real) = (f (x + dx) - f x) / dx.

op derive f x = lim (differential f x) 0%r.

op differentiable_at f x = lim_exists (differential f x) 0%r.

lemma integral_split_le f (x1 x0 x2 : real) :
  x0 < x1 => x1 < x2 =>
  has_flb_in f x0 x2 =>
  integral f x0 x2 <= integral f x0 x1 + integral f x1 x2.
proof.
move => le_x0_x1 le_x1_x2 has_flb_f.
apply lub_le_ub; first exact has_lub_lower_sum.
move => s is_lower_sum_s.
case is_lower_sum_s => xs [is_partition_xs is_sum_xs].
subst.
apply (ler_trans (lower_sum f (split_partition_to xs x1) + lower_sum f (split_partition_from xs x1))).
- by apply (split_lower_sum x1 f xs x0 x2) => /#.
suff: lower_sum f (split_partition_to xs x1) <= integral f x0 x1 /\
  lower_sum f (split_partition_from xs x1) <= integral f x1 x2 by smt().
split.
- apply lower_sum_le_integral.
  exists (split_partition_to xs x1) => /=.
  exact (is_partition_split_to xs x0 x1 x2).
- apply lower_sum_le_integral.
  exists (split_partition_from xs x1) => /=.
  exact (is_partition_split_from xs x0 x1 x2).
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

lemma integral_split_ge f (x1 x0 x2 : real) :
  x0 < x1 => x1 < x2 =>
  has_flb_in f x0 x2 =>
  integral f x0 x2 >= integral f x0 x1 + integral f x1 x2.
proof.
move => lt_x0_x1 lt_x1_x2 has_flb_f.
apply ler_sum_lub.
- exists (lower_sum f [x0; x1]) => /#.
- smt(has_lub_lower_sum has_flb_in_subset).
- exact has_lub_lower_sum.
smt(is_lower_sum_cat).
qed.

lemma integral_split f (x1 x0 x2 : real) :
  x0 < x1 => x1 < x2 =>
  has_flb_in f x0 x2 =>
  integral f x0 x2 = integral f x0 x1 + integral f x1 x2.
proof. smt(integral_split_le integral_split_ge). qed.

lemma fundamental_theorem_of_calculus (f : real -> real) (x x0 : real) :
  x0 < x =>
  continuous f =>
  differentiable_at (integral f x0) x /\
  derive (integral f x0) x = f x.
proof.
move => order_xs continuous_f.
suff: is_lim (differential (integral f x0) x) 0%r (f x).
- smt(lim_unique choicebP).
move => dy gt0_dy /=.
pose dy' := minr dy 0.5.
(**
have H: continuous_at f x by smt().
apply (continuous_flub_fglb f x dy') in H.
case H => [dx0 [gt0_dx0 [ub_f lb_f]]].
pose dx1 := dy' / (2%r * `|f x| + dy').
pose dx2 := x - x0.
exists (minr dx0 (minr dx1 dx2)).
split => [/#| h ne0_h small_h].
rewrite /differential.
case (0%r < h) => [gt0_h|le0_h].
- rewrite (integral_split f x); 1,2,3: smt(continuous_has_flb_in).
  have ->: integral f x0 x + integral f x (x + h) - integral f x0 x = integral f x (x + h) by smt().
  case (0%r <= integral f x (x + h) / h - f x); admit.
  (* broken due to added flb assumption... *)
  (*
  + smt(ler_pdivr_mulr integral_ub flub_in_subset).
  + smt(ler_pdivl_mulr integral_lb fglb_in_subset). *)
- rewrite (integral_split f (x + h) x0 x); 1,2,3:smt(continuous_has_flb_in).
  have -> /=: integral f x0 (x + h) - (integral f x0 (x + h) + integral f (x + h) x) = - integral f (x + h) x by smt().
  case (0%r <= (- integral f (x + h) x) / h - f x).
  + suff: (- integral f (x + h) x) / h - f x < dy by smt().
    apply (ler_lt_trans (flub_in f (x + h) x - f x)); last smt(flub_in_subset).
    suff: (- integral f (x + h) x) / h <= (flub_in f (x + h) x) by smt().
    admit. (* broken due to added flb assumption *)
    (* by apply ler_ndivr_mulr; smt(integral_ub). *)
  + suff: integral f (x + h) x / h + f x < dy by smt().
    apply (ler_lt_trans (- fglb_in f (x + h) x + f x)); last smt(fglb_in_subset).
    suff: integral f (x + h) x / h <= - fglb_in f (x + h) x by smt().
    apply ler_ndivr_mulr; smt(integral_lb).
qed.
**)
admitted.
