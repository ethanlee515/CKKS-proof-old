require import AllCore Real List StdBigop.
import RField.
import Bigreal Bigreal.BRA.
require import StdOrder.
import RealOrder.
require import RealFLub.

(* Extending RealFlub for closed intervals *)

op flub_in (f : real -> real) x0 x1 = flub (fun x => f x * b2r (x0 <= x /\ x <= x1)).

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

op lower_sum f xs =
  bigi predT
  (fun i =>
    let x0 = nth 0%r xs i in
    let x1 = nth 0%r xs (i + 1) in
    let y0 = f x0 in
    let y1 = f x1 in
    let y = minr y0 y1 in
    y * (x1 - x0))
  0 (size xs - 1).

op is_lower_sum f x0 x1 y =
  exists xs,
  sorted Real.(<=) xs /\
  xs <> [] /\
  head 0%r xs = x0 /\
  last 0%r xs = x1 /\
  lower_sum f xs = y.

op integral f x0 x1 = lub (is_lower_sum f x0 x1).

lemma lower_sum_le_integral f x0 x1 y :
  is_lower_sum f x0 x1 y =>
  y <= integral f x0 x1.
proof.
admitted.

op upper_sum f xs =
  bigi predT
  (fun i =>
    let x0 = nth 0%r xs i in
    let x1 = nth 0%r xs (i + 1) in
    let y0 = f x0 in
    let y1 = f x1 in
    let y = maxr y0 y1 in
    y * (x1 - x0))
  0 (size xs - 1).

op is_upper_sum f x0 x1 y =
  exists xs,
  sorted Real.(<=) xs /\
  xs <> [] /\
  head 0%r xs = x0 /\
  last 0%r xs = x1 /\
  upper_sum f xs = y.

(* greatest lower bound *)
op glb xs = - (lub (xs \o Real.([ - ]))).

op upper_integral f x0 x1 = glb (is_upper_sum f x0 x1).

op integrable f = forall x0 x1, (integral f x0 x1 = upper_integral f x0 x1).

op differential (f : real -> real) (x dx : real) = (f (x + dx) - f x) / dx.

op derive f x = lim (differential f x) 0%r.

op differentiable_at f x = lim_exists (differential f x) 0%r.

lemma integral_xx f x :
  integral f x x = 0%r.
proof. admitted.

lemma integral_split f (x1 x0 x2 : real) :
  x0 <= x1 => x1 <= x2 =>
  integral f x0 x2 = integral f x0 x1 + integral f x1 x2.
proof. admitted.

op fglb_in f x0 x1 = - (flub_in (f \o Real.([ - ])) x0 x1).

lemma continuous_flub_fglb (f : real -> real) (x eps : real) :
  continuous_at f x =>
  exists dx,
  0%r < dx /\
  flub_in f (x - dx) (x + dx) < (f x + eps) /\
  fglb_in f (x - dx) (x + dx) > f x - eps.
proof. admitted.

lemma flub_in_subset f (x0 x1 x0' x1' : real) :
  x0 <= x0' =>
  x1' <= x1 =>
  x0' <= x1' =>
  flub_in f x0' x1' <= flub_in f x0 x1.
proof. admitted.

lemma fglb_in_subset f (x0 x1 x0' x1' : real) :
  x0 <= x0' =>
  x1' <= x1 =>
  x0' <= x1' =>
  fglb_in f x0 x1 <= fglb_in f x0' x1'.
proof. admitted.

lemma integral_ub f x0 x1 :
  integral f x0 x1 <= flub_in f x0 x1 * (x1 - x0).
proof. admitted.

lemma integral_lb f x0 x1 :
  fglb_in f x0 x1 * (x1 - x0) <= integral f x0 x1.
proof. admitted.

lemma fundamental_theorem_of_calculus (f : real -> real) (x x0 : real) :
  x0 < x =>
  continuous_at f x =>
  differentiable_at (integral f x0) x /\
  derive (integral f x0) x = f x.
proof.
move => order_xs continuous_f.
suff: is_lim (differential (integral f x0) x) 0%r (f x).
- smt(lim_unique choicebP).
move => dy gt0_dy /=.
pose dy' := minr dy 0.5.
apply (continuous_flub_fglb f x dy') in continuous_f.
case continuous_f => [dx0 [gt0_dx0 [ub_f lb_f]]].
pose dx1 := dy' / (2%r * `|f x| + dy').
pose dx2 := x - x0.
exists (minr dx0 (minr dx1 dx2)).
split => [/#| h ne0_h small_h].
rewrite /differential.
case (0%r < h) => [gt0_h|le0_h].
- rewrite (integral_split f x); 1,2:smt().
  have ->: integral f x0 x + integral f x (x + h) - integral f x0 x = integral f x (x + h) by smt().
  case (0%r <= integral f x (x + h) / h - f x).
  + smt(ler_pdivr_mulr integral_ub flub_in_subset).
  + smt(ler_pdivl_mulr integral_lb fglb_in_subset).
- rewrite (integral_split f (x + h) x0 x); 1,2:smt().
  have -> /=: integral f x0 (x + h) - (integral f x0 (x + h) + integral f (x + h) x) = - integral f (x + h) x by smt().
  case (0%r <= (- integral f (x + h) x) / h - f x).
  + suff: (- integral f (x + h) x) / h - f x < dy by smt().
    apply (ler_lt_trans (flub_in f (x + h) x - f x)); last smt(flub_in_subset).
    suff: (- integral f (x + h) x) / h <= (flub_in f (x + h) x) by smt().
    by apply ler_ndivr_mulr; smt(integral_ub).
  + suff: integral f (x + h) x / h + f x < dy by smt().
    apply (ler_lt_trans (- fglb_in f (x + h) x + f x)); last smt(fglb_in_subset).
    suff: integral f (x + h) x / h <= - fglb_in f (x + h) x by smt().
    apply ler_ndivr_mulr; smt(integral_lb).
qed.
