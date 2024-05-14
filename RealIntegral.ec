require import AllCore Real List StdBigop.
import RField.
import Bigreal Bigreal.BRA.
require import StdOrder.
import RealOrder.

(* standard delta-epsilon definition of a limit *)
op is_lim (f : real -> real) (x y : real) =
  forall dy, 0%r < dy =>
  (exists dx, 0%r < dx /\ forall x', `|x' - x| < dx => `|f x' - y| < dy).

lemma lim_unique f x y0 y1 :
  is_lim f x y0 => is_lim f x y1 => y0 = y1.
proof.
move => is_lim_y0 is_lim_y1.
apply (absurd true) => [ne_ys /=|//].
pose eps := `|y0 - y1| / 4%r.
have is_lim_y0': exists dx, 0%r < dx /\ forall x', `|x' - x| < dx => `|f x' - y0| < eps.
- by apply is_lim_y0 => /#.
have is_lim_y1': exists dx, 0%r < dx /\ forall x', `|x' - x| < dx => `|f x' - y1| < eps.
- by apply is_lim_y1 => /#.
smt().
qed.

op lim_exists f x = exists y, is_lim f x y.
op lim f x = choiceb (is_lim f x) 0%r.

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

op lower_sums f x0 x1 y =
  exists xs,
  sorted Real.(<=) xs /\
  head xs = x0 /\
  last xs = x1 /\
  lower_sum f xs = y.

op integral f x0 x1 = lub (lower_sums f x0 x1).

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

op upper_sums f x0 x1 y =
  exists xs,
  sorted Real.(<=) xs /\
  head xs = x0 /\
  last xs = x1 /\
  upper_sum f xs = y.

(* greatest lower bound *)
op glb xs = - (lub (xs \o Real.([ - ]))).

op upper_integral f x0 x1 = glb (upper_sums f x0 x1).

op integrable f x0 x1 = (integral f x0 x1 = upper_integral f x0 x1).

op derive (f : real -> real) (x : real) = lim (fun dx => (f (x + dx) - f x) / dx) 0%r.


