require import AllCore RealExp.
require import ListExtras RealFlubExtras.
require import StdOrder.
import RealOrder.
require import RealSeq.
require import BolzanoWeierstrass.

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

lemma differentiable_is_continuous f x :
  differentiable_at f x =>
  continuous_at f x.
proof. admitted.

lemma derive_lim_c f c :
  differentiable_at f c =>
  derive f c = lim (fun x => (f x - f c) / (x - c)) c.
proof. admitted.

lemma chain_rule f g x :
  differentiable_at f x =>
  differentiable_at g (f x) =>
  derive (g \o f) x = derive g (f x) * derive f x.
proof.
move => ??.
admitted.

lemma derive_exp x :
  derive RealExp.exp x = exp x.
proof. admitted.

lemma derive_ln x :
  0%r < x =>
  derive ln x = 1%r / x.
proof. admitted.

lemma differentiable_compose f g x :
  differentiable_at g x =>
  differentiable_at f (g x) =>
  differentiable_at (f \o g) x.
proof.
admitted.

lemma derive_mult f g x :
  derive (f \o g) x =
  derive f x * g x + f x * derive g x.
proof.
admitted.
