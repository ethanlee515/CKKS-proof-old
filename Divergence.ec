require import AllCore Distr.
require import RealExp RealSeries.
require import RealIntegral.
require import RealDerivative.

op kl_divergence (p q : 'a distr) = sum (fun x => mu1 p x * ln (mu1 p x / mu1 q x)).

op renyi_divergence (alpha : real) (p q : 'a distr) = ln (
  sum (fun x => (mu1 p x) ^ alpha * (mu1 q x) ^ (1%r - alpha))) / (alpha - 1%r).

lemma derive_at_root f r :
  f r = 0%r =>
  differentiable_at f r =>
  derive f r = lim (fun x => f x / (x - r)) r.
proof. admitted.

op differentiable f = forall x, differentiable_at f x.

op convergeto_pointwise (f_ : int -> real -> real) (f : real -> real) =
  forall x, convergeto (fun k => f_ k x) (f x).

op convergeto_uniformly (f_ : int -> real -> real) (g : real -> real) =
  forall eps, 0%r < eps =>
  exists (N : int), forall n x, N <= n => `|f_ n x - g x| < eps.

lemma converge_derivatives f_k f g :
  convergeto_pointwise f_k f =>
  (forall k, differentiable (f_k k)) =>
  convergeto_uniformly (fun k => derive (f_k k)) g =>
  derive f = g.
proof. admitted.

op fsum (f_k : int -> real -> real) x = sum (fun k => f_k k x).
op fsummable (f_k : int -> real -> real) = forall x, summable (fun k => f_k k x).
op fsum_n f_k n x = bigi (fun k => f_k k x) 0 n.

lemma derive_fsum f_ :
  fsummable f_ =>
  (forall k, differentiable (f_ k)) =>
  convergeto_uniformly (fun k => derive (f_ k)) (fun _ => 0%r) =>
  derive (fsum f_) = fsum (fun k => derive (f_ k)).
proof. admitted.

lemma renyi_to_kl (p q : 'a distr) :
  lim_exists (fun alpha => renyi_divergence alpha p q) 1%r =>
  lim (fun alpha => renyi_divergence alpha p q) 1%r = kl_divergence p q.
proof.
move => ?.
rewrite /renyi_divergence.
rewrite -derive_at_root /=.
- admit.
- admit.
rewrite chain_rule /=.
- admit.
- admit.
rewrite derive_ln.
- admit.
admitted.
