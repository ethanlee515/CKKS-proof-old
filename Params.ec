require import AllCore.

(* poly degree *)
op n : {int | 0 < n} as gt0_n.
(* modulus *)
op q : {int | 2 <= q} as ge2_q.
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
