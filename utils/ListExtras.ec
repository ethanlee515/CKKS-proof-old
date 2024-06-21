require import AllCore List.

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
