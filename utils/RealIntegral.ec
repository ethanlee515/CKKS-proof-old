require import AllCore Real List StdBigop.
import RField.
import Bigreal Bigreal.BRA.
require import StdOrder.
import RealOrder.
require import RealLub RealFLub RealSeq.
require import ListExtras RealFlubExtras.
require import RealDerivative.

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
have [dx [gt0_dx [?[?[??]]]]] : exists dx, 0%r < dx /\
  has_fub_in f (x - dx) (x + dx) /\
  flub_in f (x - dx) (x + dx) < f x + dy /\
  has_flb_in f (x - dx) (x + dx) /\ 
  f x - dy < fglb_in f (x - dx) (x + dx).
- smt(continuous_flub_fglb).
exists (minr dx (x - x0)).
split => [/#| h ne0_h small_h].
rewrite /slope.
case (0%r < h) => [gt0_h|le0_h].
- rewrite (integral_split f x) //=; 1,2,3:smt(continuous_has_flb_in continuous_has_fub_in).
  have ->: integral f x0 x + integral f x (x + h) - integral f x0 x = integral f x (x + h) by smt().
  rewrite /"`|_|".
  case (0%r <= integral f x (x + h) / h - f x) => /= _.
  + rewrite ltr_subl_addl ltr_pdivr_mulr //=.
    apply (ltr_le_trans ((f x + dy) * h)); last first.
    * by rewrite ler_pmul2r /#.
    apply (ler_lt_trans (flub_in f x (x + h) * (x + h - x))); last first.
    * have ->: x + h - x = h by algebra.
      rewrite ltr_pmul2r //=.
      apply (ler_lt_trans (flub_in f (x - dx) (x + dx))); last by smt().
      by apply flub_in_subset => /#.
    apply (integral_ub f x (x + h)) => //=.
    * smt().
    * smt(has_flb_in_subset).
    * smt(has_fub_in_subset).
  + apply ltr_oppl.
    rewrite ltr_subr_addl ltr_pdivl_mulr //.
    apply (ler_lt_trans ((f x - dy) * h)); first by smt().
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
