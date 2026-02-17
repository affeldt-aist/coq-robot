From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum matrix interval.
From mathcomp Require Import poly archimedean generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
Require Import tilt_analysis ode_common ode_contfun ode.

(**md**************************************************************************)
(* # ODE wip                                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

(* global Lipschitz condition -> the solution is always in a set where phi is Lipschitz *)
Section cauchy_lipschitzT.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}) (rho : {posnum R}).
Hypothesis rho1 : rho%:num < 1.
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
(* lip2 and cont1 hold for any vector *)
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_[set: 'rV_n] (phi x)}.
Hypothesis cont1 : {in [set: 'rV_n], forall y, {within `[a, b], continuous phi ^~ y}}.

Let B := closed_ball u0 r%:num.

Let lip2' : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Proof.
move=> t tab /= [x y] [/= Bx By].
have : ([set: 'rV_n] `*` [set: 'rV_n]) (x, y) by rewrite setXTT.
by move=> /(lip2 tab); exact.
Qed.

Let cont1' : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Proof. by move=> t tab /=; apply: cont1; rewrite in_setT. Qed.

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).

Definition lipschitzT_solution_f : continuousFunType `[a, a + safe_dist] [set: 'rV[R]_n] :=
  repr (picard_fix ab k0 lip2' cont1' rho1).

Lemma lipschitzT_solution :
  is_sol_on phi u0 a (BLeft (a + safe_dist)) lipschitzT_solution_f.
Proof.
apply/(integral_sol_iff_sol (k:=k) (r:=r)) => //.
- by rewrite gt_eqF.
- by rewrite ltDl_safe_dist.
- move=> t td.
  apply: lip2'.
  by apply: subset_itvl td; rewrite bnd_simp -lerBrDl safe_dist_itv.
- move=> /= x xB.
  apply/continuous_subspaceW/cont1 => //.
    by apply: subset_itvl => /=; rewrite bnd_simp -lerBrDl safe_dist_itv.
  by rewrite inE.
- rewrite /local_solution.
  exact: cts_fun.
- by move => _ [t tad] <-; exact: cauchy_lipschitz_in_cball.
- exact: cauchy_lipschitz_integral_version.
Qed.

Lemma lipschitzT_solution_stays_in_ball :
  {in `[a, a + safe_dist], forall t, closed_ball u0 r%:num (lipschitzT_solution_f t)}.
Proof. by move=> t; rewrite inE => /cauchy_lipschitz_in_cball; exact. Qed.

Lemma lipschitzT_solution_continuous :
  {within `[a, a + safe_dist], continuous lipschitzT_solution_f}.
Proof. exact: cts_fun. Qed.

Let f := lipschitzT_solution_f.

Theorem lipschitzT_cauchy_lipschitz_local :
  safe_dist > 0 /\
  is_sol_on phi u0 a (BLeft (a + safe_dist)) f /\
  {in `[a, a + safe_dist], forall t, closed_ball u0 r%:num (f t)}.
Proof.
split; first exact: safe_dist_gt0.
split.
- exact: lipschitzT_solution.
- exact: lipschitzT_solution_stays_in_ball.
Qed.

End cauchy_lipschitzT.

Lemma min2r (T : realDomainType) (a b c : T) : a <= c ->
  (Num.min a b <= Num.min c b).
Proof.
rewrite /minr; have [ab|ba] := ltP a b; have [cb|bc] := ltP c b => //.
- by move=> _; exact: ltW.
- by move=> /le_lt_trans => /(_ _ cb); rewrite ltNge ba.
Qed.

Section itv_partition_lemmas.
Context {R : realType}.
Variables a b : R.
Hypothesis ab : a < b.

Lemma itv_partition_ex s x : itv_partition a b s ->
  a <= x <= b ->
  let I i := `[nth b (a :: s) i, nth b (a :: s) i.+1]%R in
  exists2 i, (i < size s)%N & x \in I i.
Proof.
elim: s a b ab x => [a0 b0 a0b0 x|s0 s1 ih a0 b0 a0b0 x abs].
  move/itv_partition_nil => a0E.
  by rewrite a0E ltxx in a0b0.
move=> /andP[a0x xb0].
have [s0s1 /= /eqP s0s1b0] := itv_partition_cons abs.
rewrite -s0s1b0.
destruct s1 as [|s2 s3].
  exists O => //.
  rewrite in_itv/= a0x/=.
  case: abs => /=.
  by rewrite andbT => a0s0 /eqP ->.
have s0b0 : s0 < b0.
  have [] := itv_partition_cons abs.
  move/order_path_min => /(_ lt_trans)/allP + /eqP <-.
  apply.
  by rewrite /= mem_last.
have [xs0|s0x] := ltP x s0.
  exists 0 => //=.
  by rewrite in_itv/= a0x (ltW xs0).
have := ih s0 b0 s0b0 x (itv_partition_cons abs).
rewrite s0x xb0 => /(_ isT)[i is3 Hx].
exists i.+1 => //=.
suff : b0 = last s2 s3 by move=> <-.
have := itv_partition_cons abs.
by case => _ /= /eqP.
Qed.

Lemma itv_partition_lt (delta : R) : 0 < delta ->
  exists (delta' : R) s,
  0 < delta' < delta /\
  itv_partition a b s /\
  forall i, (i < size s)%N -> nth b (a :: s) i.+1 - nth b (a :: s) i < delta.
Proof.
move=> delta0.
pose delta' := delta / 2.
have delta'delta : delta' < delta.
  by rewrite gtr_pMr// invf_lt1// ltr1n.
have delta'0 : 0 < delta' by rewrite divr_gt0.
have [Hnat_num|Hnat_num] := pselect ((b - a) / delta' \is a nat_num).
  pose m := truncn ((b - a) / delta').
  have m0 : (0 < m)%N.
    rewrite -(ltr_nat R).
    move: Hnat_num; rewrite natrEtruncn => /eqP; rewrite -/m => ->.
    by rewrite divr_gt0// subr_gt0.
  have bE : a + delta' *+ m = b.
    rewrite -mulr_natl.
    move: Hnat_num; rewrite natrEtruncn => /eqP; rewrite -/m => ->.
    by rewrite -mulrA mulVf ?mulr1 ?gt_eqF// subrKC.
  pose s := (seq.map (fun k => a + delta' *+ k) (iota 1 m)).
  have lasts : last b s = b.
    rewrite /s -bE (@last_map _ _ (fun k => a + delta' *+ k)).
    rewrite (_ : last _ _ = m)//.
    rewrite {2}(_ : m = m.-1 + 1)%N//; last by rewrite addn1 prednK.
    by rewrite iotaD/= cats1 last_rcons add1n prednK.
  (*  a
      a + delta'
      ...
      a + m * delta' = b
      size = m *)
  have sm : size s = m by rewrite /s size_map size_iota.
  have nth_itv_partition :
      (forall i, (i <= m)%N -> nth b (a :: s) i = a + delta' *+ i).
    move=> i im.
    rewrite /s; destruct i as [|i] => /=.
      by rewrite mulr0n addr0.
    by rewrite (nth_map 0) ?size_iota// nth_iota.
  exists delta', s.
  split.
    by apply/andP; split.
  split.
    split; last first.
      rewrite -nth_last -lasts -nth_last; apply/eqP.
      apply: set_nth_default.
      by rewrite sm prednK.
    apply/(pathP b) => i si.
    destruct i as [|i] => /=.
      by rewrite (nth_map 0) ?size_iota// nth_iota// addn0 mulr1n ltrDl.
    have im : (i < m)%N by rewrite -sm (leq_trans _ si).
    rewrite /s (nth_map 0) ?size_iota// nth_iota//.
    rewrite (nth_map 0) ?size_iota//; last by rewrite -sm.
    rewrite nth_iota; last by rewrite -sm.
    by rewrite !add1n ltrD2l [in ltRHS]mulrS ltrDr.
  move=> i si.
  rewrite nth_itv_partition; last by rewrite -sm.
  rewrite nth_itv_partition; last by rewrite -sm ltnW.
  by rewrite mulrS (addrCA _ delta') addrK.
pose m := (truncn ((b - a) / delta')).+1.
pose s := rcons (seq.map (fun k => a + delta' *+ k) (iota 1 m.-1)) b.
have m0 : (0 < m)%N by [].
(* a
   a + delta'
   ...
   a + (m - 1) * delta'
   b
   size = m + 1 *)
have sm1 : size s = m by rewrite /s size_rcons size_map size_iota prednK.
have nth_itv_partition :
    (forall i, (i < m)%N -> nth b (a :: s) i = a + delta' *+ i).
  move=> i im.
  rewrite /s; destruct i as [|i] => /=.
    by rewrite mulr0n addr0.
  rewrite nth_rcons size_map size_iota.
  case: ifPn => im1.
    by rewrite (nth_map 0) ?size_iota// nth_iota.
  move: im1.
  by rewrite -(ltn_add2r 1) !addn1 -/m im.
have asrhok_last : nth b (a :: s) m - nth b (a :: s) m.-1 <= delta'.
  rewrite {1}(_ : m = (size (a :: s)).-1)// nth_last.
  rewrite {1}/s /= last_rcons.
  rewrite nth_itv_partition//.
  rewrite opprD addrA lerBlDl -mulrSr -/m.
  rewrite -mulr_natl -ler_pdivrMr//.
  by rewrite /m ltW// real_truncnS_gt// num_real.
exists delta', s.
split.
  by apply/andP; split.
split.
  split; last by rewrite last_rcons.
  apply/(pathP b) => i si.
  destruct i as [|i] => /=.
    rewrite /s nth_rcons size_map size_iota.
    case: ifPn => m10.
      by rewrite (nth_map 0) ?size_iota// nth_iota// addn0 mulr1n ltrDl.
    by rewrite if_same.
  rewrite /s !nth_rcons size_map size_iota.
  have im1 : (i < m.-1)%N.
    by rewrite -(ltn_add2r 1) !addn1 prednK// -sm1.
  rewrite im1 (nth_map 0) ?size_iota// nth_iota//.
  case: ifPn => i1m1.
    rewrite (nth_map 0) ?size_iota//.
    by rewrite nth_iota// !add1n ltrD2l [in ltRHS]mulrS ltrDr.
  rewrite if_same add1n.
  have {}i1m1 : i.+1 = m.-1 by apply/eqP; rewrite eqn_leq im1 leqNgt i1m1.
  rewrite i1m1.
  rewrite -ltrBrDl -mulr_natl -ltr_pdivlMr//.
  rewrite /m/= lt_neqAle.
  apply/andP; split.
    by rewrite -natrEtruncn//; exact/negP.
  by rewrite truncn_le divr_ge0// ltW// subr_gt0.
move=> i.
rewrite leq_eqVlt => /predU1P[i1s|si1].
  rewrite i1s.
  rewrite (_ : (size s) = (size (a :: s)).-1)//.
  rewrite nth_last/= last_rcons.
  rewrite nth_itv_partition//; last by rewrite -sm1 -i1s.
  rewrite (le_lt_trans _ delta'delta)//.
  rewrite opprD addrA lerBlDl -mulrSr -/m.
  rewrite -mulr_natl -ler_pdivrMr// /m ltW// i1s sm1.
  by rewrite real_truncnS_gt// num_real.
rewrite nth_itv_partition//; last by rewrite -sm1.
rewrite nth_itv_partition//; last by rewrite -sm1 (leq_trans _ si1).
by rewrite mulrS (addrCA _ delta') addrK.
Qed.

End itv_partition_lemmas.

Section itv_partition_porder.
Context {d} {T : porderType d}.
Implicit Types (a b x : T) (s : seq T).

Let itv_partition_in_itv a b s :
  itv_partition a b s -> {in s, forall x, x \in `]a, b]%R}.
Proof.
move=> /[dup]parts.
move=> [/[dup]/lt_path_min/allP sa].
move=> /[dup]pas.
rewrite lt_path_pairwise.
move/pairwiseP => pwltas.
move/eqP => lsb.
move=> x xs.
rewrite in_itv/=; apply/andP; split; first exact: sa.
rewrite -lsb (last_nth a).
have xas : x \in a :: s by rewrite in_cons; apply/orP; right.
rewrite -(nth_index a xas).
rewrite le_eqVlt; apply/predU1P.
rewrite -implyNp => nlast.
apply: pwltas.
- rewrite inE/=.
  case: ifP => // _.
  by rewrite ltnS index_mem.
- by rewrite inE//.
- rewrite /=.
 move: s lsb parts sa pas x nlast xs xas.
  apply: last_ind => // s t IH.
  rewrite last_rcons => ->.
  move=> patsb asb psb x/[swap] xsb.
  rewrite nth_index; last first.
    by rewrite in_cons; apply/orP; right.
    move/[swap] => _.
    rewrite -last_nth last_rcons => xb.
  rewrite ifN; last first.
    by rewrite lt_eqF// asb.
  rewrite (_ : index x (rcons s b) = index x s); last first.
    rewrite -cats1 index_cat.
    rewrite ifT//.
    move: xsb.
    by rewrite mem_rcons in_cons => /predU1P; case.
  rewrite size_rcons ltnS.
  rewrite index_mem.
  move: xsb.
  rewrite mem_rcons in_cons.
  by move/predU1P; case.
Qed.

Lemma itv_partition_gt_lb a b s : (a < b)%O ->
  itv_partition a b s -> forall n, (a < nth b s n)%O.
Proof.
move=> ab ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth b s n \in `]a, b]%R.
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_le_ub a b s :
  itv_partition a b s -> forall n, (nth b s n <= b)%O.
Proof.
move=> ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth b s n \in `]a, b]%R.
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_head_in_itv a b s t :
  itv_partition a b (rcons s t) -> {in s, forall x, x \in `]a, b[%R}.
Proof.
move=> pst x xs.
have in_ab := itv_partition_in_itv pst.
rewrite in_itv/=; apply/andP; split.
  have := in_ab x.
  rewrite mem_rcons in_cons.
  have H : (x == t) || (x \in s) by apply/orP; right.
  by move/(_ H); rewrite in_itv/= => /andP[ax xb].
have [] := pst.
rewrite lt_path_pairwise.
move/pairwiseP => lt_ast.
move/eqP <-; rewrite (last_nth a).
have : x \in a :: (rcons s t).
  rewrite in_cons; apply/orP; right.
  by rewrite mem_rcons in_cons xs orbT.
move/(nth_index a) <-.
apply: lt_ast; last 2 first.
- by rewrite inE.
- rewrite /=.
  rewrite ifF; last first.
    rewrite lt_eqF => //.
    have [/lt_path_min/allP + _] := pst.
    by apply; rewrite mem_rcons in_cons xs orbT.
  by rewrite size_rcons -cats1 index_cat xs ltnS index_mem.
rewrite inE index_mem.
rewrite in_cons; apply/orP; right.
by rewrite mem_rcons in_cons xs orbT.
Qed.

Lemma itv_partition_lt_ub a b s :
  itv_partition a b s -> forall n, (n.+1 < size s)%N -> (nth b s n < b)%O.
Proof.
elim/last_ind : s => // s0 s1 _ ps n.
rewrite size_rcons ltnS => ns0.
pose s := rcons s0 s1.
rewrite -/s.
suff : nth b s n \in `]a, b[%R.
  by rewrite in_itv/= => /andP[].
apply: (@itv_partition_head_in_itv _ _ s0 s1) => //.
apply/(nthP b).
exists n => //.
by rewrite nth_rcons ns0.
Qed.

End itv_partition_porder.

(* Theorem 3.2: global existence and uniqueness *)
Section cauchy_lipschitz_global.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_[set: 'rV[R]_n] (phi x)}.
Hypothesis cont1 : {in [set: 'rV[R]_n], forall y, {within `[a, b], continuous phi ^~ y}}.

Let elt_prop (f : (R -> U) * (R * R) * nat) := True.

Let elt_type := {f : (R -> U) * (R * R) * nat | elt_prop f}.

Let f_ (x : elt_type) := (proj1_sig x).1.1.
Let a_ (x : elt_type) := (proj1_sig x).1.2.1.
Let b_ (x : elt_type) := (proj1_sig x).1.2.2.
Let i_ (x : elt_type) := (proj1_sig x).2.

Let elt_rel i j := f_ j (a_ j) = f_ i (b_ i).

Theorem cauchy_lipschitz_global : exists f : R -> 'rV_n (*: continuousFunType `[a, b] [set: 'rV[R]_n]*),
  is_sol_on phi u0 a (BLeft b) f.
Proof.
near (0:R)^'+ => rho'.
have rho'_gt0 : 0 < rho' by [].
have rho'_lt1 : rho' < 1 by [].
pose rho := PosNum rho'_gt0.
have rho1 : rho%:num < 1 by [].
have r_gt0 init a' b' : 0 < (rho%:num * sup_phi phi a' b' init / ((1 - rho%:num) * k)) + 1.
  rewrite ltr_wpDl// mulr_ge0 ?invr_ge0// mulr_ge0// ?subr_ge0.
  exact: sup_phi_ge0.
  exact: ltW.
  exact: ltW.
have [barhok|barhok] := leP (b - a) (rho%:num / k).
  pose h := sup [set `|phi t u0| | t in `[a, b]].
  have {}r_gt0 : 0 < (rho%:num * h / ((1 - rho%:num) * k)) + 1.
    by rewrite r_gt0// sup_phi_ge0.
  pose r := PosNum r_gt0.
  have Hr : r%:num / (k * r%:num + h) > rho%:num / k.
    rewrite ltr_pdivlMr; last first.
      rewrite ltr_wpDr//.
        exact: sup_phi_ge0.
      by rewrite mulr_gt0.
    rewrite mulrAC -ltr_pdivlMr ?invr_gt0// invrK.
    rewrite mulrDr -ltrBrDl -[X in _ < X - _]mul1r (mulrC k).
    rewrite -mulrBl mulrCA -ltr_pdivrMr; last by rewrite mulr_gt0// subr_gt0.
    by rewrite /= ltrDl.
  have safe_distba : safe_dist phi a b k u0 (PosNum r_gt0) rho = b - a.
    rewrite /safe_dist; apply/min_idPl.
    rewrite le_min barhok andbT.
    rewrite (le_trans barhok)//.
    exact: ltW.
  exists (@lipschitzT_solution_f R n phi a b k u0 r rho rho1 ab k0 lip2 cont1).
  have [d0 [[fau0 H1] H2 H3]] :=
    @lipschitzT_cauchy_lipschitz_local R n phi a b k u0 r rho rho1 ab k0 lip2 cont1.
  split => //.
    move=> t tab.
    apply H1; apply/mem_set.
    move/set_mem : tab.
    by apply: subset_itvl; rewrite bnd_simp safe_distba subrKC.
  apply: continuous_subspaceW H2.
  apply: subset_trans; first exact: itv_closure.
  rewrite closure_neitv_oo ?ltDl_safe_dist//.
  apply: subset_itvl; rewrite bnd_simp -lerBlDl.
  by rewrite safe_distba.
have [delta /andP[delta_gt0 delta_rhok]] : exists delta, 0 < delta <= rho%:num / k.
  admit.
have [delta' [s [/andP[delta'0 delta'delta] [abs nthdelta']]]] : exists (delta' : R) s,
    0 < delta' < delta /\
    itv_partition a b s /\
    forall i, (i < size s)%N -> nth b (a :: s) i.+1 - nth b (a :: s) i < delta.
  exact: itv_partition_lt.
have sizes_gt0 : (0 < size s)%N.
  move: abs.
  destruct s => //.
  case => /= _ /eqP ?; subst b.
  move: ab.
  by rewrite ltxx.
have Ilt i : (i < size s)%N -> nth b (a :: s) i < nth b (a :: s) i.+1.
  move=> si; case: abs => sa /eqP asb.
  by move/(pathP b) : sa; apply.
pose I i := `[nth b (a :: s) i, nth b (a :: s) i.+1]%R.
have Iiab i : [set` I i] `<=` `[a, b].
  have [si|si] := leqP i (size s).
    move=> x/=.
    rewrite !in_itv/= => /andP[ix xi]; apply/andP.
    destruct i as [|i] => //.
      rewrite ix; split => //.
      rewrite (le_trans xi)//.
      destruct s as [|s0 s1] => //=.
      case: abs => /= /andP[as0].
      move/order_path_min => /(_ lt_trans)/allP H /eqP s0s1b.
      destruct s1 as [|s1 s2].
        by rewrite /= in s0s1b; rewrite s0s1b.
      by apply/ltW/H; rewrite -s0s1b /=  mem_last.
    split.
      rewrite (le_trans _ ix)// ltW//.
      case: abs => /order_path_min => /(_ lt_trans)/allP + _.
      apply.
      by apply/(nthP b); exists i.
    rewrite (le_trans xi)//.
    case: abs => sa /eqP asb.
    move: si; rewrite leq_eqVlt => /predU1P[->|si].
      by rewrite nth_default.
    rewrite -{2} asb (last_nth b) -(@prednK (size s)); last by rewrite (leq_trans _ si).
    apply: sorted_leq_nth => //.
    - exact: le_trans.
    - apply: path_sorted.
      apply: sub_path sa.
      by move=> ? ? /ltW.
    - by rewrite inE prednK// (leq_trans _ si).
    - by rewrite -(ltn_add2r 1) !addn1 (leq_trans si)// prednK// (leq_trans _ si).
   have -> : [set` I i] = [set b].
     apply/seteqP; split => [x/=|].
       rewrite in_itv/=.
       rewrite nth_default/=//.
       rewrite nth_default; last exact: ltnW.
       by rewrite -eq_le => /eqP.
     move=> _ /= ->.
     rewrite in_itv/=.
     rewrite nth_default/=//.
     rewrite nth_default; last exact: ltnW.
     by rewrite !lexx.
   move=> x/= ->.
   by rewrite bound_itvE ltW.
have pickup_itv (x : R) : x \in `[a, b] -> exists2 i : nat, (i < size s)%N & x \in I i.
  move=> xab; apply: itv_partition_ex => //.
  by move: xab; rewrite inE/= in_itv.
have lip2'' (i : nat) : (i <= size s)%N -> {in I i, forall x : R, k.-lipschitz (phi x)}.
  move=> im.
  apply/in_switch/(@lipschitzW _ _ _ _ _ `[a, b]).
    exact: Iiab.
  apply/in_switch => t tab [X Y] [/= u0rX u0rY].
  have /(_ (X, Y)) := lip2 tab.
  exact.
have cont1'' (i : nat) : (i <= size s)%N ->
    {in [set: 'rV_n], forall y : 'rV_n, {within [set` I i], continuous phi^~ y}}.
  move=> si /= t tu0r.
  apply: (@continuous_subspaceW _ _ _ `[a, b]); last exact: cont1.
  exact: Iiab.
pose h0 := sup_phi phi a (nth b (a :: s) 1).
pose f_0 : R -> U :=
  @lipschitzT_solution_f R n phi a (nth b (a :: s) 1) k u0
    (PosNum (r_gt0 u0 a (nth b (a :: s) 1))) rho rho1
    (Ilt _ sizes_gt0) k0 (lip2'' _ (ltnW sizes_gt0)) (cont1'' _ (ltnW sizes_gt0)).
have [v [v0 Pv]] : {v : nat -> elt_type |
    v 0%N = exist _ (f_0, (a, nth b (a :: s) 1), O) Logic.I /\
    forall n, elt_rel (v n) (v n.+1)}.
  apply: dependent_choice => -[[[f [a' b']] i']] [].
  pose init0 : U := f b'.
  pose a'' := nth b (a :: s) i'.+1.
  have [i's|i's] := ltnP (i'.+1) (size s)%N.
    pose b'' := nth b (a :: s) i'.+2.
    pose f_i : R -> U :=
      @lipschitzT_solution_f R n phi a'' b'' k init0
        (PosNum (r_gt0 init0 a'' b''))
      rho rho1 (Ilt _ i's) k0 (lip2'' _ (ltnW i's)) (cont1'' _ (ltnW i's)).
    exists (exist _ (f_i, (a'', b''), i'.+1) Logic.I).
    rewrite /elt_rel.
    rewrite /f_/=.
    have [/=] := lipschitzT_solution init0 (PosNum (r_gt0 init0 a'' b'')) rho1
         (Ilt i'.+1 i's) k0 (lip2'' i'.+1 (ltnW i's)) (cont1'' i'.+1 (ltnW i's)).
    move=> + _ _.
    rewrite -/f_i.
    rewrite /init0.
    rewrite /a_/=.
    rewrite /b_/= => <-.
    by rewrite /a''/=.
  apply/cid.
  move: i's; rewrite leq_eqVlt => /predU1P[i's|i's].
    have a''E : a'' = last b s.
      rewrite /a'' -i's.
      rewrite -last_nth//.
      rewrite -!nth_last.
      apply: set_nth_default.
      by rewrite prednK.
    case: abs => _ /eqP asb.
    have {}a''E : a'' = b.
      rewrite a''E.
      rewrite -nth_last -[RHS]asb -nth_last.
      apply: set_nth_default.
      by rewrite prednK.
    exists (exist _ ((cst (f b')), (b, b), i'.+1) Logic.I).
    rewrite /elt_rel/=.
    rewrite /f_/=.
    by rewrite /a_ /b_ /=.
  have a''E : a'' = last b s.
    rewrite /a'' /= nth_default//.
    case: abs => _ /eqP asb.
    rewrite -[LHS]asb -!nth_last.
    apply: set_nth_default.
    by rewrite prednK.
  exists (exist _ ((cst (f b')), (b, b), i'.+1) Logic.I).
  rewrite /elt_rel/=.
  rewrite /f_/=.
  by rewrite /a_ /b_ /=.
pose pickup_itv_fun (x : R) : nat :=
  match pselect (x \in `[a, b]) with
  | left H => sval (cid2 (pickup_itv x H))
  | right _ => 0
  end.
exists (fun x =>
    match pselect (x \in `[a, b]) with
    | left H => let i := sval (cid2 (pickup_itv x H)) in
                let im : (i < size s)%N := (svalP (cid2 (pickup_itv x H))).1 in
                let xIi : x \in I i := (svalP (cid2 (pickup_itv x H))).2 in
      f_ (v i) x
    | right _ => \row_(i < n) 0
    end).
split.
- case: pselect; last first.
    by rewrite inE/= bound_itvE (ltW ab).
  move=> ?.
  rewrite /=.
  case: cid2 => // i/= si aIi.
  rewrite /f_/=.
  have i0 : i = 0.
    apply/eqP/negPn.
    rewrite -lt0n; apply/negP => i0.
    move: aIi.
    rewrite in_itv/= => /andP[ia ai].
    move: ia.
    rewrite leNgt => /negP; apply.
    destruct i as [|i] => //=.
    apply: itv_partition_gt_lb.
    done.
    done.
  rewrite i0 v0/=.
  have := lipschitzT_solution u0 (PosNum (r_gt0 u0 a (nth b (a :: s) 1))) rho1
       (Ilt 0%N sizes_gt0) k0 (lip2'' 0%N (ltnW sizes_gt0)) (cont1'' 0%N (ltnW sizes_gt0)).
  by case => //.
- move=> t tab; split.
    admit.
  admit.
- rewrite closure_neitv_oo//.
  apply/(continuous_within_itvP _ ab); split.
  + move=> t tab.
    rewrite /continuous_at.
    admit.
  + admit.
  + admit.
Abort.

End cauchy_lipschitz_global.

Section exe325.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis k0 : 0 < k.
Variable D : set U.
Hypothesis lip2 : {in `[a, b]%R, forall t : R, k.-lipschitz_D (phi t)}.
Hypothesis cont1 : {in D, forall x : U, {within `[a, b], continuous phi ^~ x}}.
Variable W : set U.
Hypothesis compactW : compact W.
Variable u0 : U.
Hypothesis u0W : u0 \in W.

Variable f : R -> U.
Hypothesis fder : forall t, derivable f t 1 /\ 'D_1 f t = phi t (f t).
Hypothesis fini : f a = u0.

Variable T : R.
Hypothesis xW : forall t, t \in `[a, T[%R -> t < b.

Lemma exe325a : @unif_continuous (subspace `[a, T[) U f.
Proof.
Admitted.

Lemma exe325b1 : forall t, t \in `[a, T[ -> f t \in W.
Proof.
Admitted.

Lemma exe325b2 : is_sol_on phi u0 a (BLeft T) f.
Proof.
Admitted.

Lemma exe325b3 : exists delta, delta > 0 /\ is_sol_on phi u0 a (BLeft (T + delta)) f.
Proof.
Admitted.

End exe325.

Section exe326.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis k0 : 0 < k.
Variable D : set U.
Hypothesis lip2 : {in `[a, b]%R, forall t : R, k.-lipschitz_D (phi t)}.
Hypothesis cont1 : {in D, forall x : U, {within `[a, b], continuous phi ^~ x}}.

Variable T : R.
Hypothesis aTab : `[a, T[ `<=` `[a, b].
Variable f : R -> U.
Variable u0 : U.
Hypothesis fsol : is_sol_on phi u0 a (BLeft T)(*exluded*) f.

Variable W : set U.
Hypothesis compactW : compact W.
Hypothesis u0W : u0 \in W.

Lemma exe326 : exists t, t \in `[a, T[%R /\ f t \notin W.
Proof.
Admitted.

End exe326.

Section cauchy_lipschitz_nonlocal.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a : R) (k : R).
Hypothesis k0 : 0 < k.
Variable D : set U.
Hypothesis lip2 : {in `[a, +oo[%R, forall t : R, k.-lipschitz_D (phi t)}.
Hypothesis cont1 : {in D, forall x : U, {within `[a, +oo[, continuous phi ^~ x}}.

Variable W : set U.
Hypothesis compactW : compact W.
Variable u0 : U.
Hypothesis u0W : u0 \in W.
Hypothesis solW : forall f : R -> U,
  (forall t, derivable f t 1 /\ 'D_1 f t = phi t (f t)) /\ f a = u0
  -> forall t, f t \in W.

Lemma thm33 : exists !f, (forall t, t \in `[a, +oo[ -> derivable f t 1 /\
                                                       'D_1 f t = phi t (f t)) /\
                         f a = u0.
Proof.
have @rho : {posnum R}.
  admit.
(* by thm31, there is a unique local solution over `[a, a + delta[*)
have @T : R.
  (* [a, T[ is the maximum interval of the solution above *)
  admit.
have @y : R -> U.
  (* a solution on [a, T[ *)
  admit.
(* if T is finite, y must leave W -> absurd *)
(* therefore T = +oo, cqfd *)
Abort.

End cauchy_lipschitz_nonlocal.
