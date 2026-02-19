From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra ring.
From mathcomp Require Import interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions reals order.
From mathcomp Require Import topology normedtype landau sequences derive realfun.
From mathcomp Require Import matrix_normedtype.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.
Require Import lasalle (* to at least get the structure of filters on sets *).
Require Import ode tilt_stability tilt_lyapunov.

(**md**************************************************************************)
(* # Formalization of [benallegue2023itac] (2/2)                              *)
(*                                                                            *)
(* The main result of this file is to show that all solutions converge to one *)
(* of the two equilibrium points.                                             *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [cohen2017itp] C. Cohen, D. Rouhling. A formal proof in Coq of LaSalle’s *)
(* invariance principle. ITP 2017                                             *)
(* - [benallegue2023itac]                                                     *)
(* https://hal.science/hal-04271257v1/file/benallegue2019tac_October_2022.pdf *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

(* finite intersection property *)
Lemma compact_decreasing_bigcap d {K : orderType d} (k0 : K)
  (X : ptopologicalType) (B : K -> set X) (O : set X) :
  hausdorff_space X ->
  (forall i : K, (k0 <= i)%O -> compact (B i)) ->
  (forall i j : K, (i <= j)%O -> B j `<=` B i) ->
  open O ->
  (\bigcap_(i in [set i | (k0 <= i)%O]) B i `<=` O) ->
  exists i0, (k0 <= i0)%O /\ B i0 `<=` O.
Proof.
move => H comp decr openO subO.
set V := fun i => B i `&` ~` O.
have comp' i : (k0 <= i)%O -> compact (V i).
  move=> i0.
  apply: compact_closedI.
    by apply comp.
  by apply open_closedC.
have decr' i j : (i <= j)%O -> V j `<=` V i.
  move=> ij.
  rewrite /V.
  by apply: setSI; exact: decr.
apply/not_existsP => hf.
suff /set0P : \bigcap_(i in [set t | k0 <= t]%O) V i !=set0.
  rewrite bigcapIl; last by exists k0 => /=; exact: lexx.
  by move/eqP/subsets_disjoint.
have cf : closed_fam_of (B k0) [set t | t >= k0]%O V.
  exists V => t t0 //.
    apply closedI.
      apply compact_closed => //.
      exact: comp.
    exact: open_closedC.
  rewrite /V setIA.
  congr (_ `&` _).
  rewrite setIC.
  exact/esym/setIidl/decr.
have : compact (B k0) by apply comp.
rewrite compact_In0/=; apply => //.
move=> D Ds.
set m := \big[Order.max/k0]_(z <- D) z.
have M x : x \in D -> (x <= m)%O by move=> xD; exact: le_bigmax_seq.
suff Vm : V m `<=` \bigcap_(i in [set` D]) V i.
  apply: (subset_nonempty Vm).
  have := hf m.
  apply: contra_notP.
  move/nonemptyPn => Ve; split.
    exact: bigmax_ge_id.
  by apply subsets_disjoint.
apply sub_bigcap => i Di.
exact/decr'/M.
Qed.

(* NB: should be possible to generalize without normal_space X *)
Lemma compact_connected_cluster {K : realType}
  (X : ptopologicalType) (f : K -> X) (A : set X) :
  hausdorff_space X ->
  normal_space X ->
  continuous f ->
  compact A ->
  (forall t, 0 <= t -> f t \in A) ->
  connected (cluster (f t @[t --> +oo])).
Proof.
move => H Hn contf compactf imagef.
set B := fun t => closure (f @` `[t, +oo[).
have Bcon t : connected (B t).
  apply: connected_closure.
  apply: connected_continuous_connected.
  apply /connected_intervalP/interval_is_interval.
  by apply continuous_subspaceT.
have Bnonempty t : B t !=set0.
  exists (f t); apply/subset_closure/set_mem/image_f.
  by rewrite inE/= in_itv/= lexx.
have Bmon s t : s <= t -> B t `<=` B s.
  move=> st; apply/closure_subset/image_subset.
  by apply: subset_itvr; rewrite bnd_simp.
have Bcom t : 0 <= t -> compact (B t).
  move=> t0; apply: (subclosed_compact _  compactf).
    exact: closed_closure.
  rewrite (closure_id A).1; last exact: compact_closed.
  apply: closure_subset => _ [x tx] <-.
  apply/set_mem/imagef.
  by move: tx; rewrite /= in_itv/= andbT; exact: le_trans.
have -> : cluster (f t @[t --> +oo]) = \bigcap_(t in [set t | 0 <= t]) B t.
  rewrite clusterE; apply/seteqP; split.
  - apply: sub_bigcap => /= t _.
    apply: bigcap_inf.
    exists t; split; first exact: num_real.
    by move=> x tx; exists x => //; rewrite /= in_itv/= ltW.
  - apply: sub_bigcap => b /= [t0 [_ /= h]].
    apply: (subset_trans (bigcap_inf (i := Num.max 0 (t0 + 1)) _)) => //=.
      by rewrite le_max lexx.
    apply: closure_subset => _ /= [x xt] <-.
    apply h.
    move: xt; rewrite in_itv/= andbT; apply: lt_le_trans.
    by rewrite lt_max ltrDl ltr01 orbT.
apply/connectedP => E [Enonempty Eu Esep].
have /(separated_closedUP Esep) [E1c E2c] : closed (E false `|` E true).
  rewrite -Eu; apply: closed_bigI => i P; apply: compact_closed => //.
  exact: Bcom.
have /normal_openP := Hn.
move /(_ K (E false) (E true)) => [//|//|| V1 [V2 [? ? EfalseV1 EtrueV2 ?]]].
  exact: separated_disjoint.
have V1V2o : open (V1 `|` V2) by exact: openU.
have V1V2sep : separated V1 V2 by exact: open_disjoint_separated.
have BV1V2 : \bigcap_(t in [set t | 0 <= t]) B t `<=` V1 `|` V2.
  by rewrite Eu; exact: setUSS.
case/compact_decreasing_bigcap : BV1V2 => // t0 [t0ge0 Bto] //.
suff: V1 `&` V2 !=set0 by apply nonemptyPn.
have [e1 E1] := Enonempty false.
have [e2 E2] := Enonempty true.
have EB : E false `|` E true `<=` B t0.
  by rewrite - Eu; exact: bigcap_inf.
have [hbv|hbv] := connected_subset V1V2sep Bto (Bcon _).
- exists e2; split; last exact: EtrueV2.
  by apply: hbv; apply: EB; right.
- exists e1; split; first exact: EfalseV1.
  by apply: hbv; apply: EB; left.
Qed.

Section sublevel.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.

Definition sublevel (V : U -> R) c := [set x : U | V x <= c].

Lemma sublevel_preimage (V : U -> R) c : sublevel V c = V @^-1` [set r | r <= c].
Proof. by []. Qed.

End sublevel.

Section LaSalle_tilt.
Context {K : realType}.
Let U := 'rV[K]_6.
Variable sol : U -> K -> U.
Variables gamma alpha1 : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Let phi := Tilt.eqn alpha1 gamma.

Hypothesis solP : forall y, y 0 \in Tilt.Upsilon1 ->
  lasalle.is_sol phi y <-> y = sol (y 0).

Hypothesis initp : forall p, sol p 0 = p.

Let isSol p : p \in Tilt.Upsilon1 -> sol_is_deriv_c0y phi (sol p).
Proof.
move=> Kp.
apply/sol_is_deriv_c0yP.
have : lasalle.is_sol phi (sol p) by apply/solP; rewrite ?initp.
move=> [/= _ H] t t0.
split.
  by apply: ex_derive; exact: H.
by rewrite derive1E; apply H.
Qed.

Definition sublevelUpsilon1 (p : U) :=
  sublevel (Tilt.V1 alpha1 gamma) (Tilt.V1 alpha1 gamma p) `&` Tilt.Upsilon1.

Lemma mem_sublevelUpsilon1 p : Tilt.Upsilon1 p ->
  p \in sublevelUpsilon1 p.
Proof. by rewrite /sublevelUpsilon1 /sublevel/= inE/=. Qed.

(* continuity in initial value: assumption needed for LaSalle *)
Hypothesis cont_sol : forall p t, {within sublevelUpsilon1 p, continuous sol^~ t}.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

Lemma V1_bound_compact p :
  compact (sublevel (Tilt.V1 alpha1 gamma) (Tilt.V1 alpha1 gamma p)).
Proof.
(* TODO: use something similar to compact_sphere *)
apply: bounded_closed_compact.
- rewrite /Tilt.V1/= /bounded_near.
  near=> r.
  move=> /= x.
  rewrite /sublevel/= !addf_div; rewrite ?lt0r_neq0 ?mulr_gt0//.
  rewrite ler_pdivrMr ?mulr_gt0// divrK; last first.
    by rewrite unitfE lt0r_neq0 // ?mulr_gt0.
  rewrite  !(mulrC 2) !mulrA -!mulrDl ler_pM2r//  => h.
  set c := `| Left p |_e ^+ 2 * gamma + `| Right p |_e ^+ 2 * alpha1.
  have c0 : 0 <= c.
    by rewrite addr_ge0// mulr_ge0 ?sqr_ge0 ?ltW.
  have hL : `| Left x |_e <= Num.sqrt (c / gamma).
    rewrite -(sqr_sqrtr (enorm_ge0 (Left x))).
    rewrite /GRing.exp/= -sqrtrM ?enorm_ge0//.
    rewrite ler_sqrt ?divr_ge0 ?(@ltW _ _ _ gamma)//.
    rewrite ler_pdivlMr//.
    apply: le_trans h.
    by rewrite lerDl mulr_ge0// ?sqr_ge0 ?ltW.
  have hR : `| Right x |_e <= Num.sqrt (c / alpha1).
    rewrite -(sqr_sqrtr (enorm_ge0 (Right x))).
    rewrite /GRing.exp/= -sqrtrM ?enorm_ge0//.
    rewrite ler_sqrt// ?divr_ge0 ?(@ltW _ _ _ alpha1)//.
    rewrite ler_pdivlMr//.
    apply: le_trans h.
    by rewrite addrC lerDl mulr_ge0 // ?sqr_ge0 ?ltW.
  have normb : `|x| <=  `| Left x |_e  + `|Right x|_e.
    rewrite -[in leLHS](@hsubmxK _ 1 3 3 x) (norm_rowmx (Left x)) ge_max.
    by rewrite !(le_trans (mxnorm_enorm_le _))//= ?lerDl ?lerDr ?enorm_ge0.
  exact/(le_trans normb)/(le_trans (lerD hL hR)).
- rewrite sublevel_preimage.
  apply: closed_comp.
    move=> /= x xin.
    exact: (differentiable_continuous (V1_diff _ _ _)).
  exact: closed_le.
Unshelve. all: by end_near. Qed.

Lemma compact_sublevelUpsilon1 p : compact (sublevelUpsilon1 p).
Proof.
apply: compact_closedI; first exact: V1_bound_compact.
rewrite Tilt.Upsilon1_preimage.
apply : closed_comp => // => x xp.
apply : continuous_comp; last exact: continuous_enorm.
apply: continuousB.
  exact: cst_continuous.
exact: continuous_rsubmx.
Qed.

Lemma invariant_sublevelUpsilon1 p :
  lasalle.is_invariant sol (sublevelUpsilon1 p).
Proof.
rewrite /= /lasalle.is_invariant/=.
move => /= x.
rewrite /sublevelUpsilon1/= =>  -[Vx Kx] t t0.
split; last first.
  apply/(@tilt_state_spaceS  _ alpha1 gamma).
  exists (sol x), (t + 1) => /=. (* use large enough time *)
  split => //.
  + rewrite initp.
    exact/mem_set.
  + apply sol_is_deriv_c0yco.
    apply isSol => //.
    by rewrite inE.
  + exists t => //.
    by rewrite /= in_itv/=t0/=ltrDl.
move/mem_set : (Kx) => /isSol /sol_is_deriv_c0yP solA.
rewrite /sublevel/=.
rewrite (le_trans _ Vx)//.
rewrite -[in leRHS](@initp x).
have : {in `[0, t + 1[, forall t : K, derivable (sol x) t 1}.
  move=> t'.
  rewrite in_itv/= => /andP[t0' _].
  by apply solA.
move/V_nincr => /= => /(_ (Tilt.V1 alpha1 gamma)).
apply.
- exact: V1_diff.
- move => t1 tt1.
  apply: (@derive_along_V1_le0 _ _ _ _ _ (t + 1)) => //.
  + by rewrite initp inE.
  + apply: sol_is_deriv_c0yco => //.
    apply/sol_is_deriv_c0yP.
    by apply solA.
  + move=> t2 /andP[t2' _].
    apply/derivable1_diffP.
    apply solA.
    by rewrite ltW.
- by rewrite ltrDl.
- by rewrite lexx.
Qed.

Local Lemma sol_sublevelUpsilon1 p u :
  u \in sublevelUpsilon1 p -> sol_is_deriv_c0y phi (sol u).
Proof.
rewrite inE/= => -[h1 h2].
apply isSol => //.
by rewrite inE.
Qed.

Lemma V1dot_point1_eq0 : V1dot Tilt.point1 = (0 : K).
Proof.
rewrite /V1dot /Tilt.point1 /=.
rewrite lsubmx_const rsubmx_const enorm0 expr0n /= oppr0 add0r !mul0mx sub0r oppr0.
by rewrite mxE.
Qed.

Lemma V1dot_point2_eq0 : V1dot Tilt.point2 = (0 : K).
Proof.
rewrite /V1dot /Tilt.point2 /=.
rewrite row_mxKl row_mxKr.
rewrite enorm0 expr0n /= oppr0 add0r.
rewrite -!scalemxAl -scalerBr.
rewrite trmx0 mulmx0 subr0.
rewrite !scalemxAl.
rewrite norm_spin.
rewrite -!scalemxAl enormZ.
rewrite spinE.
suff -> : 'e_2 *v 'e_2 = (0 : 'rV[K]_3).
  by rewrite enorm0 /GRing.exp /= !mulr0 oppr0.
by rewrite vece2 /= scale0r.
Qed.

Local Lemma sol_continuous p : p \in Tilt.Upsilon1 -> continuous (sol p).
Proof.
move => sp t.
have [issol0 issol1]: lasalle.is_sol phi (sol p).
  apply: (lasalle.sol_is_sol (sol := sol) (K:=Tilt.Upsilon1)) => //.
  move => y Ky.
  by apply /solP;rewrite inE.
  move : sp.
  by rewrite inE.
apply : differentiable_continuous.
apply /derivable1_diffP.
have [ht | ht] := ltP t 0; last by apply /ex_derive/issol1.
apply : (@near_eq_derivable _ _ _ (fun t => 2 *: sol p 0 - sol p (-t))) => //.
  near do (rewrite -issol0//).
  exact: lt_nbhsl.
apply/derivable1_diffP.
apply: differentiable_comp => //.
apply: differentiable_comp => //.
apply: differentiable_comp => //.
apply/derivable1_diffP.
apply/ex_derive/issol1.
by rewrite lerNr oppr0 ltW.
Unshelve. all: by end_near. Qed.

Local Lemma limS_subset_V1dot0 p :
  p \in Tilt.Upsilon1 ->
  lasalle.limS sol (sublevelUpsilon1 p) `<=`
  [set x : 'rV[K]_6 | V1dot x = 0] `&` Tilt.Upsilon1.
Proof.
move => ps.
have lasalle_sol (y : K -> 'rV_6) :
  sublevelUpsilon1 p (y 0) -> lasalle.is_sol phi y <-> y = sol (y 0).
  move=> Ky.
  apply/solP.
  rewrite inE.
  by apply Ky.
have H : lasalle.limS sol (sublevelUpsilon1 p) `<=`
         [set x | (Tilt.V1 alpha1 gamma \o sol x)^`()%classic 0 = 0] `&`
         Tilt.Upsilon1.
  rewrite subsetI; split.
  - apply: (@lasalle.stable_limS _ _ _ _ (@compact_sublevelUpsilon1 p) _ _
        lasalle_sol _ (@invariant_sublevelUpsilon1 p)
        (Tilt.V1 alpha1 gamma)) => //=.
    + apply/continuous_subspaceT => x xK.
      apply: differentiable_continuous.
      exact: V1_diff.
    + move=> /= p0 t K0 t0.
      apply/derivable1_diffP.
      apply: differentiable_comp.
        apply/derivable1_diffP.
        apply isSol => //; last first.
          by rewrite in_itv/= andbT.
        rewrite inE.
        by have [_ +] := K0.
      exact: V1_diff.
    + move=> p0 K0.
      have p0s : p0 \in Tilt.Upsilon1.
        by move : K0; rewrite inE/= /inE/= => -[].
      rewrite derive1E -derive_along_derive.
      * apply : derive_along_V1_le0_global => //.
          by rewrite initp.
        by apply isSol.
      * rewrite initp.
        exact: V1_diff.
    + apply /derivable1_diffP.
      apply isSol => //.
      by rewrite in_itv/= lexx.
  - move=>/=x [q qKsub xcl].
    suff [] : (sublevelUpsilon1 q) x by [].
    rewrite (closure_id (sublevelUpsilon1 q)).1; last first.
      apply compact_closed => //.
      exact: compact_sublevelUpsilon1.
    have qs (t : K) : 0 <= t -> state_space phi (sublevelUpsilon1 q) (sol q t).
      move=> t0; exists (sol q), (t + 1); split.
      + by rewrite initp; apply: mem_sublevelUpsilon1; case: qKsub.
      + apply: sol_is_deriv_c0yco.
        by apply isSol; rewrite inE; apply qKsub.
      + exists t => //.
        by rewrite/=in_itv/= t0 ltrDl ltr01.
    have lim_sp : (sol q x @[x --> +oo]) (sublevelUpsilon1 q).
      exists 0; split => // t t0 /=.
      apply invariant_sublevelUpsilon1.
        split => /=.
          by rewrite /sublevel/=.
        by case: qKsub.
      by rewrite ltW.
    by move: xcl; rewrite clusterE; exact.
apply: (subset_trans H) =>/= x [+ h1] /=.
rewrite /= derive1E -derive_along_derive.
- rewrite derive_along_V1_global //=.
    by rewrite initp ?inE.
  split => //.
  apply isSol => //.
    by apply/mem_set.
  apply isSol => //.
  by apply/mem_set.
- exact: V1_diff.
- apply/derivable1_diffP.
  apply isSol => //; last first.
    by rewrite in_itv/= lexx.
  by rewrite inE.
Qed.

Lemma limS_subset_points p :
  p \in Tilt.Upsilon1 -> lasalle.limS sol (sublevelUpsilon1 p) `<=` Tilt.points.
Proof.
have -> : Tilt.points = [set x : 'rV[K]_6 | V1dot  x = 0] `&` Tilt.Upsilon1.
  apply/seteqP; split => x /=.
    case => ->;split; [exact: V1dot_point1_eq0 | | exact: V1dot_point2_eq0 | ].
      have := @tilt_point1_in_state_space K.
      by rewrite inE.
    have := @tilt_point2_in_state_space K.
    by rewrite inE.
  move => [h1 h2'].
  have h2 : x \in Tilt.Upsilon1 by rewrite inE.
  move : h1.
  have hi := initp x.
  rewrite -hi => h1.
  have sol' : sol_is_deriv_co (fun=> phi) 0 1 (sol x).
    apply: sol_is_deriv_c0yco.
    by apply isSol.
  rewrite /Tilt.points/=.
  apply: (V1dot_eq0_p1_or_p2 _ sol') => //.
    rewrite hi.
    exact/mem_set.
  by rewrite bound_itvE ltr01.
by apply limS_subset_V1dot0.
Qed.

Lemma cvg_to_set_points p : p \in Tilt.Upsilon1 ->
  sol p t @[t --> +oo] --> (Tilt.points : set 'rV_6).
Proof.
move=> /set_mem ps.
have p0K : (forall p0 : 'rV_6, p0 \in sublevelUpsilon1 p -> sol p0 0 = p0).
  move => q /set_mem[_ h].
  exact: initp.
apply: (cvg_trans (lasalle.cvg_to_limS (@compact_sublevelUpsilon1 p)
                    (@invariant_sublevelUpsilon1 p) _)).
  by apply/set_mem/mem_sublevelUpsilon1.
move => /= S [eps eps0 Be].
exists eps => //.
apply bigcup_sub => /= x H.
apply: (subset_trans _ Be).
have ps' : p \in Tilt.Upsilon1 by exact/mem_set.
have : Tilt.points x by apply: (limS_subset_points ps').
move => h x' Bx'.
by exists x.
Qed.

Lemma avoid_x (x : U) : (~` Tilt.points) x ->
  exists S : set U, [/\ open S, Tilt.points `<=` S & ~ closure S x].
Proof.
move => hx.
have cx : closed [set x].
  by apply accessible_closed_set1; apply hausdorff_accessible.
have cp : closed (@Tilt.points K).
  rewrite /Tilt.points.
  by apply accessible_finite_set_closed => //; apply hausdorff_accessible.
have /(@normal_openP K) Hn : normal_space U by apply: pseudometric_normal.
have [|V1 [V2 [V1o V2o V1c V2c Vdisj]]] := (Hn _ _ cx cp).
  apply disjoints_subset.
  by rewrite sub1set; apply/mem_set .
exists V2;split => //.
move => h.
have [_ +] := open_disjoint_separated V1o V2o Vdisj.
apply /nonemptyPn => /=.
rewrite not_notE.
exists x.
split => //.
by apply V1c.
Qed.

Lemma cluster_contained_points p : p \in Tilt.Upsilon1 ->
  cluster (sol p t @[t --> +oo]) `<=` Tilt.points.
Proof.
move => ps.
have /cvg_cluster cp12 := cvg_to_set_points ps.
apply: (subset_trans cp12).
rewrite clusterE.
move => /= x H.
suff : (~ (~` Tilt.points) x) by apply contrapT.
move => Hdist.
have [S [So Sc Sx]] := avoid_x Hdist.
have [e1 /= e10 /= P1] :  \forall e \near 0^'+, ball Tilt.point1 e `<=` S.
  apply: open_subball => //.
  by apply Sc;left.
have [e2 /= e20 /= P2] :  \forall e \near 0^'+, ball Tilt.point2 e `<=` S.
  apply: open_subball => //.
  by apply Sc;right.
set eps := Num.min (e1 / 2) (e2 / 2).
have eps0 : 0 < eps.
  by rewrite lt_min !divr_gt0.
have B1 : ball Tilt.point1 eps `<=` S.
  apply P1 => //.
  rewrite /ball_/= sub0r normrN ger0_norm ?gt_min ?ltW // ltr_pdivrMr // ltr_pMr ?ltrDr //.
  by apply /orP;left.
have B2 : ball Tilt.point2 eps `<=` S.
  apply P2 => //.
  rewrite /ball_/= sub0r normrN ger0_norm ?gt_min ?ltW // ?ltr_pdivrMr // ltr_pMr ?ltrDr //.
  by apply /orP;right.
have nbh' : (nbhs Tilt.points S).
  exists eps => //=.
  rewrite /ball_set.
  by apply: bigcup_sub => /= _ [-> | ->].
by have := H _ nbh'.
Qed.

Local Lemma connected2_subset (A : set U) : connected A -> A !=set0 ->
  A `<=` Tilt.points -> A = [set Tilt.point1] \/ A = [set Tilt.point2].
Proof.
move=>Ac Anonempty Asub.
have sep : separated [set (@Tilt.point1 K)] [set Tilt.point2].
  split.
  - rewrite -(closure_id _).1; last first.
      by apply accessible_closed_set1; apply hausdorff_accessible.
    apply/disjoints_subset.
    rewrite sub1set.
    apply/mem_set => /=.
    exact/eqP/Tilt.point1_neq2.
  - rewrite setIC -(closure_id _).1; last first.
      by apply accessible_closed_set1; apply hausdorff_accessible.
    apply/disjoints_subset.
    rewrite sub1set.
    apply/mem_set => /=.
    exact/nesym/eqP/Tilt.point1_neq2.
have [/subset_set1 [/nonemptyPn A0 | ] | /subset_set1 [/nonemptyPn A0 |] ] :=
  connected_subset sep Asub Ac => //.
by left.
by right.
Qed.

Lemma cluster_nonempty p : p \in Tilt.Upsilon1 -> cluster (sol p t @[t --> +oo]) !=set0.
Proof.
move => sp.
suff : (sublevelUpsilon1 p) `&`  cluster (sol p t @[t --> +oo]) !=set0.
  move => [x [_ cx]].
  by exists x.
apply (@compact_sublevelUpsilon1 p) => //.
  by apply: fmap_proper_filter.
apply sub_image_at_infty => /=.
move => _ [t t0] <-.
apply invariant_sublevelUpsilon1 => //.
by apply/set_mem/mem_sublevelUpsilon1/set_mem.
Qed.

Lemma p1_sublevelUpsilon1 p : sublevelUpsilon1 p Tilt.point1.
Proof.
split => /=; last by have /set_mem := @tilt_point1_in_state_space K.
rewrite /sublevel/= /Tilt.point1 /Tilt.V1.
rewrite lsubmx_const rsubmx_const/= !enorm0 !expr0n /= !mul0r add0r.
by rewrite addr_ge0 // divr_ge0 // ?sqr_ge0 ?mulr_ge0 // ltW.
Qed.

Lemma tilt_cvg_to_point1_or_point2 p : p \in Tilt.Upsilon1 ->
  (sol p t @[t --> +oo] --> Tilt.point1) \/
  (sol p t @[t --> +oo] --> Tilt.point2).
Proof.
move => ps.
have cluster_con : connected (cluster (sol p t @[t --> +oo])).
  apply: (compact_connected_cluster _ _ _ (@compact_sublevelUpsilon1 p) ) => //.
    by apply: pseudometric_normal.
    by apply: sol_continuous.
  move => t t0.
  apply/mem_set.
  apply: invariant_sublevelUpsilon1 => //.
  by apply/set_mem/mem_sublevelUpsilon1/set_mem.
have := connected2_subset cluster_con (cluster_nonempty ps) (cluster_contained_points ps).
suff H (q : U): cluster (sol p t @[t --> +oo]) = [set q] ->  sol p t @[t --> +oo] --> q.
  move => [h | h]; [left | right];apply H => //.
move => H.
have sublevelUpsilon1q : sublevelUpsilon1 p q.
   suff:  cluster (sol p t @[t --> +oo]) `<=` sublevelUpsilon1 p.
      by apply; rewrite H.
   rewrite clusterE.
   apply :(@subset_trans  _ (closure  (sol p @` `[0, +oo[))).
     apply: bigcap_inf => //=.
     exists 0; split => //= x x0.
     exists x=>//.
     rewrite in_itv/=ltW//.
     rewrite (closure_id (sublevelUpsilon1 p)).1;last first.
       by apply compact_closed =>//; apply compact_sublevelUpsilon1.
   apply closure_subset.
   move => /= _ [t +] <-.
   rewrite in_itv/= => /andP[t0 _].
   apply invariant_sublevelUpsilon1 => //.
   by apply/set_mem/mem_sublevelUpsilon1/set_mem.
have [M [Mr Mp]]: bounded_set (sublevelUpsilon1 p).
  apply compact_bounded.
  exact: compact_sublevelUpsilon1.
have [M0 | M0]  := leP 0 M;last first.
   suff : `|q| < 0 by rewrite normr_lt0.
   have M02 : M < M/2.
     by rewrite ltr_pdivlMr // gtr_nMr // ltrDl.
   have /= w := (Mp _ M02 _ sublevelUpsilon1q).
   apply (le_lt_trans w).
   rewrite ltr_pdivrMr // mul0r //.
set V := ball  (p : U) (`|p|+(M+1+1) : K).
have VsublevelUpsilon1  : sublevelUpsilon1 p `<=` V.
  move => /= x Kx.
  rewrite /V -ball_normE/ball_ /=.
  by rewrite (le_lt_trans (ler_normB _ _))// ltrD2l ltr_pwDr// Mp// ltrDl.
have B1 :  0 < `|p| + (M + 1 + 1).
  by rewrite ltr_wpDl// addr_gt0// ltr_wpDl.
have Vo : open V.
  by rewrite /V; exact: ball_open.
have cV : compact (closure V).
   rewrite closure_ballE closed_ballE//.
   apply: bounded_closed_compact; last by apply: closed_closed_ball_.
   exists (`|p| + (`|p| + (M + 1 +1))).
   rewrite /closed_ball_/=.
   split => //= x xB y Hy.
   rewrite -(subrKC p y).
   apply: (le_trans (ler_normD _ _)).
   rewrite distrC.
   apply (le_trans (lerD (lexx _ ) Hy)).
   by apply ltW.
apply: (compact_cluster_set1 _ cV ) => //.
  rewrite nbhsE/=.
  exists V; last by apply subset_closure.
  split => //.
  by apply VsublevelUpsilon1.
apply: (filterS (closure_subset VsublevelUpsilon1)).
exists 0; split => //= x /ltW x0.
rewrite -(closure_id (sublevelUpsilon1 p)).1;last first.
  by apply compact_closed =>//; apply compact_sublevelUpsilon1.
apply invariant_sublevelUpsilon1 => //.
by apply/set_mem/mem_sublevelUpsilon1/set_mem.
Qed.

End LaSalle_tilt.
