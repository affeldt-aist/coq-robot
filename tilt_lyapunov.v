From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra ring.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals order.
From mathcomp Require Import topology normedtype landau sequences derive realfun.
From mathcomp Require Import matrix_normedtype.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.
Require Import ode tilt_stability.

(**md**************************************************************************)
(* # Formalization of [benallegue2023itac] (1/2)                              *)
(*                                                                            *)
(* ```                                                                        *)
(*   Tilt.Upsilon1 == state-space                                             *)
(* ```                                                                        *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [benallegue2023itac]                                                     *)
(* https://hal.science/hal-04271257v1/file/benallegue2019tac_October_2022.pdf *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

(* Modelization of the physical problem *)
Section ya.
(* mesure de l'accelerometre *)
Variable K : realType.
Variable R : K -> 'M[K]_3. (* L/W *)
Variable g0 : K. (*standard gravity constant*)
Let w t := ang_vel R t. (* local frame of the sensor (gyroscope) *)
Definition x2 t : 'rV_3 := 'e_2 *m R t.
Definition y_a x t := - x t *m \S(w t) + 'D_1 x t + g0 *: x2 t. (* world frame *)
Variable p : K -> 'rV[K]_3.
Let v := fun t : K => 'D_1 p t *m R t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.

Lemma y_aE t (derivableR : forall t, derivable R t 1)
    (derivablep : forall t, derivable p t 1)
    (derivableDp : forall t, derivable ('D_1 p) t 1) :
  ('D_1 ('D_1 p) t + g0 *: 'e_2) *m R t = y_a v t.
Proof.
rewrite mulmxDl.
rewrite /y_a/= /= /x2.
congr +%R; last by rewrite scalemxAl.
rewrite -ang_vel_mxE/=; last 2 first.
 move=> t0.
 by rewrite rotation_sub.
 exact : derivableR.
rewrite [in RHS]derive_mulmx => //.
rewrite derive1mx_ang_vel => //; last first.
  by move=> t0; rewrite rotation_sub.
rewrite ang_vel_mxE// => //; last first.
  by move=> t0; rewrite rotation_sub.
rewrite addrCA.
rewrite -mulmxE.
rewrite -mulNmx.
rewrite [X in _ = _ X]addrC.
rewrite !mulNmx.
by rewrite -mulmxA /= addrN addr0.
Qed.

End ya.

Definition S2 {K : realType} := [set x : 'rV[K]_3 | `|x|_e = 1].

(* section III.A of [benallegue2023itac] *)
Section state_dynamics.
Variable K : realType.
Variable g0 : K.
Variable R : K -> 'M[K]_3.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.
Hypothesis derivableR : forall t, derivable R t 1.
Variable v : K -> 'rV[K]_3.
Let x1 t := v t.
Let x2 t : 'rV_3 := ('e_2) *m R t (* eqn (8) *). (* local frame ez ? *)
Let x1_dot t := 'D_1 x1 t.
Let x2_dot t := 'D_1 x2 t.
Let w t := ang_vel R t.

Lemma x2_S2 t : x2 t \in S2.
Proof.
by rewrite /S2 /x2 inE/= orth_preserves_norm ?enormeE ?rotation_sub.
Qed.

(* not used but could be interesting *)
Lemma dRu t (u : K -> 'rV[K]_3) (T : K -> 'M[K]_3) (w' := ang_vel T)
  : 'D_1 (fun t => u t *m T t) t = u t *m T t *m \S(w' t) + 'D_1 u t *m T t.
Proof.
rewrite derive_mulmx; last 2 first.
  admit.
  admit.
rewrite addrC.
congr(_+_).
rewrite -ang_vel_mxE; last 2 first.
  admit.
  admit.
rewrite -mulmxA.
rewrite mulmxE.
rewrite -derive1mx_ang_vel; last first.
  admit.
by [].
Abort.

(* eqn (10/11): we write x_1 * S(w) whereas it is - S(w) * x_1 in [benallegue2023itac] *)
Notation y_a := (y_a R g0).
Lemma derive_x1 t : 'D_1 x1 t = x1 t *m \S(w t) + y_a x1 t - g0 *: x2 t.
Proof.
rewrite /y_a/= -addrA addrK.
rewrite /x1.
rewrite addrCA addrA mulNmx /= /w.
by rewrite (addrC(-_)) subrr add0r.
Qed.

 (* eqn (11b): x_2 * S(w) instead of - S(w) * x_2 in [benallegue2023itac] *)
Lemma derive_x2 (t : K) : x2_dot t = x2 t *m \S( w t ).
Proof.
rewrite /w.
rewrite -ang_vel_mxE; last 2 first.
  by move=> ?; rewrite rotation_sub.
  by [].
rewrite /x2_dot.
rewrite /x2.
have ->: 'D_1 (fun t0 : K => 'e_2 *m (R t0)) t =
         'e_2 *m 'D_1 (fun t => (R t)) t.
  move => n /=.
  rewrite derive_mulmx//=.
  by rewrite derive_cst mul0mx add0r.
rewrite derive1mx_ang_vel /=; last first.
  by move=> ?; rewrite rotation_sub.
by rewrite mulmxA.
Qed.

End state_dynamics.

(* section III.A in [benallegue2023itac] *)
Section two_steps_first_order_estimator.
Context {K : realType}.
Variables gamma alpha1 : K.
Variable v : K -> 'rV[K]_3.
Variable R : K -> 'M[K]_3.
Hypothesis derivableR : forall t, derivable R t 1.
Let w t := ang_vel R t.
Variable x1_hat : K -> 'rV[K]_3.
Hypothesis derivable_x1_hat : forall t, derivable x1_hat t 1.
Variable x2_hat : K -> 'rV[K]_3.
Variable g0 : K.
Hypotheses g0_eq0 : g0 != 0.
Notation y_a := (y_a R g0 v).
Let x1 t := v t.
Let x2'_hat t := - (alpha1 / g0) *: (x1 t - x1_hat t). (* eqn (12b) *)
(* we write x^_1 * S(w) instead - S(w) * x^_1 in [benallegue2023itac] *)
Hypothesis eqn12a : forall t,
  'D_1 x1_hat t = x1_hat t *m \S(w t) + y_a t - g0 *: x2'_hat t. (* eqn (12a) *)
(* we write x^_2 * S(...) instead of - S(...) * x^_2
   and + gamma instead of - gamma in [benallegue2023itac] *)
Hypothesis eqn12c : forall t,
  'D_1 x2_hat t = x2_hat t *m \S(w t + gamma *: x2'_hat t *m \S(x2_hat t)). (* eqn (12c) *)
Hypothesis x2_hat_S2 : x2_hat 0 \in S2.
Hypothesis x2_hat_derivable : forall t, derivable x2_hat t 1.
Hypothesis v_derivable : forall t, derivable v t 1.
Notation x2 := (x2 R).
(* estimation error *)
Let error1 t := x2 t - x2'_hat t. (* p_1 in [benallegue2023ieeetac] *)
Let error2 t := x2 t - x2_hat t. (* \tilde{x_2} in [benallegue2023ieeetac] *)
Let error1_dot t := 'D_1 error1 t.
Let error2_dot t := 'D_1 error2 t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.
(* projection from the local frame to the world frame(?) *)
Let error1_p t := error1 t *m (R t)^T (* z_p_1 in [benallegue2023ieeetac] *).
Let error2_p t := error2 t *m (R t)^T.
Hypothesis norm_x2_hat : forall t, `|x2_hat t|_e = 1.

Let error1E : error1 = fun t => x2 t + (alpha1 / g0) *: (x1 t - x1_hat t).
Proof.
apply/funext => ?.
rewrite /error1 /x2; congr +%R.
by rewrite /x2'_hat scaleNr opprK.
Qed.

Let error2E t : error2 t = error2_p t *m R t.
Proof.
rewrite /error2 -mulmxA.
by rewrite orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

Let derivable_x2 t : derivable x2 t 1. Proof. exact: derivable_mulmx. Qed.

Let derivable_x2'_hat t : derivable x2'_hat t 1.
Proof. by apply: derivableZ => /=; exact: derivableB. Qed.

Let derivable_error1 t : derivable error1 t 1. Proof. exact: derivableB. Qed.

Let derivable_error2 t : derivable error2 t 1. Proof. exact: derivableB. Qed.

(* eqn (13a) *)
(* we write p_1 * S(w) instead of - S(w) * p1 in [benallegue2023itac] *)
Lemma derive_error1 t :
  'D_1 error1 t = error1 t *m \S(w t) - alpha1 *: error1 t.
Proof.
simpl in *.
rewrite error1E.
rewrite deriveD//=; last first.
  by apply: derivableZ => /=; exact: derivableB.
rewrite deriveZ//=; last exact: derivableB.
rewrite deriveB//.
rewrite !(derive_x2) // -/(x2 t) /=.
rewrite (derive_x1  g0 R) //.
rewrite -/(x2 t) -/(v t) -/(x1 t) -/(w t).
rewrite eqn12a.
transitivity ((x2 t + (alpha1 / g0) *: (x1 t - x1_hat t)) *m \S(w t)
              - alpha1 *: error1 t).
  transitivity (x2 t *m \S(w t) + (alpha1 / g0)
                *: (x1 t *m \S(w t) - g0 *: x2 t - (x1_hat t *m \S(w t) - g0 *: x2'_hat t))).
    congr (_ + _ *: _).
    rewrite -2![in LHS]addrA -[in RHS]addrA.
    congr +%R.
    rewrite opprD [in LHS]addrCA.
    rewrite opprK.
    rewrite [in RHS]opprB.
    rewrite [in RHS]addrCA [in RHS]addrC.
    rewrite -[in RHS]addrA.
    congr +%R.
    rewrite opprD.
    rewrite [LHS]addrA.
    rewrite (addrC (y_a t)).
    by rewrite subrK.
  rewrite (_ : x1 t *m \S(w t) - g0 *: x2 t -
                 (x1_hat t *m \S(w t) - g0 *: x2'_hat t) =
               (x1 t - x1_hat t) *m \S(w t) -
                 g0 *: (x2 t - x2'_hat t)); last first.
    rewrite mulmxBl scalerDr scalerN opprB addrA [LHS]addrC 2!addrA.
    rewrite -addrA; congr +%R.
      by rewrite addrC.
    by rewrite opprB addrC.
  rewrite -/(error1 t).
  rewrite scalerDr addrA scalemxAl -mulmxDl scalerN scalerA.
  by rewrite divfK.
by rewrite error1E.
Qed.

(* eqn (13b) *)
(* we write x~_2 * S(w) instead of - S(w) * x~_2 in [benallegue2023itac] *)
Lemma derive_error2 t :
  'D_1 error2 t = error2 t *m \S(w t) +
                  gamma *: (error2 t - error1 t) *m \S(x2_hat t) ^+ 2.
Proof.
rewrite /error2.
rewrite [in LHS]deriveB//.
rewrite derive_x2//.
rewrite -/(x2 t) -/(w t) -/(error2 t).
rewrite eqn12c.
rewrite spinD.
rewrite -[in LHS]scalemxAl.
rewrite (spinZ gamma).
rewrite mulmxDr opprD [LHS]addrA.
rewrite [in LHS]addrC addrA (addrC _ (x2 t *m \S(w t))).
rewrite addrAC.
rewrite -mulmxBl -/(error2 t).
simpl in *.
rewrite -[in RHS]opprB.
rewrite scalerN mulNmx.
congr (_ - _).
rewrite -scalemxAr -[RHS]scalemxAl.
congr (_ *: _).
rewrite /error2 /error1.
rewrite opprB addrCA.
rewrite (addrC (x2 t)) addrK.
rewrite mulmxBl.
rewrite [X in _ = X + _](_ : _ = 0) ?add0r; last first.
  rewrite mulmxA.
  rewrite -(mulmxA(x2_hat t)) sqr_spin //.
  rewrite mulmxDr !mulmxA.
  rewrite dotmul1 // mul1mx.
  by rewrite mulmxN mulmx1 subrr.
rewrite expr2 -mulmxE fact215 -mulmxE -spin_crossmul.
rewrite [in RHS]mulmxA [in RHS]spinE spinE spinE.
by rewrite [LHS](@lieC _ (vec3 K)).
Qed.

Lemma x2_hatR t : x2_hat t *m (R t)^T = 'e_2 - error2_p t.
Proof.
rewrite /error2_p /error2 mulmxBl opprB addrCA.
rewrite [X in _ + X](_ : _ = 0) ?addr0//.
rewrite /x2 -mulmxA.
by rewrite orthogonal_mul_tr ?rotation_sub// mulmx1 subrr.
Qed.

(* eqn (14a) *)
Lemma derive_error1_p t : 'D_1 error1_p t = - alpha1 *: error1_p t.
Proof.
rewrite /error1.
rewrite derive_mulmx//=; last by rewrite derivable_trmx.
rewrite derive_error1.
rewrite mulmxBl addrAC.
apply/eqP.
rewrite subr_eq.
rewrite [in eqbRHS]addrC scaleNr scalemxAl subrr /=.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel //; last by move => t0; rewrite rotation_sub.
rewrite ang_vel_mxE //; last by move => t1 ; rewrite rotation_sub.
rewrite -/(w t) -mulmxA -mulmxDr trmx_mul tr_spin.
by rewrite mulNmx subrr mulmx0.
Qed.

Definition eqn14b_rhs x1 x2 := gamma *: (x2 - x1) *m \S('e_2 - x2) ^+ 2.

(* eqn (14b) *)
Lemma derive_error2_p t : 'D_1 error2_p t = eqn14b_rhs (error1_p t) (error2_p t).
Proof.
rewrite /eqn14b_rhs.
rewrite [LHS]derive_mulmx//=; last by rewrite derivable_trmx.
simpl in *.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel//=; last by move=> ?; rewrite rotation_sub.
rewrite !ang_vel_mxE//; last by move=> ?; rewrite rotation_sub.
rewrite trmx_mul mulmxA -mulmxDl.
rewrite derive_error2 /=.
rewrite -/(w t) tr_spin mulmxN.
rewrite -!addrA addrC addrA subrK.
rewrite -scalemxAl.
rewrite -!scalemxAl.
congr (_ *: _).
rewrite -x2_hatR.
rewrite -spin_similarity ?rotationV//.
rewrite trmxK.
rewrite [in RHS]expr2 -mulmxE !mulmxA.
rewrite -!mulNmx opprB.
congr (_ *m _ *m _).
rewrite -[in RHS]mulmxA.
rewrite orthogonal_tr_mul ?rotation_sub// mulmx1.
congr (_ *m _).
rewrite -/(error2 _).
rewrite error2E.
rewrite mulmxDl.
congr (_ + _)%R.
by rewrite /error1 -mulmxA orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

End two_steps_first_order_estimator.

Module Tilt.
Section tilt.
Context {K : realType}.
Variables alpha1 gamma : K.

Definition eqn_functional (f : K -> 'rV[K]_6) : K -> 'rV[K]_6 :=
  let error1_p_dot := Left \o f in
  let error2_p_dot := Right \o f in
  fun t => row_mx
    (- alpha1 *: error1_p_dot t)
    (eqn14b_rhs gamma (error1_p_dot t) (error2_p_dot t)).

Definition eqn (dot_zp1_z2 : 'rV[K]_6) : 'rV[K]_6 :=
  let dot_zp1 := Left dot_zp1_z2 in
  let dot_z2 := Right dot_zp1_z2 in
  row_mx (- alpha1 *: dot_zp1)
         (eqn14b_rhs gamma dot_zp1 dot_z2).

Lemma eqnE (f : K -> 'rV[K]_6) t : eqn (f t) = eqn_functional f t.
Proof. by []. Qed.

Lemma eqn_functionalE f t : eqn_functional f t = eqn (f t).
Proof. by []. Qed.

Definition Upsilon1 := [set x : 'rV[K]_6 | `| 'e_2 - Right x |_e = 1].

Definition point1 : 'rV[K]_6 := 0.
Definition point2 : 'rV[K]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2).

Lemma point1_neq2 : point1 != point2.
Proof.
apply/eqP; rewrite /point1 /point2 => /eqP.
rewrite eq_sym (@row_mx_eq0 _ 1 3 3) eqxx/= => /eqP/rowP/(_ ord_max).
by rewrite !mxE eqxx/= mulr1; apply/eqP; rewrite pnatr_eq0.
Qed.

Definition points := [set point1; point2].

End tilt.
End Tilt.

Section tilt_eqn.
Context {K : realType}.
Variables alpha1 gamma : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Let phi := Tilt.eqn alpha1 gamma.

Lemma tilt_eqn_locally_lipschitz : locally_lipschitz phi.
Proof.
move=> /= x.
exists (PosNum ltr01).
near (pinfty_nbhs K) => k.
have k0 : 0 < k by [].
exists (PosNum k0) => /= => -[/= x0 x1] [x0B x1B].
rewrite (opp_row_mx (n1:=3)) (add_row_mx (n1:=3)).
rewrite !scaleNr opprK/=.
rewrite addrC -scalerBr.
rewrite /eqn14b_rhs.
rewrite -!scalemxAl -scalerBr.
rewrite (norm_rowmx (m:=0) (n1:=2) (n2:=2)).
rewrite ge_max; apply/andP; split.
- rewrite mx_normZ.
  rewrite -linearB/=.
  rewrite ler_pM//.
  rewrite distrC.
  exact/le_trans/(@left_norm_le _ 2 2).
- rewrite mx_normZ.
  set a := Right x0 - Left x0.
  set b := Right x1 - Left x1.
  set c := \S('e_2 - Right x0) ^+ 2.
  set d := \S('e_2 - Right x1) ^+ 2.
  have abound : `|a| <= 2 * (`|x| + 1).
    rewrite (le_trans (ler_normB _ _ ))// mulrDl lerD// mul1r.
      rewrite (le_trans (right_norm_le _))//.
      exact: closed_ball_bounded.
    rewrite (le_trans (left_norm_le _))//.
    exact: closed_ball_bounded.
  (* todo: find some bound and show *)
  have sbound x' : closed_ball x 1 x' ->  `|'e_2 - Right x'| <= 2+`|x|.
    move=> cb.
    rewrite (le_trans (ler_normB _ _))// [in leRHS](natrD _ 1 1) -addrA lerD//.
      exact: mx_norm_delta_mx.
    by rewrite (le_trans (right_norm_le _))// addrC closed_ball_bounded.
  have dbound : `|d| <=  3 * (2 + `|x|) ^+ 2.
    rewrite /d.
    apply: (le_trans (spin_sq_norm_bound _)).
    apply ler_pM => //.
    suff h :  `|'e_2 - Right x1| <= 2 + `|x|.
       by apply ler_pM => //; apply normr_ge0.
    by apply sbound.
  rewrite -ler_pdivlMl; last by rewrite normr_gt0 lt0r_neq0.
  rewrite -(subrKA (a *m d) (a *m c )) (le_trans (ler_normD _ _))//.
  rewrite -[X in `|X| + _]mulmxBr.
  rewrite -[X in _ + `|X|]mulmxBl.
  rewrite (splitr  `|gamma|^-1) mulrDl.
  rewrite -invrM ?unitfE//; last first.
    by rewrite gt_eqF// gtr0_norm.
  rewrite lerD//.
  + apply: (le_trans (mx_norm_mul _ _)).
    have h0 := spin_sq_dist_bound ('e_2 - Right x0) ('e_2 - Right x1).
    apply : (le_trans (ler_pM _ _ (le_refl _) h0)) => //.
    have -> : 'e_2 - Right x0 - ('e_2 - Right x1) = Right x1 - Right x0.
      by rewrite opprB addrC addrA subrK.
    rewrite !mulrA.
    apply ler_pM => //; last by rewrite distrC -linearB; exact: right_norm_le.
    rewrite (mulrC 3) -!mulrA.
    apply : (le_trans (ler_pM _ _ abound (le_refl _))) => //.
    rewrite !mulrA.
    rewrite ler_pdivlMl; last first.
       by rewrite mulr_gt0// gtr0_norm.
    rewrite !mulrA.
    suff h : `|'e_2 - Right x0| + `|'e_2 - Right x1| <= 2 * (2 + `|x|).
      exact: (le_trans (ler_pM _ _ (le_refl _) h)).
    by rewrite mulrDl mul1r lerD//; apply sbound.
  + rewrite (le_trans (mx_norm_mul _ _))//.
    rewrite opprB -addrA (addrC (-Left x0)) addrA (addrC (Left x1)) addrA  -(addrA (Right x0 - _)).
    rewrite mulrC.
    apply (@le_trans _ _ (`| d| *  (6 * `|x0 - x1|))).
    apply ler_pM => //.
    rewrite [in leRHS](natrM _ 3 2)// -mulrA ler_pM//.
    rewrite (le_trans (ler_normD _ _))//.
    rewrite mulrDl lerD// mul1r.
      by rewrite -linearB; apply: right_norm_le.
    by rewrite distrC -linearB/=; apply: left_norm_le.
    rewrite (le_trans (ler_pM  _ _ dbound (lexx _ )))//.
    rewrite ler_pdivlMl; last first.
      by rewrite mulr_gt0// gtr0_norm.
    by rewrite !mulrA ler_pM.
Unshelve. all: by end_near. Qed.

Lemma tilt_state_spaceS : state_space phi Tilt.Upsilon1 `<=` Tilt.Upsilon1.
Proof.
move => p [y [Delta [y0_init1 deri]]].
have [Delta0|Delta0] := leP 0 Delta; last first.
  move=> -[t [+ x]].
  rewrite in_itv/= => -/andP[x0 xDelta].
  have := lt_trans xDelta Delta0.
  by rewrite ltNge x0.
rewrite /Tilt.Upsilon1.
have : {in `]0, Delta[, (fun t => ('e_2 - Right (y t)) *d (('e_2 - Right (y t))))^`() =1 0}.
  move => x xd /=.
  transitivity ((fun t => -2 * (Right(y^`()%classic t) *d ('e_2 - Right (y t)))) x).
    rewrite !derive1E.
    have ? : derivable y x 1.
      apply deri.
      rewrite inE/= in xd.
      apply: subset_itvr xd.
      by rewrite bnd_simp.
    rewrite derive_mx//.
    rewrite /dotmul.
    under eq_fun do rewrite dotmulP /=.
    rewrite dotmulP.
    rewrite !mxE /= mulr1n.
    under eq_fun do rewrite !mxE /= mulr1n.
    rewrite !derive_dotmul/=; last 2 first.
      apply: derivableB => //=;  apply : derivable_rsubmx => //=.
      by apply: derivableB => //=; apply: derivable_rsubmx => //=.
    rewrite /dotmul /=.
    rewrite [in RHS]mulr2n [RHS]mulNr [in RHS]mulrDl.
    rewrite !mul1r !dotmulP /= dotmulC [in RHS]dotmulC !linearD /=.
    rewrite !mxE /= !mulr1n.
    have -> : 'D_1 (fun x2 : K => 'e_2 - Right (y x2)) x = - Right ('D_1 y x).
      rewrite deriveB /= ; last 2 first.
        exact: derivable_cst.
        by apply: derivable_rsubmx.
      rewrite derive_cst /= sub0r; congr (- _).
      by apply: derive_rsubmx.
    rewrite -(_ : 'D_1 y x =
        (\matrix_(i, j) 'D_1 (fun t0 : K => y t0 i j) x)); last first.
      apply/matrixP => a b; rewrite !mxE.
      by rewrite derive_mx//= ?mxE//.
    ring.
  have Rsu t0 : t0 \in `[0, Delta[ -> Right (y^`()%classic t0) =
               (gamma *: (Right (y t0) - Left (y t0)) *m \S('e_2 - Right (y t0)) ^+ 2).
    rewrite inE/=.
    rewrite /is_sol_on0o/= in deri.
    by move/deri => [_ ->]; rewrite row_mxKr.
  rewrite /dotmul.
  transitivity (-2 * (gamma *: (Right (y x) -
                          Left (y x)) *m \S('e_2 - Right (y x)) ^+ 2 *m
                                          ('e_2 - Right (y x))^T) 0 0).
    rewrite Rsu//.
    move: xd.
    rewrite !inE/=.
    by apply: subset_itvr; rewrite bnd_simp.
  rewrite !mulmxA.
  apply/eqP.
  rewrite mulf_eq0 /= oppr_eq0 ?pnatr_eq0 /= -!mulmxA spin_mul_tr.
  by rewrite !mulmx0 mxE.
move => h [t [t0d ->]].
have norm_constant t0 : t0 \in `[0, Delta[ ->
    `|'e_2 - Right (y t0)|_e ^+ 2 = `|'e_2 - Right (y 0)|_e ^+ 2.
  have : forall x0, x0 \in `]0,Delta[ ->
      is_derive x0 (1:K) (fun x : K => `|'e_2 - Right (y x)|_e ^+ 2) 0.
    move => x0 x0d.
    have ? : derivable y x0 1.
      apply deri.
      rewrite inE/= in x0d.
      apply: subset_itvr x0d.
      by rewrite bnd_simp.
    apply: DeriveDef.
      apply/derivable_enorm_squared => //=.
      apply/derivableB => //=.
      by apply/derivable_rsubmx => //.
    rewrite -derive1E.
    have := h _ x0d.
    under eq_fun do rewrite dotmulvv /=.
    by apply.
  rewrite /=.
  move => hd0 t0d'.
  apply/esym.
  have {}t0d'' : t0 \in `[0, t0].
    rewrite inE/= in_itv/= lexx andbT.
    move: t0d'.
    by rewrite inE/= => /andP[].
  have {}hd0 : forall x0 : K,
      x0 \in `]0, t0[ -> is_derive x0 1 (fun x : K => `| 'e_2 - Right (y x) |_e ^+ 2) 0.
    move=> x0 x00t0.
    apply: hd0.
    move: x00t0; rewrite !inE/=.
    apply: subset_itvl; rewrite bnd_simp.
    by move: t0d'; rewrite inE/= in_itv/= => /andP[_ /ltW].
  have := is_derive_0_is_cst_new' t0d'' _ hd0.
  clear t0d'' hd0.
  apply => //; last first.
    rewrite inE/= in_itv/= lexx/=.
    by move: t0d'; rewrite inE/= in_itv/= => /andP[].
  apply: (@within_continuous_comp _ _ _ _ _ (fun x => `|'e_2 - Right x|_e ^+ 2) y) => //=.
    by move: t0d'; rewrite inE/= in_itv/= => /andP[].
  move=> z _.
  apply: differentiable_continuous => //.
  apply: differentiable_enorm_squared => /=.
  exact: differentiableB.
  move: t0d; rewrite in_itv/= => /andP[t_ge0 tDelta].
  rewrite /is_sol_on0o/= in deri.
  have cont : {in `[0, t0], continuous y}.
    move=> t' t'0D.
    rewrite inE/= in t'0D.
    apply: differentiable_continuous.
    apply/derivable1_diffP.
    apply deri.
    apply: subset_itvl t'0D.
    rewrite bnd_simp.
    by move: t0d'; rewrite inE/= in_itv/= => /andP[].
  move/continuous_in_subspaceT : cont.
  apply: continuous_subspaceW.
  by apply: subset_itvl; rewrite bnd_simp.
suff: `|'e_2 - Right (y t)|_e ^+ 2 = 1.
  move=> /(congr1 Num.sqrt).
  by rewrite sqrtr1 sqr_sqrtr// dotmulvv sqr_ge0.
rewrite norm_constant//; last first.
  by rewrite inE.
move: y0_init1.
rewrite inE /Tilt.Upsilon1 /= => ->.
by rewrite expr2 mulr1.
Qed.

Lemma tilt_point1_in_state_space : @Tilt.point1 K \in Tilt.Upsilon1.
Proof.
rewrite inE /Tilt.Upsilon1 /Tilt.point1/=.
 by rewrite rsubmx_const /= subr0 enormeE.
Qed.

Lemma equilibrium_tilt_point1 :
  is_equilibrium_point phi Tilt.Upsilon1 Tilt.point1.
Proof.
split.
- exact: tilt_point1_in_state_space.
- move=> Delta.
  move=> t t0Delta.
  split; first exact: derivable_cst.
  rewrite derive1E derive_cst /Tilt.point1; apply/eqP.
  rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP; split.
    rewrite scaler_eq0; apply/orP; right; apply/eqP/rowP  => i.
    by rewrite lsubmx_const.
  apply/eqP/rowP; move => i; apply/eqP.
  rewrite /eqn14b_rhs.
  set N := (X in _ *: X *m _); have : N = 0.
    rewrite /N /=; apply /rowP; move => a.
    rewrite !mxE.
    by rewrite subrr.
  by move => n; rewrite n scaler0 mul0mx.
Qed.

Lemma tilt_point2_in_state_space : @Tilt.point2 K \in Tilt.Upsilon1.
Proof.
rewrite inE /Tilt.Upsilon1 /Tilt.point2 /=.
rewrite row_mxKr.
rewrite -[X in X - _ ]scale1r.
rewrite -scalerBl enormZ enormeE mulr1 distrC.
rewrite [X in _ - X](_:1 = 1%:R) //.
by rewrite -natrB //= normr1.
Qed.

Lemma equilibrium_tilt_point2 :
  is_equilibrium_point phi Tilt.Upsilon1 Tilt.point2.
Proof.
split; first exact: tilt_point2_in_state_space.
move=> Delta.
move=> t t0Delta.
split; first exact: derivable_cst.
rewrite derive1E derive_cst; apply/eqP.
rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
set N := (X in _ *: X == 0 /\ _).
have N0 : N = 0.
  apply/rowP; move=> i; rewrite !mxE; case: splitP.
    by move => j _; rewrite mxE.
  move=> k /= i3k.
  have := ltn_ord i.
  by rewrite i3k -ltn_subRL subnn.
split.
  by rewrite scaler_eq0 N0 eqxx orbT.
rewrite /eqn14b_rhs.
rewrite -scalemxAl scalemx_eq0 gt_eqF//=.
rewrite -[Left Tilt.point2]/N N0 subr0.
set M := (X in X *m _); rewrite -/M.
have ME : M = 2 *: 'e_2.
  apply/rowP => i; rewrite !mxE eqxx/=.
  case: splitP => [j ij|j]/=.
    have := ltn_ord j.
    by rewrite -ij.
  move/eqP.
  rewrite eqn_add2l => /eqP /ord_inj ->.
  by rewrite !mxE eqxx/=.
rewrite ME -scalemxAl scalemx_eq0 pnatr_eq0/=.
rewrite [X in X *: _](_ : _ = 1 + 1)// scalerDl scale1r opprD addrA.
rewrite subrr sub0r spinN sqrrN expr2 -mulmxE mulmxA.
rewrite (_ : 'e_2 *m _ = 0) ?mul0mx//; apply: trmx_inj.
by rewrite trmx_mul trmx0 tr_spin mulNmx spin_mul_tr oppr0.
Qed.

End tilt_eqn.

(* technical section, skip on a first reading *)
Section u2.
Context {K : realType}.

Definition u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2) [eta (fun=> 0) with
  (0,0) |-> 1,
  (0,1) |-> -2^-1,
  (1,0) |-> -2^-1,
  (1,1) |-> 1] (i, j).

Lemma u2neq0 : u2 != 0.
Proof. by apply/matrix0Pn; exists 1, 1; rewrite mxE /= oner_neq0. Qed.

Lemma u2_sym : u2 \is sym 2 K.
Proof.
rewrite /= symE.
apply/eqP/matrixP.
move => i j.
rewrite !mxE/=.
case: ifPn => [/eqP[->{i} ->{j}//]|].
case: ifPn => [/eqP[->{i} ->{j}//]|].
case: ifPn => [/eqP[->{i} ->{j}//]|].
case: ifPn => [/eqP[->{i} ->{j}//]|].
by move: i j => [[|[|//]]] /= ? [[|[|]]].
Qed.

Lemma tr_u2 : \tr u2 = 2.
Proof. by rewrite /u2/= /mxtrace /= sum2E/= !mxE/=. Qed.

Lemma det_u2 : \det u2 = 3/4.
Proof. by rewrite /u2 det_mx22 /= !mxE /=; field. Qed.

Lemma posdefmxu2 : posdefmx u2.
Proof.
split; first exact: u2_sym.
move=> a.
move/eigenvalueP => [u] /[swap] u0 H.
have a_eigen : eigenvalue u2 a.
  apply/eigenvalueP.
  exists u. rewrite /u2.
    exact: H.
  exact: u0.
have : root (char_poly u2) a.
  rewrite -eigenvalue_root_char.
  exact : a_eigen.
rewrite char_poly2 tr_u2 det_u2 rootE => a_root .
have char_poly_fact : 'X^2 - 2%:P * 'X + (3/4)%:P =
    ('X - (1%:R / 2)%:P) * ('X - (3%:R / 2)%:P) :> {poly K}.
  rewrite mulrBr mulrBl -expr2 -!addrA; congr +%R.
  rewrite mulrBl opprB addrCA addrC; congr +%R.
    by rewrite -[RHS]polyCM; congr (_%:P); field.
  rewrite [in RHS]mulrC -opprD -mulrDr mulrC; congr (- (_ * _)).
  by rewrite -polyCD; congr (_%:P); by field.
move: a_root.
rewrite char_poly_fact hornerM !hornerXsubC.
by rewrite mulf_eq0 => /orP[|]; rewrite subr_eq0 => /eqP ->; rewrite divr_gt0.
Qed.

Lemma u2_quadratic_form_gt0 (v : 'rV_2) :
  v != 0 -> 0 < (v *m u2 *m v^T) 0 0.
Proof.
move=> v0.
rewrite !(mxE,sum2E,mulr1)/= !mulrDl -!expr2.
rewrite [ltRHS](_ : _ = v``_0 ^+ 2 - v``_1 * v``_0 + v``_1 ^+ 2); last first.
  rewrite -!addrA; congr +%R.
  rewrite !addrA; congr +%R.
  rewrite (mulrC _ v``_0) -mulrA -mulrDr.
  rewrite mulrC -mulNr; congr *%R.
  rewrite mulrC -mulrDr -mulr2n.
  rewrite mulNr; congr (- _).
  rewrite -(mulr_natl v``_1).
  by rewrite mulrA mulVf// ?mul1r.
rewrite [ltRHS](_ : _ = (v``_0 - 2^-1 * v``_1) ^+ 2 + 3 / 4 * v``_1 ^+ 2); last first.
  rewrite sqrrB -!addrA; congr +%R.
  rewrite -mulNrn mulrCA -(mulr_natl (- _) 2) mulrN !mulrA divff ?mul1r//.
  rewrite mulrC; congr +%R.
  rewrite -mulrA -expr2 exprMn -mulrDl.
  rewrite (expr2 2^-1).
  rewrite -invfM -div1r -natrM -mulrDl.
  by rewrite nat1r divff// mul1r.
rewrite ltNge le_eqVlt negb_or -leNgt addr_ge0 ?(sqr_ge0,mulr_ge0)// andbT.
rewrite paddr_eq0 ?(sqr_ge0,mulr_ge0)//.
apply/negP => /andP[]; rewrite sqrf_eq0 => /[swap].
rewrite mulf_eq0/= sqrf_eq0 mulf_eq0 invr_eq0 !pnatr_eq0/= => /eqP v10.
rewrite v10 mulr0 subr0 => /eqP v00.
move/negP : v0; apply.
apply/eqP/rowP => -[[i|[j|//]]]; rewrite !mxE//.
by rewrite (_ : Ordinal _ = 0)//; exact/val_inj.
by rewrite (_ : Ordinal _ = 1)//; exact/val_inj.
Qed.

End u2.

Section V1.
Local Open Scope classical_set_scope.
Context {K : realType}.
Variables alpha1 gamma : K.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.

Definition V1 (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  `|zp1|_e ^+ 2 / (2 * alpha1) + `|z2|_e ^+ 2 / (2 * gamma).

Lemma V1_is_Lyapunov_candidate :
  is_Lyapunov_candidate V1 [set: 'rV_6] Tilt.point1.
Proof.
rewrite /V1 /Tilt.point1; split; first by rewrite inE.
split.
  by rewrite lsubmx_const rsubmx_const enorm0 expr0n/= !mul0r add0r.
move=> /= z_near _ z0.
have /orP[lz0|rz0] : (Left z_near != 0) || (Right z_near != 0).
  rewrite -negb_and.
  apply: contra z0 => /andP[/eqP l0 /eqP r0].
  rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
  apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?;
  by rewrite mxE.
- set rsub := Right z_near.
  have : `|rsub|_e >= 0 by rewrite enorm_ge0.
  set lsub := Left z_near.
  move=> nor.
  have normlsub : `|lsub|_e > 0 by rewrite enorm_gt0.
  rewrite ltr_pwDl//.
    by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
  by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
- rewrite ltr_pwDr//.
    by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0 ?enorm_gt0.
  by rewrite divr_ge0 ?exprn_ge0 ?enorm_ge0 ?mulr_ge0// ltW.
Unshelve. all: by end_near. Qed.

Definition V1dot (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  - `|zp1|_e ^+ 2 + (z2 *m (\S('e_2 - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2 - z2))^+2 *m zp1^T)``_0.

End V1.

Section hurwitz.
Context {K : realType}.

(* thm 4.6 p136*)
Definition hurwitz n (A : 'M[K]_n) : Prop :=
  (forall a, eigenvalue A a -> a < 0).

(* thm 4.7 p139 + fact: it is exponentially stable*)
Definition locally_exponentially_stable_at n (eqn : 'rV[K]_n -> 'rV[K]_n)
    (point : 'rV[K]_n) : Prop :=
  hurwitz (jacobian eqn point).

Lemma tilt_eqn_is_locally_exponentially_stable_at_0 alpha1 gamma :
  locally_exponentially_stable_at (Tilt.eqn alpha1 gamma) Tilt.point1.
Proof.
rewrite /locally_exponentially_stable_at /jacobian /hurwitz.
rewrite /lin1_mx/= /Tilt.eqn /eqn14b_rhs/=.
move => a.
move/eigenvalueP => [u] /[swap] u0 H.
have a_eigen : eigenvalue (jacobian (Tilt.eqn alpha1 gamma) Tilt.point1) a.
  apply/eigenvalueP.
  exists u.
    exact: H.
  exact: u0.
have : root (char_poly (jacobian (Tilt.eqn alpha1 gamma) Tilt.point1)) a.
  rewrite -eigenvalue_root_char.
  exact : a_eigen.
rewrite /Tilt.eqn /jacobian.
Abort.

End hurwitz.

Section tilt_eqn_Lyapunov.
Local Open Scope classical_set_scope.
Context {K : realType}.
Variables alpha1 gamma : K.
Hypotheses (alpha1_gt0 : 0 < alpha1) (gamma_gt0 : 0 < gamma).
Let phi := Tilt.eqn alpha1 gamma.
Variable Delta : K.

Lemma derive_zp1 (t : K) (sol : K -> 'rV_6) :
  is_sol_on0o phi (BLeft Delta) sol ->
  t \in `[0, Delta[ -> 'D_1 (Left \o sol) t = - alpha1 *: Left (sol t).
Proof.
move=> /= deri /[!inE]/= t0Delta.
have [derivable_sol] := deri _ t0Delta.
move=> /(congr1 Left).
rewrite derive1E.
rewrite row_mxKl.
move=> <-.
by rewrite derive_lsubmx.
Qed.

Lemma derive_z2 (z : K) (sol : K -> 'rV_6) :
  is_sol_on0o phi (BLeft Delta) sol ->
  z \in `[0, Delta[ -> 'D_1 (Right \o sol) z =
  gamma *: (Right (sol z) - Left (sol z)) *m \S('e_2 - Right (sol z)) ^+ 2.
Proof.
move=> deriv /[!inE]/= z0Delta.
have [derivable_sol +] := deriv _ z0Delta.
move => /(congr1 Right).
rewrite derive1E.
by rewrite row_mxKr => ?; rewrite derive_rsubmx.
Qed.

Lemma is_sol_state_space_tilt (sol : K -> 'rV_6) t :
  t \in `[0, Delta[%R ->
  sol 0 \in Tilt.Upsilon1 ->
  is_sol_on0o phi (BLeft Delta) sol ->
  Tilt.Upsilon1 (sol t).
Proof.
move=> t0Delta sol0 deriv_sol.
move: t0Delta.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<- Delta0|t0 tDelta].
  exact/set_mem.
apply: (@tilt_state_spaceS _ alpha1 gamma) => //=.
exists sol, Delta; split => //=.
exists t; split => //.
by rewrite in_itv/= (ltW t0) tDelta.
Qed.

Lemma enorm_e2z2 (sol : K -> 'rV_6) (z : K)
    (z2 := Right \o sol) (zp1 := Left \o sol) (u := 'e_2 - z2 z) :
  z \in `[0, Delta[%R ->
  sol 0 \in Tilt.Upsilon1 ->
  is_sol_on0o phi (BLeft Delta) sol -> `|u|_e = 1.
Proof.
move=> z0Delta sol0 dtraj.
suff: Tilt.Upsilon1 (row_mx (zp1 z) (z2 z)).
  by rewrite /Tilt.Upsilon1/= row_mxKr.
rewrite /zp1 /z2 hsubmxK /=.
by apply: is_sol_state_space_tilt => //.
Qed.

Lemma angvel_sqr (sol : K -> 'rV_6) (z : K)  (z2 := fun r : K => Right (sol r) : 'rV_3)
  (w := (z2 z) *m \S('e_2)) (u := 'e_2 - z2 z) :
  z \in `[0, Delta[%R ->
  sol 0 \in Tilt.Upsilon1 ->
  is_sol_on0o phi (BLeft Delta) sol ->
  (w *m \S(u)) *d (w *m \S(u)) = (w *d w) * (u *d u) - (w *d u) ^+ 2.
Proof.
move=> z0Delta sol0 dtraj.
rewrite /dotmul !trmx_mul !tr_spin !mulNmx mulmxN opprK mulmxN !dotmulP.
have key_ortho : (z2 z *m \S('e_2)) *d u = 0.
 by rewrite dotmulC; exact/ortho_spin.
rewrite key_ortho expr2.
rewrite [in RHS]mxE.
rewrite [X in _ =  - (w *m (\S('e_2) *m (z2 z)^T)) 0 0 * (u *d u)%:M 0 0 - 0%:M 0 0 * X]mxE.
rewrite mulr1n mulr0 subr0/=.
rewrite /u -/w /dotmul.
have Hw_ortho : (w *d u) = 0 by rewrite /u dotmulC ortho_spin.
rewrite !mulmxA dotmulP dotmulvv enorm_e2z2 // expr2 mulr1.
rewrite [X in _ =  - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1n /=.
rewrite [X in _ =   - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1.
have wu0 : w *m u^T *m u = 0 by rewrite dotmulP Hw_ortho mul_scalar_mx scale0r.
rewrite -[in LHS](mulmxA w) sqr_spin; last by rewrite -/u enorm_e2z2.
rewrite [in LHS]mulmxBr mulmxA wu0 sub0r.
by rewrite 2!mulNmx mulmx1 mxE.
Qed.

Lemma neg_spin (sol : K -> 'rV_6) (z : K) :
  z \in `[0, Delta[%R ->
  sol 0 \in Tilt.Upsilon1 ->
  is_sol_on0o phi (BLeft Delta) sol ->
  `|Right (sol z) *m \S('e_2) *m - \S('e_2 - Right (sol z))|_e =
  `|Right (sol z) *m \S('e_2)|_e.
Proof.
move=> z0Delta sol0 dtraj.
rewrite mulmxN enormN.
pose zp1 := fun r => Left (sol r).
pose z2 := fun r => Right (sol r).
set w := (z2 z) *m \S('e_2).
have Upsilon1_traj : Tilt.Upsilon1 (sol z) by apply/is_sol_state_space_tilt.
rewrite /enorm.
rewrite !dotmulvv [RHS]sqrtr_sqr sqrtr_sqr.
have Hnorm_sq : `|w *m \S('e_2 - Right (sol z))|_e ^+ 2 = `|w|_e ^+ 2.
  rewrite -!dotmulvv angvel_sqr// !dotmulvv enorm_e2z2//=.
  rewrite -!dotmulvv expr2 !mul1r mulr1.
  have -> : w *d ('e_2 - Right (sol z)) = 0 by rewrite dotmulC ortho_spin.
  by rewrite expr2 mul0r subr0.
rewrite !normr_enorm.
by move/sqr_inj : Hnorm_sq => ->//; rewrite ?nnegrE ?enorm_ge0.
Qed.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

Lemma V1dotE (z : K) (sol : K -> 'rV_6)
  (zp1 := Left \o sol) (z2 := Right \o sol) :
  is_sol_on0o phi (BLeft Delta) sol ->
  z \in `[0, Delta[ ->
  V1dot (sol z) =
    c1 *: (2 *: 'D_1 zp1 z *m (Left (sol z))^T) 0 0 +
    c2 *: (2 *: 'D_1 z2 z *m (Right (sol z))^T) 0 0.
Proof.
move=> ? zd.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC.
rewrite mulVf// div1r.
rewrite derive_zp1 // -scalemxAl mxE [X in X + _](mulrA (alpha1^-1) (- alpha1)).
rewrite mulrN mulVf ?gt_eqF// mulN1r.
rewrite derive_z2 // -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE.
rewrite scalerA mulVf ?gt_eqF// scale1r.
rewrite enorm_squared /V1dot.
congr +%R.
rewrite -2![in LHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
rewrite -[X in (X *m (_ *m _)) 0 0 = _]trmxK.
rewrite -[X in (_ *m (X *m _)) 0 0 = _]trmxK.
rewrite mulmxA -trmx_mul -trmx_mul [LHS]mxE.
rewrite -(mulmxA (Right (sol z) - (Left (sol z)))) mulmxE -expr2.
rewrite tr_sqr_spin.
by rewrite mulmxA.
Qed.

Lemma derive_along_V1 t (sol : K -> 'rV_6) :
  t \in `]0, Delta[ ->
  is_sol_on0o phi (BLeft Delta) sol ->
  (forall t, t \in `]0, Delta[ -> differentiable sol t) ->
  'D~(sol) (V1 alpha1 gamma) t = V1dot (sol t).
Proof.
move=> t0Delta tilt_eqnx dif1.
rewrite /V1 derive_alongD; last 3 first.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl => //; last 2 first.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  exact: dif1.
rewrite derive_alongMl => //; last 2 first.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
rewrite -fctE /= !derive_along_enorm_squared//=.
- rewrite V1dotE.
    by rewrite /c1 /c2 !invfM.
  rewrite /= in tilt_eqnx.
  exact: tilt_eqnx.
- move: t0Delta.
  by rewrite !inE/=; apply: subset_itvr; rewrite bnd_simp.
- exact/differentiable_lsubmx_comp.
- exact: dif1.
- exact: dif1.
Qed.

Definition u1 (sol : K -> 'rV[K]_6) t
  (zp1 := Left \o sol) (z2 := Right \o sol)
  (w := z2 t *m \S('e_2)) : 'rV[K]_2 :=
  \row_(i < 2) [eta (fun=> 0) with 0 |-> `|zp1 t|_e, 1 |-> `|w|_e] i.

Lemma V1dot_ub (sol : K -> 'rV[K]_6) (zp1 := Left \o sol) (z2 := Right \o sol) :
  sol 0 \in Tilt.Upsilon1 ->
  is_sol_on0o phi (BLeft Delta) sol ->
  forall t, t \in `[0, Delta[%R ->
    V1dot (sol t) <= (- (u1 sol t) *m u2 *m (u1 sol t)^T) 0 0.
Proof.
move=> sol0 dtraj z z0Delta.
set w := z2 z *m \S('e_2).
rewrite /V1dot.
rewrite mxE norm_spin mxE addrA expr2 mulmxA.
have -> : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2).
  by rewrite spinD spinN -tr_spin !mulmxDr !mul_tr_spin !addr0.
rewrite -dotmulNv addrC -mulmxN -expr2.
have cauchy : ((w *m - \S('e_2 - z2 z) *d (zp1 z))%:M : 'rV_1) 0 0 <=
              `|w *m - \S('e_2 - z2 z)|_e * `|zp1 z|_e.
  rewrite mxE /= mulr1n (le_trans (ler_norm _)) //.
  rewrite -ler_sqr // ; last first.
    by rewrite nnegrE // mulr_ge0 ?enorm_ge0.
  by rewrite exprMn sqr_normr (le_trans (CauchySchwarz_rV _ _)) // !dotmulvv.
apply: (@le_trans _ _ (`|w *m - \S('e_2 - z2 z)|_e * `|zp1 z|_e + (- `|zp1 z|_e ^+ 2 - `|w|_e ^+ 2))).
  rewrite lerD2r.
  rewrite (le_trans _ cauchy) //.
  by rewrite mxE eqxx mulr1n.
rewrite neg_spin /u1 /u2 //.
rewrite mxE.
rewrite !sum2E/= ![in leRHS]mxE !sum2E/= ![in leRHS]mxE /=.
rewrite !mulr1 mulrN mulNr opprK mulrDl mulNr -expr2.
rewrite [in leLHS] addrCA -!addrA lerD2l mulrDl (mulNr `|w|_e).
rewrite -expr2 !addrA lerD2r !(mulrN , mulNr) opprK -mulrA.
rewrite [in leRHS](mulrC (_ / 2)) (mulrC 2^-1) -mulrDr -splitr.
by rewrite [leRHS]mulrC.
Qed.

Lemma V1dot_eq0_p1_or_p2 (sol : K -> 'rV[K]_6) (t : K) :
  is_sol_on0o phi (BLeft Delta) sol ->
  sol 0 \in Tilt.Upsilon1 ->
  t \in `[0, Delta[%R ->
  V1dot (sol t) = 0 ->
  sol t = Tilt.point1 \/ sol t = Tilt.point2.
Proof.
move => solP sol0 t0d V1dsol.
have h : u1 sol t = 0.
  case: (u1 sol t =P 0) => [-> // |/eqP hsol].
  have := V1dot_ub sol0 solP t0d.
  have := u2_quadratic_form_gt0 hsol.
  rewrite V1dsol !mulNmx !mxE oppr_ge0.
  move => h1 h2.
  have := lt_le_trans h1 h2.
  by rewrite ltxx.
have L0 : Left (sol t) = 0.
  apply/eqP; rewrite -enorm_eq0; apply /eqP.
  have := congr1 (fun v : 'rV[K]_2 => v ord0 ord0) h.
  by rewrite !mxE/=.
have R0 : (Right (sol t)) *m \S('e_2) = 0.
  apply/eqP; rewrite -enorm_eq0; apply/eqP.
  have := congr1 (fun v : 'rV[K]_2 => v ord0 ord_max) h.
  by rewrite !mxE/=.
rewrite -(hsubmxK (n1:=3) (sol t)).
rewrite L0.
suff [-> | -> ] : Right (sol t) = 0 \/ Right (sol t) = (2 *: 'e_2).
  left;apply /matrixP => i j;rewrite mxE.
  case: splitP => // k _;by rewrite !mxE.
  right;apply /matrixP => i j;rewrite mxE.
  by case: splitP => // k _.
have := is_sol_state_space_tilt t0d sol0 solP.
rewrite /Tilt.Upsilon1/=.
have /sub_rVP [k ->] : (Right (sol t) <= ('e_2 : 'rV[K]_3))%MS.
  apply: (@submx_trans _ _ _ _ _ _ (kermx \S('e_2))).
    by apply /sub_kermxP.
  rewrite submxElt kernel_spin //.
  by apply /negP;rewrite -enorm_eq0 enormeE;apply /negP.
rewrite -{1}(scale1r 'e_2)/= -scalerBl enormZ enormeE mulr1.
rewrite -{2}normr1.
move /eqP => hk.
rewrite eqr_norm2 in hk.
case /orP : hk.
by rewrite subr_eq addrC -subr_eq subrr => /eqP <-;rewrite scale0r;left.
by rewrite subr_eq addrC -subr_eq opprK => /eqP <-;right.
Qed.

(* TODO: rework of this proof is needed *)
(* NB: unused *)
Lemma derive_along_Left_Right_le0 (sol : _ -> _ -> _) (x : 'rV[K]_6) :
  is_sol_on0o phi (BLeft Delta) (sol x) ->
  sol x 0 = Tilt.point1 ->
  \forall z \near 0^',
    ('D~(sol x) (fun x => `|Left x|_e ^+ 2 / (2 * alpha1)) +
     'D~(sol x) (fun x => `|Right x|_e ^+ 2 / (2 * gamma))) z <= 0.
Proof.
move=> dtraj traj0.
rewrite fctE !invfM /=.
near=> z.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
(* move: dtraj => [H0 Hderiv Htilt]. *)
(* have Hz_derivable : derivable (sol x) z 1. *)
(*   apply: Hderiv. *)
(*   admit. *)
(* rewrite derive_alongMl; last 2 first. *)
(*   exact/differentiable_norm_squared/differentiable_lsubmx. *)
(*   apply derivable1_diffP. *)
(*   apply: Hderiv. *)
(*   admit. *)
(* rewrite derive_alongMl; last 2 first. *)
(*   exact/differentiable_norm_squared/differentiable_rsubmx. *)
(*   exact/derivable1_diffP. *)
(* rewrite /= !derive_along_norm_squared; last 4 first. *)
(*   exact/differentiable_rsubmx. *)
(*   exact/derivable1_diffP. *)
(*   exact/differentiable_lsubmx. *)
(*   exact/derivable1_diffP. *)
(* rewrite -V1dotE //. *)
(* pose zp1 := Left \o sol x. *)
(* pose z2 := Right \o sol x. *)
(* set w := (z2 z) *m \S('e_2). *)
(* pose u1 : 'rV[K]_2 := *)
(*   \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i. *)
(* apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)). *)
(*   exact: V1dot_ub. *)
(* have [->|H] := eqVneq u1 0. *)
(*   by rewrite mulNmx mul0mx mulNmx mul0mx mxE mxE oppr0. *)
(* by rewrite leNgt 2!mulNmx mxE oppr_gt0 -leNgt ltW// u2_quadratic_form_gt0. *)
Unshelve. all: try by end_near. Abort.

(* NB: should be completed to prove asymptotic stability *)
Lemma locnegsemidef_derive_alone_V1 sol (x : 'rV[K]_6) :
  is_sol_on0o phi (BLeft Delta) (sol x) ->
  sol x 0 = Tilt.point1 ->
  locnegsemidef ('D~(sol x) (V1 alpha1 gamma)) 0.
Proof.
(* move=> [y033] dy dtraj traj0. *)
(* rewrite /locnegsemidef /V1. *)
(* rewrite derive_alongD /=; last 3 first. *)
(*   apply: differentiableM => /=; last exact: differentiable_cst. *)
(*   exact/differentiable_norm_squared/differentiable_lsubmx. *)
(*   apply: differentiableM; last exact: differentiable_cst. *)
(*   exact/differentiable_norm_squared/differentiable_rsubmx. *)
(*   apply/derivable1_diffP. *)
(*   admit. *)
(* split; last first. *)
(*   near=> z. *)
(*   rewrite derive_along_derive //; last first. *)
(*     apply/derivable1_diffP. *)
(*     admit. *)
(*   admit. (* TODO: lynda *) *)
(*   admit. (* TODO: lynda *) *)
(* under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC. *)
(* under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC. *)
(* rewrite derive_alongMl; last 2 first. *)
(*   exact/differentiable_norm_squared/differentiable_lsubmx. *)
(*   apply/derivable1_diffP. *)
(*   admit. *)
(* rewrite /= !derivative_derive_along_eq0. *)
(* - by rewrite scaler0 add0r. *)
(* TODO: urgent - apply/differentiable_norm_squared/differentiable_rsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /tilt_point1.
  rewrite /eqn14b_rhs.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
<<<<<<< HEAD
    exact/differentiable_enorm_squared/differentiable_lsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
=======
    exact/differentiable_norm_squared/differentiable_lsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /tilt_point1.
>>>>>>> d87c05f (complete uniqueness, two small admits in tilt, cleaning)
  rewrite /eqn14b_rhs.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.*)
Abort.

Lemma locnegdef_derive_along_V1 (sol : 'rV_6 -> K -> 'rV_6) (x : 'rV[K]_6)
   (zp1 := Left \o sol x) (z2 := Right \o sol x) :
  is_sol_on0o phi (BLeft Delta) (sol x) ->
  sol x 0 \in Tilt.Upsilon1 ->
  (forall t : K, Tilt.Upsilon1 (sol x t)) ->
  sol x 0 = Tilt.point1 ->
  locnegdef ('D~(sol x) (V1 alpha1 gamma)) 0.
Proof.
move=> solves sol0 state y0.
split.
  rewrite /is_sol_on0o in solves.
  rewrite /= derivative_derive_along_eq0 => //; last first.
    admit.
  rewrite /V1.
  apply: differentiableD => //; last first.
    apply: differentiableM; last exact: differentiable_cst.
    exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  apply: differentiableM => //.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
near=> z0.
rewrite derive_along_V1.
- have z00Delta : z0 \in `[0, Delta[%R.
    admit.
  have V1dot_le := V1dot_ub sol0 solves z00Delta => //.
  set w := z2 z0 *m \S('e_2).
  set u1 : 'rV[K]_2 := \row_(i < 2)
    [eta (fun=> 0) with 0 |-> `|zp1 z0|_e, 1 |-> `|w|_e] i.
  have Hpos : 0 < (u1 *m u2 *m u1^T) 0 0.
    rewrite u2_quadratic_form_gt0//.
    rewrite /u1.
    admit.
  have Hneg : -  (u1 *m u2 *m u1^T) 0 0 < 0 by rewrite oppr_lt0.
  rewrite lt_neqAle.
  apply/andP; split; last first.
    apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
      by [].
    have -> : (- u1 *m u2 *m u1^T) 0 0 = - (u1 *m u2 *m u1^T) 0 0.
      rewrite !mxE -sumrN.
      under [in RHS]eq_bigr do rewrite -mulNr.
      by under [in LHS]eq_bigr do rewrite mulNmx mxE.
  by apply/ltW => //.
  rewrite /V1dot.
  rewrite mxE/=.
  apply/eqP => Habs.
  admit.
- admit.
- by [].
- move => t t0Delta.
  apply/derivable1_diffP => //.
  move : solves; rewrite /is_sol_on0o.
  move=> deri.
  apply deri.
  move: t0Delta; rewrite inE/=.
  by apply: subset_itvr; rewrite bnd_simp.
Unshelve. all: by end_near. Abort.

(*Definition is_Lyapunov_stable_at {K : realType} {n}
  (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
  (A : set 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> K)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0 A,
      is_Lyapunov_candidate V setT x0 &
      forall traj1 traj2 : (K -> 'rV[K]_n.+1),
        is_sol f traj1 A ->
        traj1 0 = x0 ->
        locnegsemidef (derive_along V (fun a => traj1) 0 ) 0].*)

(*Lemma V1_is_Lyapunov_stable :
  is_Lyapunov_stable_at (tilt_eqn alpha1 gamma) state_space_tilt (V1 alpha1 gamma) tilt_point1.
Proof.
split.
- exact: equilibrium_tilt_point1.
- exact: V1_is_Lyapunov_candidate.
(*- by move=> traj1 ? ?; exact: V1_point_is_lnsd.
Qed.*) Abort.*)

Lemma derive_along_V1_le0 (sol : K -> 'rV[K]_6) :
  is_sol_on0o phi (BLeft Delta) sol ->
  sol 0 \in Tilt.Upsilon1 ->
  (forall t, 0 < t < Delta -> differentiable sol t) ->
  forall t : K, 0 < t < Delta ->
  'D~(sol) (V1 alpha1 gamma) t <= 0.
Proof.
move=> solves sol0 diff t t0.
rewrite derive_along_V1//; last 2 first.
  by rewrite inE/= in_itv/=.
  move=> t1 t10Delta.
  apply: diff => //.
  by rewrite inE/= in_itv/= in t10Delta.
have t0Delta : t \in `[0, Delta[%R.
  rewrite in_itv/=.
  by move/andP : t0 => [] /ltW -> ->.
have Hub := V1dot_ub sol0 solves t0Delta.
apply: (le_trans Hub).
have Hquad : let u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o sol) t|_e,
                        1 |-> `|(Right \o sol) t *m \S('e_2)|_e]
                         i in 0 <= (u1 *m u2 *m u1^T) 0 0.
  set u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o sol) t|_e,
                        1 |-> `|(Right \o sol) t *m \S('e_2)|_e]
            i.
  rewrite /=.
  case: (u1 =P 0) => [->|/eqP u1_neq0].
    by rewrite !mul0mx mxE.
  by rewrite ltW// u2_quadratic_form_gt0.
by rewrite -oppr_ge0 !mulNmx mxE opprK Hquad.
Qed.

End tilt_eqn_Lyapunov.

Section tilt_eqn_Lyapunov_global.
Local Open Scope classical_set_scope.
Context {K : realType}.
Variables alpha1 gamma : K.
Hypotheses (alpha1_gt0 : 0 < alpha1) (gamma_gt0 : 0 < gamma).
Let phi := Tilt.eqn alpha1 gamma.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

(* todo: copy paste *)
Lemma derive_zp10 (sol : K -> 'rV_6) :
  is_sol_on0y phi sol ->
  'D_1 (Left \o sol) 0 = - alpha1 *: Left (sol 0).
Proof.
move/is_sol_on0yP.
move/(_ _ (lexx 0)) => [d0 +].
move=> /(congr1 Left).
rewrite derive1E.
rewrite row_mxKl.
move=> <-.
by rewrite derive_lsubmx.
Qed.

Lemma derive_z20 (sol : K -> 'rV_6) :
  is_sol_on0y phi sol ->
  'D_1 (Right \o sol) 0 =
  gamma *: (Right (sol 0) - Left (sol 0)) *m \S('e_2 - Right (sol 0)) ^+ 2.
Proof.
move/is_sol_on0yP.
move /(_ _ (lexx 0)) => [d0 +].
move => /(congr1 Right).
rewrite derive1E.
by rewrite row_mxKr => ?; rewrite derive_rsubmx.
Qed.

Lemma V1dotE0 (sol : K -> 'rV_6) (zp1 := Left \o sol) (z2 := Right \o sol) :
  is_sol_on0y phi sol ->
  V1dot (sol 0) =
    c1 *: (2 *: 'D_1 zp1 0 *m (Left (sol 0))^T) 0 0 +
    c2 *: (2 *: 'D_1 z2 0 *m (Right (sol 0))^T) 0 0.
Proof.
move => h.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC.
rewrite mulVf// div1r.
rewrite derive_zp10 // -scalemxAl mxE [X in X + _](mulrA (alpha1^-1) (- alpha1)).
rewrite mulrN mulVf ?gt_eqF// mulN1r.
rewrite derive_z20 // -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE.
rewrite scalerA mulVf ?gt_eqF// scale1r.
rewrite enorm_squared /V1dot.
congr +%R.
rewrite -2![in LHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
rewrite -[X in (X *m (_ *m _)) 0 0 = _]trmxK.
rewrite -[X in (_ *m (X *m _)) 0 0 = _]trmxK.
rewrite mulmxA -trmx_mul -trmx_mul [LHS]mxE.
rewrite -(mulmxA (Right (sol 0) - (Left (sol 0)))) mulmxE -expr2.
rewrite tr_sqr_spin.
by rewrite mulmxA.
Qed.

Lemma derive_along_V1_global t (sol : K -> 'rV_6) :
  0 <= t ->
  is_sol_on0y phi sol ->
  'D~(sol) (V1 alpha1 gamma) t = V1dot (sol t).
Proof.
move=> t0 tilt_eqnx.
have dif1 : forall (t : K), 0 <= t -> differentiable sol t.
   move => /= t' t'0.
   apply/derivable1_diffP.
   move/is_sol_on0yP in tilt_eqnx.
   by apply tilt_eqnx.
rewrite /V1 derive_alongD; last 3 first.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl => //; last first.
  exact: dif1.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
rewrite derive_alongMl => //; last first.
  exact: dif1.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  rewrite -fctE /= !derive_along_enorm_squared//=.
  move : t0.
  rewrite le_eqVlt => /predU1P[<-//|t0].
  rewrite V1dotE0 => //.
  by rewrite !invfM.
 -  rewrite (V1dotE alpha1_gt0 gamma_gt0 (@global_sol_sol _ _ _ _ tilt_eqnx (BLeft (t + 1)))) //.
    by rewrite !invfM.
    by rewrite inE/= in_itv/= (ltW t0) ltrDl;apply /andP.
- exact/differentiable_lsubmx_comp.
exact:dif1.
exact:dif1.
Qed.

Lemma derive_along_V1_le0_global (sol : K -> 'rV[K]_6) :
  is_sol_on0y phi sol ->
  sol 0 \in Tilt.Upsilon1 ->
  forall t : K, 0 <= t  ->
  'D~(sol) (V1 alpha1 gamma) t <= 0.
Proof.
move=> solves sol0.
have diff : forall (t : K), 0 <= t -> differentiable sol t.
   move => /= t' t0'.
   apply/derivable1_diffP.
   move/is_sol_on0yP in solves.
   by apply solves.
move => t t0.
rewrite derive_along_V1_global//.
have t0Delta : t \in `[0, t+1[%R.
  by rewrite in_itv/=t0 ltrDl ltr01.
have Hub := V1dot_ub sol0 (@global_sol_sol _ _ _ _ solves (BLeft (t + 1))) t0Delta.
apply: (le_trans Hub).
have Hquad : let u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o sol) t|_e,
                        1 |-> `|(Right \o sol) t *m \S('e_2)|_e]
                         i in 0 <= (u1 *m u2 *m u1^T) 0 0.
  set u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o sol) t|_e,
                        1 |-> `|(Right \o sol) t *m \S('e_2)|_e]
            i.
  rewrite /=.
  case: (u1 =P 0) => [->|/eqP u1_neq0].
    by rewrite !mul0mx mxE.
  by rewrite ltW// u2_quadratic_form_gt0.
by rewrite -oppr_ge0 !mulNmx mxE opprK Hquad.
Qed.

End tilt_eqn_Lyapunov_global.

Section equilibrium_zero_stable.
Context {K : realType}.
Variables gamma alpha1 : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Let phi := Tilt.eqn alpha1 gamma.
Variable Init : set 'rV[K]_6.

(* Hypothesis y_sol : is_sol Delta (sol 0). *)
(* Hypothesis y00 : sol 0 0 = 0. *)

Lemma V1_diff : forall t : 'rV_6, differentiable (V1 alpha1 gamma) t.
Proof.
move=> t; apply/differentiableD => //=.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
apply/differentiableM => //=.
exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
Qed.

Lemma equilibrium_zero_stable :
  0 \in Init -> open Init -> Init `<=` Tilt.Upsilon1 ->
  is_locally_stable_at phi Init Tilt.point1.
Proof.
move=> Init0 openInit Init_in_state.
apply: (@Lyapunov_stability K _ phi Init openInit (V1 alpha1 gamma)).
- exact: V1_diff.
- move=> Delta sol sol0 solP t t0.
  apply: (@derive_along_V1_le0 _ _ _ _ _ Delta sol).
  + assumption.
  + assumption.
  + assumption.
  + by apply/mem_set/Init_in_state/set_mem.
  + move=> /= t1 t10Delta.
    rewrite -derivable1_diffP.
    apply solP.
    rewrite in_itv/=.
    by case/andP : t10Delta => /ltW -> ->.
  + case/andP : t0 => t0 tDelta.
    rewrite tDelta andbT.
    assumption.
- have := V1_is_Lyapunov_candidate alpha1_gt0 gamma_gt0.
  rewrite /is_Lyapunov_candidate /Tilt.point1 => Hpos.
  rewrite /V1 lsubmx_const rsubmx_const; split => //.
  split.
    by rewrite !expr2 !enorm0 !mulr0 !mul0r add0r.
  move=> z zin z_neq0.
  case : Hpos => // _ [V1_eq0 V1_gt0].
  apply: V1_gt0 => //.
  by rewrite inE.
- split => // Delta.
  have [_] := equilibrium_tilt_point1 alpha1 gamma.
  exact.
Qed.

End equilibrium_zero_stable.
