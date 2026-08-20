From HB Require Import structures.
From mathcomp Require Import boot order algebra ring_tactic interval_inference.
From mathcomp Require Import boolp classical_sets functions reals order
 topology normedtype landau sequences derive realfun matrix_normedtype.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.
Require Import ode tilt_stability.

(**md**************************************************************************)
(* # Formalization of [benallegue2023itac] (1/2)                              *)
(*                                                                            *)
(* This file starts with a formal description of the physical model.          *)
(* The final result of this file is the proof that the equilibrium point 0 is *)
(* stable.                                                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*                    S2 == unit sphere centered at 0                         *)
(*  Module PhysicalModel == This module contains a formalization of the       *)
(*                          transformation of a system of measurements to     *)
(*                          a differential equation that captures the error   *)
(*                          dynamics.                                         *)
(*       Tilt.point{1.2} == equilibrium points                                *)
(*         Tilt.Upsilon1 == state space                                       *)
(*              Tilt.eqn == equation (14) in [benallegue2023itac]             *)
(*               Tilt.V1 == Lyapunov function                                 *)
(*                    u2 == 2 x 2 matrix to prove the Lyapunov function       *)
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

Definition S2 {R : realType} := [set x : 'rV[R]_3 | `|x|_e = 1].

Module PhysicalModel.
Section physicalmodel.
Context {R : realType} (g0 : R) (* standard gravitational constant *).
Hypotheses g0_neq0 : g0 != 0.

Variable M : R -> 'M[R]_3. (* orientation of frame L w.r.t. frame W *)
Hypothesis MisSO : forall t, M t \is 'SO[R]_3.

Let w t := ang_vel M t. (* angular velocity *)

(* tilt, eqn (8) *)
Definition x2 t : 'rV[R]_3 := 'e_2 *m M t.

Lemma x2_S2 t : x2 t \in S2.
Proof. by rewrite /S2 /x2 inE/= orth_preserves_norm ?enormeE ?rotation_sub. Qed.

(* what the accelerometer measures according to [benallegue2023itac] *)
Definition y_a x t := - x t *m \S(w t) + 'D_1 x t + g0 *: x2 t.

(* proof that y_a is indeed the sum of linear and gravitational acceleration *)
Section y_aE.
Variable p : R -> 'rV[R]_3.
Let v := fun t : R => 'D_1 p t *m M t.

Lemma y_aE t : (forall t, derivable M t 1) ->
    (forall t, derivable p t 1) -> (forall t, derivable ('D_1 p) t 1) ->
  ('D_1 ('D_1 p) t + g0 *: 'e_2) *m M t = y_a v t.
Proof.
move=> derivableR derivablep derivableDp.
rewrite mulmxDl.
rewrite /y_a/= /= /x2.
congr +%R; last by rewrite scalemxAl.
rewrite -ang_vel_mxE/=.
  by move=> ?; rewrite rotation_sub.
  exact: derivableR.
rewrite [in RHS]derive_mulmx => //.
rewrite derive1mx_ang_vel//; first by move=> ?; rewrite rotation_sub.
rewrite ang_vel_mxE//; first by move=> ?; rewrite rotation_sub.
rewrite addrCA.
rewrite -mulmxE.
rewrite -mulNmx.
rewrite [X in _ = _ X]addrC.
rewrite !mulNmx.
by rewrite -mulmxA /= addrN addr0.
Qed.

End y_aE.

Hypothesis derivableR : forall t, derivable M t 1.
Variable v : R -> 'rV[R]_3. (* linear velocity *)
Let x1 t := v t.

(* section III.A of [benallegue2023itac] *)
Section state_dynamics.

(* NB: not used *)
Lemma derive_ang_vel t (u : R -> 'rV[R]_3) (T : R -> 'M[R]_3) :
  (forall t, derivable u t 1) -> (forall t, derivable T t 1) ->
  (forall t, t \is 'SO[R]_3) ->
  'D_1 (fun t => u t *m T t) t = u t *m T t *m \S(ang_vel T t) + 'D_1 u t *m T t.
Proof.
move=> deru dert TisSO.
rewrite derive_mulmx => //.
rewrite addrC; congr +%R.
rewrite -ang_vel_mxE.
  by move => t0; rewrite rotation_sub.
  exact: dert.
rewrite -mulmxA.
rewrite mulmxE.
by rewrite -derive1mx_ang_vel// => ?; rewrite rotation_sub.
Qed.

(* eqn (10/11) *)
(* NB: we write x_i * S(w) whereas it is - S(w) * x_i in [benallegue2023itac],
   row convention *)
Lemma derive_x1 t : 'D_1 x1 t = x1 t *m \S(w t) + y_a x1 t - g0 *: x2 t.
Proof.
rewrite /y_a/= -addrA addrK.
rewrite /x1.
rewrite addrCA addrA mulNmx /= /w.
by rewrite (addrC(-_)) subrr add0r.
Qed.

 (* eqn (11b) *)
Lemma derive_x2 t : 'D_1 x2 t = x2 t *m \S( w t ).
Proof.
rewrite /w -ang_vel_mxE//; first by move=> ?; rewrite rotation_sub.
have -> : 'D_1 (fun t0 => 'e_2 *m (M t0)) t = 'e_2 *m 'D_1 M t.
  move=> n /=.
  rewrite derive_mulmx//=.
  by rewrite derive_cst mul0mx add0r.
rewrite derive1mx_ang_vel /=; first by move=> ?; rewrite rotation_sub.
by rewrite mulmxA.
Qed.

End state_dynamics.

Hypothesis v_derivable : forall t, derivable v t 1.

(* section III.A in [benallegue2023itac] *)
Section two_steps_first_order_estimator.
Local Notation y_a := (y_a v).
Variables gamma alpha1 : R.

Variable x1_hat : R -> 'rV[R]_3. (* estimator *)
Hypothesis derivable_x1_hat : forall t, derivable x1_hat t 1.

Variable x2_hat : R -> 'rV[R]_3. (* estimator *)
Hypothesis x2_hat_S2 : x2_hat 0 \in S2.
Hypothesis x2_hat_derivable : forall t, derivable x2_hat t 1.
Hypothesis norm_x2_hat : forall t, `|x2_hat t|_e = 1.

Let x2'_hat t := - (alpha1 / g0) *: (x1 t - x1_hat t). (* eqn (12b) *)

Hypothesis eqn12a : forall t,
  'D_1 x1_hat t = x1_hat t *m \S(w t) + y_a t - g0 *: x2'_hat t. (* eqn (12a) *)

Hypothesis eqn12c : forall t,
  'D_1 x2_hat t = x2_hat t *m \S(w t + gamma *: x2'_hat t *m \S(x2_hat t)).
  (* eqn (12c) *)

(* estimation error *)
Let error1 t := x2 t - x2'_hat t. (* p_1 in [benallegue2023ieeetac] *)
Let error2 t := x2 t - x2_hat t. (* \tilde{x_2} in [benallegue2023ieeetac] *)
(* projection from the local frame to the world frame(?) *)
Let error1_p t := error1 t *m (M t)^T (* z_p_1 in [benallegue2023ieeetac] *).
Let error2_p t := error2 t *m (M t)^T.

Let error2E t : error2 t = error2_p t *m M t.
Proof.
by rewrite /error2 -mulmxA orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

Let derivable_x2 t : derivable x2 t 1. Proof. exact: derivable_mulmx. Qed.

Let derivable_x2'_hat t : derivable x2'_hat t 1.
Proof. by apply: derivableZ => /=; exact: derivableB. Qed.

Let derivable_error1 t : derivable error1 t 1. Proof. exact: derivableB. Qed.

Let derivable_error2 t : derivable error2 t 1. Proof. exact: derivableB. Qed.

(* eqn (13a) *)
Lemma derive_error1 t :
  'D_1 error1 t = error1 t *m \S(w t) - alpha1 *: error1 t.
Proof.
simpl in *.
rewrite deriveB//=.
rewrite deriveZ/=; first exact: derivableB.
rewrite scaleNr opprK.
rewrite deriveB//=.
rewrite !derive_x2 // -/(x2 t) /=.
rewrite derive_x1//.
rewrite eqn12a.
transitivity ((x2 t + (alpha1 / g0) *: (x1 t - x1_hat t)) *m \S(w t)
              - alpha1 *: error1 t).
  transitivity (x2 t *m \S(w t) + (alpha1 / g0) *: (x1 t *m \S(w t) -
                                                   g0 *: x2 t -
                                                   (x1_hat t *m \S(w t) -
                                                   g0 *: x2'_hat t))).
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
               g0 *: (x2 t - x2'_hat t)).
    rewrite mulmxBl scalerDr scalerN opprB addrA [LHS]addrC 2!addrA.
    rewrite -addrA; congr +%R.
      by rewrite addrC.
    by rewrite opprB addrC.
  rewrite -/(error1 t).
  rewrite scalerDr addrA scalemxAl -mulmxDl scalerN scalerA.
  by rewrite divfK.
by rewrite {2}/error1 /x2'_hat scaleNr opprK.
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
rewrite [X in _ = X + _](_ : _ = 0) ?add0r.
  rewrite mulmxA.
  rewrite -(mulmxA(x2_hat t)) sqr_spin //.
  rewrite mulmxDr !mulmxA.
  rewrite dotmul1 // mul1mx.
  by rewrite mulmxN mulmx1 subrr.
rewrite expr2 -mulmxE fact215 -mulmxE -spin_crossmul.
rewrite [in RHS]mulmxA [in RHS]spinE spinE spinE.
by rewrite [LHS](@lieC _ (vec3 R)).
Qed.

Lemma x2_hatR t : x2_hat t *m (M t)^T = 'e_2 - error2_p t.
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
rewrite derive_mulmx/=.
  by [].
  by rewrite derivable_trmx.
rewrite derive_error1.
rewrite mulmxBl addrAC.
apply/eqP.
rewrite subr_eq.
rewrite [in eqbRHS]addrC scaleNr scalemxAl subrr /=.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel //; first by move => t0; rewrite rotation_sub.
rewrite ang_vel_mxE //; first by move => t1 ; rewrite rotation_sub.
rewrite -/(w t) -mulmxA -mulmxDr trmx_mul tr_spin.
by rewrite mulNmx subrr mulmx0.
Qed.

Definition eqn14b_rhs x1 x2 := gamma *: (x2 - x1) *m \S('e_2 - x2) ^+ 2.

(* eqn (14b) *)
Lemma derive_error2_p t : 'D_1 error2_p t = eqn14b_rhs (error1_p t) (error2_p t).
Proof.
rewrite /eqn14b_rhs.
rewrite [LHS]derive_mulmx/=.
  by [].
  by rewrite derivable_trmx.
simpl in *.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel//=; first by move=> ?; rewrite rotation_sub.
rewrite !ang_vel_mxE//; first by move=> ?; rewrite rotation_sub.
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

End physicalmodel.
End PhysicalModel.

Module Tilt.
Section tilt.
Context {R : realType}.
Variables alpha1 gamma : R.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

Definition eqn_functional (f : R -> 'rV[R]_6) : R -> 'rV[R]_6 :=
  let error1_p_dot := Left \o f in
  let error2_p_dot := Right \o f in
  fun t => row_mx
    (- alpha1 *: error1_p_dot t)
    (PhysicalModel.eqn14b_rhs gamma (error1_p_dot t) (error2_p_dot t)).

Definition eqn (dot_z1_z2 : 'rV[R]_6) : 'rV[R]_6 :=
  let dot_z1 := Left dot_z1_z2 in
  let dot_z2 := Right dot_z1_z2 in
  row_mx (- alpha1 *: dot_z1)
         (PhysicalModel.eqn14b_rhs gamma dot_z1 dot_z2).

Lemma eqnE (f : R -> 'rV[R]_6) t : eqn (f t) = eqn_functional f t.
Proof. by []. Qed.

Definition Upsilon1 := [set x : 'rV[R]_6 | `| 'e_2 - Right x |_e = 1].

Lemma Upsilon1_preimage :
  Upsilon1 = (fun x => `| 'e_2 - Right x |_e ) @^-1` [set (1 : R)].
Proof. by []. Qed.

Definition point1 : 'rV[R]_6 := 0.
Definition point2 : 'rV[R]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2).

Lemma point1_neq2 : point1 != point2.
Proof.
apply/eqP; rewrite /point1 /point2 => /eqP.
rewrite eq_sym (@row_mx_eq0 _ 1 3 3) eqxx/= => /eqP/rowP/(_ ord_max).
by rewrite !mxE eqxx/= mulr1; apply/eqP; rewrite pnatr_eq0.
Qed.

Definition points := [set point1; point2].

Definition V1 (z1_z2 : 'rV[R]_6) : R :=
  let z1 := Left z1_z2 in
  let z2 := Right z1_z2 in
  `|z1|_e ^+ 2 / (2 * alpha1) + `|z2|_e ^+ 2 / (2 * gamma).

End tilt.
End Tilt.

(* properties of Tilt.eqn *)
Section tilt_eqn.
Context {R : realType}.
Variables alpha1 gamma : R.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Let phi := Tilt.eqn alpha1 gamma.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

Lemma tilt_eqn_locally_lipschitz_new x (r : R) :
 exists k : {posnum R}, k%:num.-lipschitz_(closed_ball x r) phi.
Proof.
have [r0|r0] := ltP 0 r; last first.
  rewrite closed_ball0//.
  by exists 1%:pos => /= -[u v] [].
near (pinfty_nbhs R) => k.
have k0 : 0 < k by [].
exists (PosNum k0) => /= => -[/= x0 x1] [x0B x1B].
rewrite (opp_row_mx (n1:=3)) (add_row_mx (n1:=3)).
rewrite !scaleNr opprK/=.
rewrite addrC -scalerBr.
rewrite /PhysicalModel.eqn14b_rhs.
rewrite -!scalemxAl -scalerBr.
rewrite (norm_rowmx (m:=0) (n1:=2) (n2:=2)).
rewrite ge_max; apply/andP; split.
- rewrite mx_normZ.
  rewrite -linearB/=.
  rewrite ler_pM//.
  rewrite distrC.
  exact/le_trans/(@lsubmx_norm_le _ 2).
- rewrite mx_normZ.
  set a := Right x0 - Left x0.
  set b := Right x1 - Left x1.
  set c := \S('e_2 - Right x0) ^+ 2.
  set d := \S('e_2 - Right x1) ^+ 2.
  have abound : `|a| <= 2 * (`|x| + r).
    rewrite (le_trans (ler_normB _ _ ))// mulrDl lerD// mul1r.
      rewrite (le_trans (rsubmx_norm_le _))//.
      by apply: closed_ball_bounded => //.
    rewrite (le_trans (lsubmx_norm_le _))//.
    exact: closed_ball_bounded.
  (* todo: find some bound and show *)
  have sbound x' : closed_ball x r x' ->  `|'e_2 - Right x'| <= (1 + r)+`|x|.
    move=> cb.
    rewrite (le_trans (ler_normB _ _))//.
    rewrite -addrA lerD//.
      exact: mx_norm_delta_mx.
    by rewrite (le_trans (rsubmx_norm_le _))// addrC closed_ball_bounded//.
  have dbound : `|d| <=  3 * ((1 + r) + `|x|) ^+ 2.
    rewrite /d.
    apply: (le_trans (spin_sq_norm_bound _)).
    apply ler_pM => //.
    suff h :  `|'e_2 - Right x1| <= (1 + r) + `|x|.
       by apply ler_pM => //; apply normr_ge0.
    by apply sbound.
  rewrite -ler_pdivlMl; first by rewrite normr_gt0 lt0r_neq0.
  rewrite -(subrKA (a *m d) (a *m c )) (le_trans (ler_normD _ _))//.
  rewrite -[X in `|X| + _]mulmxBr.
  rewrite -[X in _ + `|X|]mulmxBl.
  rewrite (splitr  `|gamma|^-1) mulrDl.
  rewrite -invrM ?unitfE//.
    by rewrite gt_eqF// gtr0_norm.
  rewrite lerD//.
  + apply: (le_trans (mx_norm_mul _ _)).
    have h0 := spin_sq_dist_bound ('e_2 - Right x0) ('e_2 - Right x1).
    apply : (le_trans (ler_pM _ _ (le_refl _) h0)) => //.
    have -> : 'e_2 - Right x0 - ('e_2 - Right x1) = Right x1 - Right x0.
      by rewrite opprB addrC addrA subrK.
    rewrite !mulrA.
    apply ler_pM => //; last by rewrite distrC -linearB; exact: rsubmx_norm_le.
    rewrite (mulrC 3) -!mulrA.
    apply: (le_trans (ler_pM _ _ abound (lexx _))) => //.
    rewrite !mulrA.
    rewrite ler_pdivlMl.
       by rewrite mulr_gt0// gtr0_norm.
    rewrite !mulrA.
    suff h : `|'e_2 - Right x0| + `|'e_2 - Right x1| <= 2 * ((1 + r) + `|x|).
      apply: (le_trans (ler_pM _ _ (le_refl _) h)) => //.
      by rewrite !mulr_ge0// addr_ge0// ltW.
    by rewrite mulrDl mul1r lerD//; apply sbound.
  + rewrite (le_trans (mx_norm_mul _ _))//.
    rewrite opprB -addrA (addrC (-Left x0)) addrA (addrC (Left x1)) addrA -(addrA (Right x0 - _)).
    rewrite mulrC.
    apply (@le_trans _ _ (`| d| *  (6 * `|x0 - x1|))).
    apply ler_pM => //.
    rewrite [in leRHS](natrM _ 3 2)// -mulrA ler_pM//.
    rewrite (le_trans (ler_normD _ _))//.
    rewrite mulrDl lerD// mul1r.
      by rewrite -linearB; exact: rsubmx_norm_le.
    by rewrite distrC -linearB/=; exact: lsubmx_norm_le.
    rewrite (le_trans (ler_pM  _ _ dbound (lexx _ )))//.
    rewrite ler_pdivlMl; first by rewrite mulr_gt0// gtr0_norm.
    by rewrite !mulrA ler_pM// !mulr_ge0// ?addr_ge0// ltW.
Unshelve. all: by end_near. Qed.

Lemma tilt_eqn_locally_lipschitz : locally_lipschitz phi.
Proof.
move=> /= x.
exists 1%:pos.
exact: tilt_eqn_locally_lipschitz_new.
Qed.

Lemma tilt_state_spaceS : state_space phi Tilt.Upsilon1 `<=` Tilt.Upsilon1.
Proof.
move => p [y [D /= [y0_init1 [_ [deri cont]]]]].
have [D0|D0] := leP 0 D; last first.
  move=> -[t + x].
  rewrite in_itv/= => -/andP[x0 xD].
  have := lt_trans xD D0.
  by rewrite ltNge x0.
rewrite /Tilt.Upsilon1.
have : {in `]0, D[%R,
    (fun t => ('e_2 - Right (y t)) *d (('e_2 - Right (y t))))^`() =1 0}.
  move => x xd /=.
  transitivity ((fun t => -2 * (Right (y^`()%classic t) *d
                                ('e_2 - Right (y t)))) x).
    rewrite !derive1E.
    have ? : derivable y x 1.
      apply deri.
      by apply: subset_itvr xd; rewrite bnd_simp.
    rewrite derive_mx//.
    rewrite /dotmul.
    under eq_fun do rewrite dotmulP /=.
    rewrite dotmulP.
    rewrite !mxE /= mulr1n.
    under eq_fun do rewrite !mxE /= mulr1n.
    rewrite !derive_dotmul/=.
      apply: derivableB => /=.
        by [].
      by apply: derivable_rsubmx => /=.
    apply: derivableB => /=.
      by [].
    by apply: derivable_rsubmx => /=.
    rewrite /dotmul /=.
    rewrite [in RHS]mulr2n [RHS]mulNr [in RHS]mulrDl.
    rewrite !mul1r !dotmulP /= dotmulC [in RHS]dotmulC !linearD /=.
    rewrite !mxE /= !mulr1n.
    have -> : 'D_1 (fun x0 => 'e_2 - Right (y x0)) x = - Right ('D_1 y x).
      rewrite deriveB /=.
        exact: derivable_cst.
        exact: derivable_rsubmx.
      rewrite derive_cst /= sub0r; congr (- _).
      exact: derive_rsubmx.
    rewrite -(_ : 'D_1 y x =
        \matrix_(i, j) 'D_1 (fun t0 => y t0 i j) x).
      by apply/matrixP => a b; rewrite !mxE derive_mx//= ?mxE.
    ring.
  have Rsu t0 : t0 \in `]0, D[%R -> Right (y^`()%classic t0) =
      (gamma *: (Right (y t0) - Left (y t0)) *m \S('e_2 - Right (y t0)) ^+ 2).
    rewrite inE/=.
    by move/deri => [_ ->]; rewrite row_mxKr.
  rewrite /dotmul.
  transitivity (-2 * (gamma *: (Right (y x) -
                          Left (y x)) *m \S('e_2 - Right (y x)) ^+ 2 *m
                                          ('e_2 - Right (y x))^T) 0 0).
    by rewrite Rsu.
  rewrite !mulmxA.
  apply/eqP.
  rewrite mulf_eq0 /= oppr_eq0 ?pnatr_eq0 /= -!mulmxA spin_mul_tr.
  by rewrite !mulmx0 mxE.
move => h [t t0d ->].
have norm_constant t0 : t0 \in `[0, D[%R ->
    `|'e_2 - Right (y t0)|_e ^+ 2 = `|'e_2 - Right (y 0)|_e ^+ 2.
  have : forall x0, x0 \in `]0, D[%R ->
      is_derive x0 (1 : R) (fun x => `|'e_2 - Right (y x)|_e ^+ 2) 0.
    move => x0 x0d.
    have ? : derivable y x0 1.
      apply deri.
      by apply: subset_itvr x0d; rewrite bnd_simp.
    apply: DeriveDef.
      apply/derivable_enorm_squared => /=.
      apply/derivableB => /=.
        by [].
      exact/derivable_rsubmx.
    rewrite -derive1E.
    have := h _ x0d.
    under eq_fun do rewrite dotmulvv /=.
    by apply.
  move=> /= hd0 t0d'.
  apply/esym.
  have {}t0d'' : t0 \in `[0, t0]%R by rewrite bound_itvE/= (itvP t0d').
  have {}hd0 x0 : x0 \in `]0, t0[%R ->
      is_derive x0 1 (fun x => `| 'e_2 - Right (y x) |_e ^+ 2) 0.
    move=> x00t0.
    apply: hd0.
    apply: subset_itvl x00t0; rewrite bnd_simp.
    by rewrite ltW// (itvP t0d').
  have {t0d'' hd0} := cc_is_derive_0_is_cst t0d'' _ hd0.
  apply => //; last by rewrite bound_itvE (itvP t0d').
  apply: (@within_continuous_comp _ _ _ `[0, t0] y (fun x => `|'e_2 - Right x|_e ^+ 2)) => //=.
    move=> z _.
    apply: differentiable_continuous => //.
    apply: differentiable_enorm_squared => /=.
    exact: differentiableB.
  rewrite /sol_is_deriv_co/= in deri.
  apply: continuous_subspaceW cont.
  rewrite closure_itvoo; last first.
    by apply: subset_itvl; rewrite bnd_simp (itvP t0d').
  rewrite lt_neqAle D0 andbT eq_sym; apply/eqP => {}D0.
  move: t0d.
  rewrite D0 in_itv/= => /andP[/le_lt_trans] => /[apply].
  by rewrite ltxx.
suff: `|'e_2 - Right (y t)|_e ^+ 2 = 1.
  move=> /(congr1 Num.sqrt).
  by rewrite sqrtr1 sqr_sqrtr// dotmulvv sqr_ge0.
rewrite norm_constant//.
move: y0_init1.
rewrite inE /Tilt.Upsilon1 /= => ->.
by rewrite expr2 mulr1.
Qed.

Lemma tilt_point1_in_state_space : @Tilt.point1 R \in Tilt.Upsilon1.
Proof.
rewrite inE /Tilt.Upsilon1 /Tilt.point1/=.
 by rewrite rsubmx_const /= subr0 enormeE.
Qed.

Lemma equilibrium_point1 : is_equilibrium_point phi Tilt.point1.
Proof.
split.
- move=> t t0;  exact: derivable_cst.
  rewrite derive1E derive_cst /Tilt.point1; apply/eqP.
  rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP; split.
    by rewrite scaler_eq0 oppr_eq0 gt_eqF//= lsubmx_const.
  apply/eqP/rowP; move => i; apply/eqP.
  rewrite /PhysicalModel.eqn14b_rhs.
  set N := (X in _ *: X *m _); have : N = 0.
    by rewrite /N /=; apply/rowP => j; rewrite !mxE subrr.
  by move=> N0; rewrite N0 scaler0 mul0mx.
Qed.

Lemma tilt_point2_in_state_space : @Tilt.point2 R \in Tilt.Upsilon1.
Proof.
rewrite inE /Tilt.Upsilon1 /Tilt.point2 /=.
rewrite row_mxKr.
rewrite -[X in X - _ ]scale1r.
rewrite -scalerBl enormZ enormeE mulr1 distrC.
rewrite [X in _ - X](_:1 = 1%:R) //.
by rewrite -natrB //= normr1.
Qed.

Lemma equilibrium_point2 : is_equilibrium_point phi Tilt.point2.
Proof.
move=> D D0.
split.
exact: derivable_cst.
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
rewrite /PhysicalModel.eqn14b_rhs.
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

Section u2.
Context {R : realType}.

Definition u2 : 'M[R]_(2, 2) := \matrix_(i < 2, j < 2) [eta (fun=> 0) with
  (0,0) |-> 1,
  (0,1) |-> -2^-1,
  (1,0) |-> -2^-1,
  (1,1) |-> 1] (i, j).

Lemma u2neq0 : u2 != 0.
Proof. by apply/matrix0Pn; exists 1, 1; rewrite mxE /= oner_neq0. Qed.

Lemma u2_sym : u2 \is sym 2 R.
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
    ('X - (1%:R / 2)%:P) * ('X - (3%:R / 2)%:P) :> {poly R}.
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
rewrite [ltRHS](_ : _ = v``_0 ^+ 2 - v``_1 * v``_0 + v``_1 ^+ 2).
  rewrite -!addrA; congr +%R.
  rewrite !addrA; congr +%R.
  rewrite (mulrC _ v``_0) -mulrA -mulrDr.
  rewrite mulrC -mulNr; congr *%R.
  rewrite mulrC -mulrDr -mulr2n.
  rewrite mulNr; congr (- _).
  rewrite -(mulr_natl v``_1).
  by rewrite mulrA mulVf// ?mul1r.
rewrite [ltRHS](_ : _ = (v``_0 - 2^-1 * v``_1) ^+ 2 + 3 / 4 * v``_1 ^+ 2).
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
Context {R : realType}.
Variables alpha1 gamma : R.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).
Local Notation V1 := (Tilt.V1 alpha1 gamma).

Lemma V1_diff (t : 'rV_6) : differentiable V1 t.
Proof.
apply/differentiableD => //=.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
apply/differentiableM => //=.
exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
Qed.

Lemma V1_is_Lyapunov_candidate :
  is_Lyapunov_candidate V1 [set: 'rV_6] Tilt.point1.
Proof.
rewrite /V1 /Tilt.point1; split; first by rewrite inE.
- by rewrite lsubmx_const rsubmx_const enorm0 expr0n/= !mul0r add0r.
- move=> /= z_near _ z0.
  have /orP[lz0|rz0] : (Left z_near != 0) || (Right z_near != 0).
    rewrite -negb_and.
    apply: contra z0 => /andP[/eqP l0 /eqP r0].
    rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
    apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?;
    by rewrite mxE.
  + set rsub := Right z_near.
    have : `|rsub|_e >= 0 by rewrite enorm_ge0.
    set lsub := Left z_near.
    move=> nor.
    have normlsub : `|lsub|_e > 0 by rewrite enorm_gt0.
    rewrite ltr_pwDl//.
      by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
    by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
  + rewrite ltr_pwDr//.
      by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0 ?enorm_gt0.
    by rewrite divr_ge0 ?exprn_ge0 ?enorm_ge0 ?mulr_ge0// ltW.
Unshelve. all: by end_near. Qed.

Definition V1dot (zp1_z2 : 'rV[R]_6) : R :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  - `|zp1|_e ^+ 2 + (z2 *m (\S('e_2 - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2 - z2))^+2 *m zp1^T)``_0.

End V1.

Section tilt_eqn_Lyapunov.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variables alpha1 gamma : R.
Hypotheses (alpha1_gt0 : 0 < alpha1) (gamma_gt0 : 0 < gamma).
Let phi := Tilt.eqn alpha1 gamma.
Implicit Types f : R -> 'rV[R]_6.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

Lemma derive_zp1 (D : R) t f :
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  t \in `]0, D[ -> 'D_1 (Left \o f) t = - alpha1 *: Left (f t).
Proof.
move=> /= deri /[!inE]/= t0D.
case: deri => _ [deri cont].
have [derivable_f] := deri _ t0D.
move=> /(congr1 Left).
rewrite derive1E row_mxKl => <-.
by rewrite derive_lsubmx.
Qed.

Lemma derive_z2 (D : R) z f :
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  z \in `]0, D[ -> 'D_1 (Right \o f) z =
  gamma *: (Right (f z) - Left (f z)) *m \S('e_2 - Right (f z)) ^+ 2.
Proof.
move=> [_ [deriv cont]] /[!inE]/= z0D.
have [derivable_f +] := deriv _ z0D.
move => /(congr1 Right).
by rewrite derive1E row_mxKr => ?; rewrite derive_rsubmx.
Qed.

Lemma is_sol_state_space_tilt (D : R) f t :
  t \in `[0, D[%R ->
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  Tilt.Upsilon1 (f t).
Proof.
move=> + f0 deriv_f.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<- D0|t0 tD].
  exact/set_mem.
apply: (@tilt_state_spaceS _ alpha1 gamma) => //=.
exists f, D; split => //=.
exists t => //.
by rewrite in_itv/= (ltW t0) tD.
Qed.

Lemma enorm_e2z2 (D : R) f (z : R)
    (z2 := Right \o f) (zp1 := Left \o f) (u := 'e_2 - z2 z) :
  z \in `[0, D[%R ->
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f -> `|u|_e = 1.
Proof.
move=> z0D sol0 sol_f.
suff: Tilt.Upsilon1 (row_mx (zp1 z) (z2 z)).
  by rewrite /Tilt.Upsilon1/= row_mxKr.
rewrite /zp1 /z2 hsubmxK /=.
exact: (is_sol_state_space_tilt z0D).
Qed.

Lemma angvel_sqr (D : R) (f : R -> 'rV_6) z
    (z2 := fun r : R => Right (f r) : 'rV_3)
  (w := (z2 z) *m \S('e_2)) (u := 'e_2 - z2 z) :
  z \in `[0, D[%R ->
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  (w *m \S(u)) *d (w *m \S(u)) = (w *d w) * (u *d u) - (w *d u) ^+ 2.
Proof.
move=> z0D sol0 dtraj.
rewrite /dotmul !trmx_mul !tr_spin.
rewrite !mulNmx !mulmxN opprK.
rewrite !dotmulP.
have key_ortho : (z2 z *m \S('e_2)) *d u = 0.
 by rewrite dotmulC; exact/ortho_spin.
rewrite key_ortho expr2.
rewrite [in RHS]mxE.
rewrite [X in _ = - (w *m (\S('e_2) *m (z2 z)^T)) 0 0 * (u *d u)%:M 0 0
                  - 0%:M 0 0 * X]mxE.
rewrite mulr1n mulr0 subr0/=.
rewrite /u -/w /dotmul.
have Hw_ortho : (w *d u) = 0 by rewrite /u dotmulC ortho_spin.
rewrite !mulmxA.
rewrite [in RHS](dotmulP ('e_2 - _)) dotmulvv (enorm_e2z2 z0D)// expr2 mulr1.
rewrite [X in _ =  - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1n /=.
rewrite [X in _ =   - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1.
have wu0 : w *m u^T *m u = 0 by rewrite dotmulP Hw_ortho mul_scalar_mx scale0r.
rewrite -[in LHS](mulmxA w) sqr_spin; first by rewrite -/u (enorm_e2z2 z0D).
rewrite [in LHS]mulmxBr mulmxA wu0 sub0r.
by rewrite 2!mulNmx mulmx1 mxE.
Qed.

Lemma neg_spin (D : R) (f : R -> 'rV_6) z :
  z \in `[0, D[%R ->
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  `|Right (f z) *m \S('e_2) *m - \S('e_2 - Right (f z))|_e =
  `|Right (f z) *m \S('e_2)|_e.
Proof.
move=> z0D f0 dtraj.
rewrite mulmxN enormN.
pose zp1 := fun r => Left (f r).
pose z2 := fun r => Right (f r).
set w := (z2 z) *m \S('e_2).
have Upsilon1_traj : Tilt.Upsilon1 (f z) by apply/(is_sol_state_space_tilt z0D).
rewrite /enorm.
rewrite !dotmulvv [RHS]sqrtr_sqr sqrtr_sqr.
have Hnorm_sq : `|w *m \S('e_2 - Right (f z))|_e ^+ 2 = `|w|_e ^+ 2.
  rewrite -!dotmulvv (angvel_sqr z0D)// !dotmulvv (enorm_e2z2 z0D)//=.
  rewrite -!dotmulvv expr2 !mul1r mulr1.
  have -> : w *d ('e_2 - Right (f z)) = 0 by rewrite dotmulC ortho_spin.
  by rewrite expr2 mul0r subr0.
rewrite !normr_enorm.
by move/sqr_inj : Hnorm_sq => ->//; rewrite ?nnegrE ?enorm_ge0.
Qed.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

Lemma V1dotE z (D : R) (f : R -> 'rV_6)
  (zp1 := Left \o f) (z2 := Right \o f) :
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  z \in `]0, D[ ->
  V1dot (f z) =
    c1 *: (2 *: 'D_1 zp1 z *m (Left (f z))^T) 0 0 +
    c2 *: (2 *: 'D_1 z2 z *m (Right (f z))^T) 0 0.
Proof.
move=> fP zd.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC.
rewrite mulVf// div1r.
rewrite (derive_zp1 fP)// -scalemxAl mxE.
rewrite [X in X + _](mulrA (alpha1^-1) (- alpha1)).
rewrite mulrN mulVf ?gt_eqF// mulN1r.
rewrite (derive_z2 fP)// -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE.
rewrite scalerA mulVf ?gt_eqF// scale1r.
rewrite enorm_squared /V1dot.
congr +%R.
rewrite -2![in LHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
rewrite -[X in (X *m (_ *m _)) 0 0 = _]trmxK.
rewrite -[X in (_ *m (X *m _)) 0 0 = _]trmxK.
rewrite mulmxA -trmx_mul -trmx_mul [LHS]mxE.
rewrite -(mulmxA (Right (f z) - (Left (f z)))) mulmxE -expr2.
rewrite tr_sqr_spin.
by rewrite mulmxA.
Qed.

Lemma derive_along_V1 (D : R) t (f : R -> 'rV_6) :
  t \in `]0, D[ ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  (forall t, t \in `]0, D[ -> differentiable f t) ->
  'D~(f) (Tilt.V1 alpha1 gamma) t = V1dot (f t).
Proof.
move=> t0D tilt_eqnx dif1.
rewrite /Tilt.V1 derive_alongD.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl => //.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  exact: dif1.
rewrite derive_alongMl => //.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
rewrite !derive_along_enorm_squared//=.
- exact/differentiable_lsubmx_comp.
- exact: dif1.
- exact: dif1.
- rewrite (V1dotE tilt_eqnx).
    by move: t0D; rewrite !inE; apply: subset_itvr; rewrite bnd_simp.
  by rewrite /c1 /c2 !invfM.
Qed.

Definition u1 (f : R -> 'rV[R]_6) t
  (zp1 := Left \o f) (z2 := Right \o f)
  (w := z2 t *m \S('e_2)) : 'rV[R]_2 :=
  \row_(i < 2) [eta (fun=> 0) with 0 |-> `|zp1 t|_e, 1 |-> `|w|_e] i.

Lemma V1dot_ub (D : R) (f : R -> 'rV[R]_6)
    (zp1 := Left \o f) (z2 := Right \o f) :
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  forall t, t \in `[0, D[%R ->
    V1dot (f t) <= (- (u1 f t) *m u2 *m (u1 f t)^T) 0 0.
Proof.
move=> f0 fP z z0D.
set w := z2 z *m \S('e_2).
rewrite /V1dot.
rewrite mxE norm_spin mxE addrA expr2 mulmxA.
have -> : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2).
  by rewrite spinD spinN -tr_spin !mulmxDr !mul_tr_spin !addr0.
rewrite -dotmulNv addrC -mulmxN -expr2.
have cauchy : ((w *m - \S('e_2 - z2 z) *d (zp1 z))%:M : 'rV_1) 0 0 <=
              `|w *m - \S('e_2 - z2 z)|_e * `|zp1 z|_e.
  rewrite mxE /= mulr1n (le_trans (ler_norm _)) //.
  rewrite -ler_sqr//.
    by rewrite nnegrE // mulr_ge0 ?enorm_ge0.
  by rewrite exprMn sqr_normr (le_trans (CauchySchwarz_rV _ _)) // !dotmulvv.
apply: (@le_trans _ _ (`|w *m - \S('e_2 - z2 z)|_e * `|zp1 z|_e +
                       (- `|zp1 z|_e ^+ 2 - `|w|_e ^+ 2))).
  rewrite lerD2r (le_trans _ cauchy)//.
  by rewrite mxE eqxx mulr1n.
rewrite (neg_spin z0D)// /u1 /u2.
rewrite mxE.
rewrite !sum2E/= ![in leRHS]mxE !sum2E/= ![in leRHS]mxE /=.
rewrite !mulr1 mulrN mulNr opprK mulrDl mulNr -expr2.
rewrite [in leLHS] addrCA -!addrA lerD2l mulrDl (mulNr `|w|_e).
rewrite -expr2 !addrA lerD2r !(mulrN, mulNr) opprK -mulrA.
rewrite !mulrA.
rewrite !(mulrC _ `| Left (f z) |_e).
rewrite !mulrA.
rewrite !(mulrC _ 2^-1).
rewrite !mulrA.
by rewrite -!mulrDl -div1r -splitr mul1r.
Qed.

Lemma V1dot_eq0_p1_or_p2 (D : R) (f : R -> 'rV[R]_6) t :
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  t \in `[0, D[%R ->
  V1dot (f t) = 0 ->
  f t = Tilt.point1 \/ f t = Tilt.point2.
Proof.
move => f0 fP t0d V1df.
have h : u1 f t = 0.
  case: (u1 f t =P 0) => [-> // |/eqP hf].
  have := V1dot_ub f0 fP t0d.
  have := u2_quadratic_form_gt0 hf.
  rewrite V1df !mulNmx !mxE oppr_ge0.
  move => h1 h2.
  have := lt_le_trans h1 h2.
  by rewrite ltxx.
have L0 : Left (f t) = 0.
  apply/eqP; rewrite -enorm_eq0; apply /eqP.
  have := congr1 (fun v : 'rV_2 => v ord0 ord0) h.
  by rewrite !mxE/=.
have R0 : (Right (f t)) *m \S('e_2) = 0.
  apply/eqP; rewrite -enorm_eq0; apply/eqP.
  have := congr1 (fun v : 'rV_2 => v ord0 ord_max) h.
  by rewrite !mxE/=.
rewrite -(hsubmxK (n1:=3) (f t)).
rewrite L0.
suff [-> | -> ] : Right (f t) = 0 \/ Right (f t) = (2 *: 'e_2).
  left;apply /matrixP => i j;rewrite mxE.
  case: splitP => // k _;by rewrite !mxE.
  right;apply /matrixP => i j;rewrite mxE.
  by case: splitP => // k _.
have := is_sol_state_space_tilt t0d f0 fP.
rewrite /Tilt.Upsilon1/=.
have /sub_rVP [k ->] : (Right (f t) <= ('e_2 : 'rV_3))%MS.
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

Lemma derive_along_V1_le0 (D : R) (f : R -> 'rV_6) :
  f 0 \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  (forall t, t \in `]0, D[%R -> differentiable f t) ->
  forall t, t \in `]0, D[%R ->
  'D~(f) (Tilt.V1 alpha1 gamma) t <= 0.
Proof.
move=> sol0 solP diff t t0.
have {}t0 : t \in `]0, D[ by rewrite inE.
rewrite (derive_along_V1 t0)//.
  move=> t1 t10D.
  apply: diff => //.
  by rewrite inE/= in t10D.
have /(V1dot_ub sol0 solP) : t \in `[0, D[%R.
  rewrite inE in t0.
  by apply: subset_itvr t0; rewrite bnd_simp.
move/le_trans; apply.
have Hquad : let u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o f) t|_e,
                        1 |-> `|(Right \o f) t *m \S('e_2)|_e]
                         i in 0 <= (u1 *m u2 *m u1^T) 0 0.
  set u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o f) t|_e,
                        1 |-> `|(Right \o f) t *m \S('e_2)|_e]
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
Context {R : realType}.
Variables alpha1 gamma : R.
Hypotheses (alpha1_gt0 : 0 < alpha1) (gamma_gt0 : 0 < gamma).
Let phi := Tilt.eqn alpha1 gamma.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

(* todo: copy paste *)
Lemma derive_zp10 (sol : R -> 'rV_6) :
  sol_is_deriv_c0y phi sol ->
  'D_1 (Left \o sol) 0 = - alpha1 *: Left (sol 0).
Proof.
move/sol_is_deriv_c0yP.
move/(_ _ (lexx 0)) => [d0 +].
move=> /(congr1 Left).
rewrite derive1E row_mxKl => <-.
by rewrite derive_lsubmx.
Qed.

Lemma derive_z20 (sol : R -> 'rV_6) :
  sol_is_deriv_c0y phi sol ->
  'D_1 (Right \o sol) 0 =
  gamma *: (Right (sol 0) - Left (sol 0)) *m \S('e_2 - Right (sol 0)) ^+ 2.
Proof.
move/sol_is_deriv_c0yP.
move /(_ _ (lexx 0)) => [d0 +].
move => /(congr1 Right).
rewrite derive1E.
by rewrite row_mxKr => ?; rewrite derive_rsubmx.
Qed.

Lemma V1dotE0 (sol : R -> 'rV_6) (zp1 := Left \o sol) (z2 := Right \o sol) :
  sol_is_deriv_c0y phi sol ->
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

Lemma derive_along_V1_global t (sol : R -> 'rV_6) :
  0 <= t ->
  sol_is_deriv_c0y phi sol ->
  'D~(sol) (Tilt.V1 alpha1 gamma) t = V1dot (sol t).
Proof.
move=> t0 tilt_eqnx.
have dif1 : forall t : R, 0 <= t -> differentiable sol t.
   move => /= t' t'0.
   apply/derivable1_diffP.
   move/sol_is_deriv_c0yP in tilt_eqnx.
   by apply tilt_eqnx.
rewrite /Tilt.V1 derive_alongD.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl//.
  exact/differentiable_enorm_squared/differentiable_lsubmx_comp.
  exact: dif1.
rewrite derive_alongMl => //.
  exact/differentiable_enorm_squared/differentiable_rsubmx_comp.
  exact: dif1.
rewrite !derive_along_enorm_squared//=.
  exact/differentiable_lsubmx_comp.
  exact: dif1.
  exact: dif1.
move: t0; rewrite le_eqVlt => /predU1P[<-//|t0].
  by rewrite V1dotE0// !invfM.
have is_sol_oo_sol : is_sol_cauchy_oo (fun=> Tilt.eqn alpha1 gamma) (sol 0) 0 (t + 1) sol.
  split.
    by [].
  split.
    rewrite /sol_is_deriv_obnd/= => t' t'0t1.
    apply: tilt_eqnx.
    by apply: subset_itv t'0t1 => //; rewrite bnd_simp.
  apply: continuous_in_subspaceT => /= t'.
  rewrite closure_itvoo ?addr_gt0// => /[!inE] t'0t1.
  apply: differentiable_continuous.
  apply: dif1.
  by rewrite (itvP t'0t1).
rewrite (V1dotE alpha1_gt0 gamma_gt0 is_sol_oo_sol) //.
  by rewrite inE/= in_itv/= t0 ltrDl ltr01.
by rewrite !invfM.
Qed.

Lemma derive_along_V1_le0_global (sol : R -> 'rV[R]_6) :
  sol 0 \in Tilt.Upsilon1 ->
  sol_is_deriv_c0y phi sol ->
  forall t : R, 0 <= t  ->
  'D~(sol) (Tilt.V1 alpha1 gamma) t <= 0.
Proof.
move=> sol0 solves.
have diff : forall (t : R), 0 <= t -> differentiable sol t.
   move => /= t' t0'.
   apply/derivable1_diffP.
   move/sol_is_deriv_c0yP in solves.
   by apply solves.
move => t t0.
rewrite derive_along_V1_global//.
have t0D : t \in `[0, t + 1[%R.
  by rewrite in_itv/=t0 ltrDl ltr01.
have is_sol_oo_sol : is_sol_cauchy_oo (fun=> Tilt.eqn alpha1 gamma) (sol 0) 0 (t + 1) sol.
  split.
    by [].
    split.
      rewrite /sol_is_deriv_obnd/= => t' t'0t1.
      apply: solves.
      by apply: subset_itv t'0t1 => //; rewrite bnd_simp.
  apply: continuous_in_subspaceT => /= t'.
  rewrite closure_itvoo; first by rewrite ltr_wpDl.
  move=> /[!inE] t'0t1.
  apply: differentiable_continuous.
  apply: diff.
  by rewrite (itvP t'0t1).
have Hub := V1dot_ub sol0 is_sol_oo_sol t0D.
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
Context {R : realType} (gamma alpha1 : R).
Hypotheses (gamma_gt0 : 0 < gamma) (alpha1_gt0 : 0 < alpha1).
Let phi := Tilt.eqn alpha1 gamma.
Variable Init : set 'rV[R]_6.

Lemma equilibrium_zero_stable :
  Tilt.point1 \in Init -> Init `<=` Tilt.Upsilon1 ->
  is_stable_at phi Init Tilt.point1.
Proof.
move=> Init0 Init_in_state.
apply: (@Lyapunov_stability R _ phi setT openT Init (Tilt.V1 alpha1 gamma)).
- exact: V1_diff.
- move=> D /= f f0 sol_f t t0.
  apply: (@derive_along_V1_le0 _ _ _ _ _ D f) => //.
  + rewrite inE.
    apply: Init_in_state.
    exact/set_mem.
 + move=> /= t1 t10D.
   have [_ [d _]] := sol_f.
   by apply/derivable1_diffP;apply d.
- have := V1_is_Lyapunov_candidate alpha1_gt0 gamma_gt0.
  rewrite /is_Lyapunov_candidate /Tilt.point1 => H.
  rewrite /Tilt.V1 lsubmx_const rsubmx_const; split => //.
  + by rewrite inE.
  + by rewrite !expr2 !enorm0 !mulr0 !mul0r add0r.
  + move=> z zInit z_neq0.
    case: H => // _ _.
    by apply => //; rewrite in_setT.
Qed.

End equilibrium_zero_stable.
