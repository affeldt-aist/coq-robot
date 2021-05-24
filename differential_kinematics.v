(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import realalg complex fingroup perm.
From mathcomp.analysis Require Import boolp reals Rstruct classical_sets posnum.
From mathcomp.analysis Require Import topology normedtype landau forms derive.
Require Import ssr_ext derive_matrix euclidean frame rot skew rigid.

(******************************************************************************)
(* This file is wip. It contains an on-going formalization of                 *)
(* [sciavicco] chap. 3.                                                       *)
(******************************************************************************)

(* contents:
  5. Module BoundVect.
     Module RFrame.
     relative frame
     (NB: to be moved to frame.v)
  6. Section kinematics
     velocity composition rule
  7. Section link_velocity.
  8. Lemma ang_vel_mx_Rz
     example: angular velocity of Rz as a spinor
  9. Section chain. (wip)
  10. Section geometric_jacobian_computation.
      geometric jacobian
  11. Section scara_geometric_jacobian.
      computation of SCARA's geometric jacobian
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope frame_scope.

Module BoundVect. (* i.e., point of application prescribed *)
Section bound_vector.
Variable T : ringType.
Record t (F : tframe T) := mk { endp : 'rV[T]_3 }.
Definition startp F (v : t F) : 'rV[T]_3 := \o{F}.
End bound_vector.
End BoundVect.
Notation bvec := BoundVect.t.
Coercion boundvectendp T (F : tframe T) (v : bvec F) := BoundVect.endp v.

Definition bvec0 T (F : tframe T) : bvec F := BoundVect.mk _ 0.

Reserved Notation "a \+b b" (at level 39).
Reserved Notation "a \-b b" (at level 39).

Section about_bound_vectors.

Variables (T : ringType) (F : tframe T).

Definition FramedVect_of_Bound (p : bvec F) : fvec F := `[ BoundVect.endp p $ F ].

Definition BoundVect_add (a b : bvec F) : bvec F :=
  BoundVect.mk F (BoundVect.endp a + BoundVect.endp b).

Definition BoundFramed_add (a : bvec F) (b : fvec F) : bvec F :=
  BoundVect.mk F (BoundVect.endp a + FramedVect.v b).

Local Notation "a \+b b" := (BoundFramed_add a b).

Lemma BoundFramed_addA (a : bvec F) (b c : fvec F) :
  a \+b b \+b c = a \+b (b \+f c).
Proof. by rewrite /BoundFramed_add /= addrA. Qed.

Definition BoundVect_sub (F : tframe T) (a b : bvec F) : fvec F :=
  `[ BoundVect.endp a - BoundVect.endp b $ F ].

Local Notation "a \-b b" := (BoundVect_sub a b).

Lemma bv_eq (a b : bvec F) : a = b :> 'rV[T]_3 -> a = b.
Proof. by move: a b => [a] [b] /= ->. Qed.

End about_bound_vectors.

Notation "a \+b b" := (BoundFramed_add a b).
Notation "a \-b b" := (BoundVect_sub a b).

Lemma derive1mx_BoundFramed_add (R : realFieldType) (F : tframe [ringType of R^o])
  (Q : R -> bvec F) (Z : R -> fvec F) t :
  derivable_mx (fun x => BoundVect.endp (Q x)) t 1 ->
  derivable_mx (fun x => FramedVect.v (Z x)) t 1 ->
  derive1mx (fun x => BoundVect.endp (Q x \+b Z x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
    derive1mx (fun x => FramedVect.v (Z x)) t.
Proof.
move=> H H'.
rewrite (_ : (fun x : R => _) = (fun x : R => BoundVect.endp (Q x) +
  (FramedVect.v (Z x)))); last by rewrite funeqE.
rewrite derive1mxD.
- by [].
- exact: H.
- exact H'.
Qed.

Module RFrame.
Section rframe.
Variable T : ringType.
Record t (F0 : tframe T) := mk {
  o : bvec F0 ;
  i : fvec F0 ;
  j : fvec F0 ;
  k : fvec F0 ;
  F : tframe T ;
  _ : BoundVect.endp o = \o{F} ;
  _ : FramedVect.v i = F~i ;
  _ : FramedVect.v j = F~j ;
  _ : FramedVect.v k = F~k ;
}.
End rframe.
End RFrame.
Notation rframe := RFrame.t.
Coercion tframe_of_rframe R (F : tframe R) (F : rframe F) : tframe R := RFrame.F F.

Lemma RFrame_o T (F0 : tframe T) (F1 : rframe F0) :
  BoundVect.endp (RFrame.o F1) = \o{RFrame.F F1}.
Proof. by destruct F1. Qed.

(* lemmas about relative frames *)

Lemma BoundVect0_fixed (R : realFieldType) T (F : tframe T) (F1 : R -> rframe F) t :
  BoundVect.endp (bvec0 (F1 t)) = BoundVect.endp (bvec0 (F1 0)).
Proof. by []. Qed.

Section derivable_FromTo.

Lemma derivable_mx_FromTo' (R : realFieldType) (F : R -> tframe [ringType of R^o])
  (G' : forall t, rframe (F t)) (G : forall t, rframe (F t)) t :
  derivable_mx F t 1 -> derivable_mx G t 1 -> derivable_mx G' t 1 ->
  derivable_mx (fun x => (G x) _R^ (G' x)) t 1.
Proof.
move=> HF HG HG' a b.
rewrite (_ : (fun x => _) = (fun x => row a (G x) *d row b (G' x))); last first.
  by rewrite funeqE => t'; rewrite !mxE.
evar (f : 'I_3 -> R^o -> R^o).
rewrite (_ : (fun x => _) = \sum_i f i); last first.
  rewrite funeqE => t'; rewrite dotmulE fct_sumE; apply: eq_bigr => /= i _.
  rewrite !mxE /f; reflexivity.
rewrite {}/f.
apply: derivable_sum => i.
apply: derivableM; [exact: HG | exact: HG'].
Qed.

Lemma derivable_mx_FromTo (R : realFieldType) (F : R -> tframe [ringType of R^o])
  (G : forall t, rframe (F t)) t :
  derivable_mx F t 1 -> derivable_mx G t 1 ->
  derivable_mx (fun x => (G x) _R^ (F x)) t 1.
Proof.
move=> HF HG a b.
have @G' : forall t0, rframe (F t0).
  move=> t0.
  exact: (@RFrame.mk _ _ (@BoundVect.mk _ _ \o{F t0}) `[(F t0)~i $ F t0] `[(F t0)~j $ F t0] `[(F t0)~k $ F t0] (F t0)).
apply: (@derivable_mx_FromTo' R F G' G).
by [].
by [].
rewrite {}/G' /=.
exact: HF.
Qed.

Lemma derivable_mx_FromTo_fixed (R : realFieldType)
  (F : tframe [ringType of R^o]) (G : R -> rframe F) t :
  derivable_mx G t 1 -> derivable_mx (fun x => (G x) _R^ F) t 1.
Proof.
move=> H; apply derivable_mx_FromTo; [move=> a b; exact: ex_derive | exact H].
Qed.

Lemma derivable_mx_FromTo_tr (R : realFieldType)
  (F : tframe [ringType of R^o]) (G : R -> rframe F) t :
  derivable_mx (fun x => F _R^ (G x)) t 1 = derivable_mx (fun x => F _R^ (G x)) t 1.
Proof. by rewrite trmx_derivable. Qed.

End derivable_FromTo.

(* the coordinate transformation of a point P1 from frame F1 to frame F
  (eqn 2.33, 3.10) *)
Definition coortrans (R : rcfType) (F : tframe [ringType of R^o]) (F1 : rframe F)
    (P1 : bvec F1) : bvec F :=
  RFrame.o F1 \+b rmap F (FramedVect_of_Bound P1).

(* motion of P1 w.r.t. the fixed frame F (eqn B.2) *)
Definition motion (R : rcfType) (F : tframe [ringType of R^o]) (F1 : R -> rframe F)
  (P1 : forall t, bvec (F1 t)) t : bvec F := coortrans (P1 t).

(* [sciavicco] p.351-352  *)
Section kinematics.

Variables (R : rcfType) (F : tframe [ringType of R^o]). (* fixed frame *)
Variable F1 : R -> rframe F. (* time-varying frame (origin and basis in F) *)
Hypothesis derivable_F1 : forall t, derivable_mx F1 t 1.
Hypothesis derivable_F1o : forall t, derivable_mx (@TFrame.o [ringType of R^o] \o F1) t 1.

Variable P1 : forall t, bvec (F1 t). (* point with coordinates in F1 *)
(* NB: compared with [sciavicco] p.351, P1 not necessarily fixed in F1 *)
Hypothesis derivable_mxP1 : forall t, derivable_mx (fun x => BoundVect.endp (P1 x)) t 1.

Let P : R -> bvec F := motion P1.

Variable Q1 : forall t, bvec (F1 t).
Hypothesis Q1_fixed_in_F1 : forall t, BoundVect.endp (Q1 t) = BoundVect.endp (Q1 0).

Let Q : R -> bvec F := motion Q1.

(* eqn B.3 *)
Lemma eqnB3 t : P t = Q t \+b rmap F (P1 t \-b Q1 t).
Proof.
rewrite /P /Q /motion /coortrans BoundFramed_addA; congr (_ \+b _).
apply fv_eq => /=; rewrite -mulmxDl; congr (_ *m _).
by rewrite addrCA subrr addr0.
Qed.

Lemma derivable_mx_Q t : derivable_mx (fun x => BoundVect.endp (Q x)) t 1.
Proof.
rewrite /Q /=; apply derivable_mxD.
  move=> a b.
  move: (@derivable_F1o t a b).
  rewrite (_ : (fun x => \o{F1 x} a b) =
    (fun x => BoundVect.endp (RFrame.o (F1 x)) a b)) // funeqE => x.
  destruct (F1 x) => /=; by rewrite e.
apply derivable_mxM; last exact: derivable_mx_FromTo.
rewrite (_ : (fun x => _) = (fun _ => BoundVect.endp (Q1 0))); last first.
  rewrite funeqE => x; by rewrite Q1_fixed_in_F1.
move=> a b; exact: ex_derive.
Qed.

Let Rot := fun t => (F1 t) _R^ F.

(* generalization of B.4  *)
Lemma velocity_composition_rule (t : R) :
  derive1mx (fun x => BoundVect.endp (P x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
  derive1mx P1 t *m Rot t (* rate of change of the coordinates P1 expressed in the frame F *) +
  ang_vel Rot t *v FramedVect.v (P t \-b Q t).
Proof.
rewrite {1}(_ : P = fun t => Q t \+b rmap F (P1 t \-b Q1 t)); last first.
  by rewrite funeqE => t'; rewrite eqnB3.
rewrite (derive1mx_BoundFramed_add (@derivable_mx_Q t)); last first.
  apply derivable_mxM; last exact: derivable_mx_FromTo.
  rewrite (_ : (fun x => _) = (fun x => FramedVect.v (FramedVect_of_Bound (P1 x)) -
    FramedVect.v (FramedVect_of_Bound (Q1 0)))); last first.
    rewrite funeqE => x; by rewrite /= Q1_fixed_in_F1.
  apply: derivable_mxB => /=.
  exact: derivable_mxP1.
  move=> a b; exact: ex_derive.
rewrite -addrA; congr (_ + _).
rewrite [in LHS]/rmap [in LHS]/= derive1mxM; last 2 first.
  rewrite {1}(_ : (fun x  => _) = (fun x  => BoundVect.endp (P1 x) -
    BoundVect.endp (Q1 0))); last first.
    by rewrite funeqE => ?; rewrite Q1_fixed_in_F1.
  apply: derivable_mxB.
    exact: derivable_mxP1.
    move=> a b; exact: ex_derive.
  exact: derivable_mx_FromTo.
rewrite derive1mxB; last 2 first.
  exact: derivable_mxP1.
  rewrite (_ : (fun x => _) = cst (BoundVect.endp (Q1 0))); last first.
    by rewrite funeqE => x; rewrite Q1_fixed_in_F1.
  exact: derivable_mx_cst.
congr (_*m _  + _).
  rewrite [in X in _ + X = _](_ : (fun x => _) = cst (BoundVect.endp (Q1 0))); last first.
    by rewrite funeqE => x; rewrite Q1_fixed_in_F1.
  by rewrite derive1mx_cst subr0.
rewrite -spinE unspinK; last first.
  rewrite ang_vel_mx_is_so; first by [].
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite /ang_vel_mx mulmxA; congr (_ *m _).
rewrite /P /Q /= opprD addrACA subrr add0r mulmxBl -!mulmxA.
by rewrite orthogonal_mul_tr ?FromTo_is_O // !mulmx1.
Qed.

Hypothesis P1_fixed_in_F1 : forall t, BoundVect.endp (P1 t) = BoundVect.endp (P1 0).

(* eqn B.4 *)
Lemma velocity_composition_rule_spec (t : R) :
  derive1mx (fun x => BoundVect.endp (P x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
  ang_vel Rot t *v (FramedVect.v (P t \-b Q t)).
Proof.
rewrite velocity_composition_rule; congr (_ + _).
suff -> : derive1mx P1 t = 0 by rewrite mul0mx addr0.
apply/matrixP => a b; rewrite !mxE.
rewrite (_ : (fun x => _) = cst (P1 0 a b)); last first.
  rewrite funeqE => x /=; by rewrite /boundvectendp (P1_fixed_in_F1 x).
by rewrite derive1_cst.
Qed.

End kinematics.

(* [sciavicco] p.81-82 *)
Section derivative_of_a_rotation_matrix_contd.

Variables (R : rcfType) (F : tframe [ringType of R^o]).
Variable F1 : R -> rframe F.
Hypothesis derivable_F1 : forall t, derivable_mx F1 t 1.
Variable p1 : forall t, bvec (F1 t).
Hypothesis derivable_mx_p1 : forall t, derivable_mx (fun x => BoundVect.endp (p1 x)) t 1.
Hypothesis derivable_F1o : forall t, derivable_mx (@TFrame.o [ringType of R^o] \o F1) t 1.

Definition p0 := motion p1.

Lemma eqn312 t :
  derive1mx (fun x => BoundVect.endp (motion p1 x)) t =
  derive1mx (fun x => BoundVect.endp (motion (fun=> bvec0 (F1 x)) t)) t +
  derive1mx p1 t *m (F1 t) _R^ F +
  ang_vel (fun t => (F1 t) _R^ F) t *v (p1 t *m (F1 t) _R^ F).
Proof.
rewrite (@velocity_composition_rule _ F _ derivable_F1 derivable_F1o p1 derivable_mx_p1
  (fun t => bvec0 (F1 t)) (@BoundVect0_fixed _ _ _ F1)).
congr (_ + _ *v _).
by rewrite /= mul0mx addr0 addrAC subrr add0r.
Qed.

End derivative_of_a_rotation_matrix_contd.

Require Import screw.

(* [murray p.54] chapter 2, section 4.2*)
Section rigid_body_velocity.

Section spatial_velocity.

Variables (R : realType) (M : R -> 'M[R^o]_4).
Hypothesis derivableM : forall t, derivable_mx M t 1.
Hypothesis MSE : forall t, M t \in 'SE3[R].

Definition spatial_velocity t : 'M_4 := (M t)^-1 * derive1mx M t.

Definition spatial_lin_vel :=
  let r : R -> 'M[R^o]_3 := @rot_of_hom _ \o M in
  let p : R -> 'rV[R^o]_3:= @trans_of_hom _ \o M in
  fun t => - p t *m (r t)^T *m derive1mx r t + derive1mx p t.

Lemma spatial_velocityE t :
  let r : R -> 'M[R^o]_3 := @rot_of_hom _ \o M in
  spatial_velocity t = block_mx (ang_vel_mx r t) 0 (spatial_lin_vel t) 0.
Proof.
move=> r.
rewrite /spatial_velocity.
transitivity (inv_hom (M t) * derive1mx M t) => //.
  by rewrite inv_homE.
rewrite /inv_hom.
rewrite /hom.
rewrite derive1mx_SE //.
rewrite (_ : rot_of_hom (M t) = r t) // -/r.
rewrite -mulmxE.
rewrite (mulmx_block (r t)^T _ _ _ (derive1mx r t)).
rewrite !(mul0mx,add0r,mul1mx,mulmx0,trmx0,addr0,mulmx1).
by rewrite mulmxE -/(ang_vel_mx r t).
Qed.

Lemma spatial_velocity_in_se3 x : spatial_velocity x \in 'se3[[rcfType of R^o]].
Proof.
rewrite spatial_velocityE. set r := @rot_of_hom _.
rewrite qualifE block_mxKul block_mxKur block_mxKdr 2!eqxx 2!andbT.
rewrite ang_vel_mx_is_so // => t0.
by rewrite rotation_sub // rot_of_hom_is_SO.
exact: derivable_rot_of_hom.
Qed.

Lemma spatial_velocity_is_twist x :
  let r : R -> 'M[R^o]_3 := @rot_of_hom _ \o M in
  spatial_velocity x = wedge \T( spatial_lin_vel x , unspin (ang_vel_mx r x)).
Proof.
move=> r.
rewrite spatial_velocityE.
rewrite /wedge lin_tcoorE ang_tcoorE unspinK //.
rewrite ang_vel_mx_is_so // => t0.
by rewrite rotation_sub // rot_of_hom_is_SO.
exact: derivable_rot_of_hom.
Qed.

End spatial_velocity.

Section body_velocity.

Variables (R : realType) (M : R -> 'M[R^o]_4).
Hypothesis derivableM : forall t, derivable_mx M t 1.
Hypothesis MSE : forall t, M t \in 'SE3[R].

Definition body_velocity t : 'M_4 := derive1mx M t * (M t)^-1.

Definition body_lin_vel :=
  let r : R -> 'M[R^o]_3 := @rot_of_hom _ \o M in
  let p : R -> 'rV[R^o]_3:= @trans_of_hom _ \o M in
  fun t => derive1mx p t *m (r t)^T.

Lemma body_ang_vel_is_so t : body_ang_vel_mx (@rot_of_hom _ \o M) t \is 'so[R]_3.
Proof.
rewrite /body_ang_vel_mx.
have : forall t, (@rot_of_hom [rcfType of R^o] \o M) t \is 'O[[ringType of R]]_3.
  move=> t0; by rewrite rotation_sub // rot_of_hom_is_SO.
move/ang_vel_mx_is_so => /(_ (derivable_rot_of_hom derivableM))/(_ t).
rewrite /ang_vel_mx.
move/(conj_so (((rot_of_hom (T:=[rcfType of R^o]) \o M) t)^T)).
rewrite !mulmxA !trmxK orthogonal_mul_tr ?rotation_sub // ?rot_of_hom_is_SO //.
by rewrite mul1mx.
Qed.

Lemma body_velocityE t : let r : R -> 'M[R^o]_3 := @rot_of_hom _ \o M in
  body_velocity t = block_mx (body_ang_vel_mx r t) 0 (body_lin_vel t) 0.
Proof.
move=> r.
rewrite /body_velocity.
transitivity (derive1mx M t * inv_hom (M t)).
  by rewrite inv_homE.
rewrite /inv_hom.
rewrite /hom.
rewrite derive1mx_SE //.
rewrite (_ : rot_of_hom (M t) = r t) // -/r.
rewrite -mulmxE.
rewrite (mulmx_block (derive1mx r t) _ _ _ (r t)^T).
rewrite !(mul0mx,add0r,mul1mx,mulmx0,trmx0,addr0,mulmx1).
by rewrite -/(body_ang_vel_mx _) -/(body_lin_vel _).
Qed.

Lemma body_velocity_is_se x : body_velocity x \is 'se3[R].
Proof.
rewrite body_velocityE.
rewrite qualifE block_mxKul block_mxKur block_mxKdr 2!eqxx 2!andbT.
by rewrite body_ang_vel_is_so.
Qed.

End body_velocity.

Section spatial_body_adjoint.

Variables (R : realType) (M : R -> 'M[R^o]_4).
Hypothesis derivableM : forall t, derivable_mx M t 1.
Hypothesis MSE : forall t, M t \in 'SE3[R].

Lemma spatial_body_velocity x :
  vee (spatial_velocity M x) = vee (body_velocity M x) *m Adjoint (M x).
Proof.
rewrite -/(SE3_action _ _) action_Adjoint; last by [].
congr vee; rewrite /spatial_velocity -mulmxE -mulmxA; congr (_ * _).
rewrite veeK; last by rewrite body_velocity_is_se.
by rewrite /body_velocity -mulmxA mulVmx ?mulmx1 // SE3_in_unitmx.
Qed.

End spatial_body_adjoint.

End rigid_body_velocity.

(* [sciavicco] p.83 *)
Section link_velocity.

Variables (R : realType) (F : tframe [ringType of R^o]).
Variable F1 : R -> rframe F.
Variable F2 : R -> rframe F.
Let o1 t : bvec F := RFrame.o (F1 t).
Let o2 t : bvec F := RFrame.o (F2 t).

Let r12 : forall t : R, bvec (F1 t) := fun t =>
  BoundVect.mk (F1 t)
    (FramedVect.v (rmap (F1 t) `[ \o{F2 t} - \o{F1 t} $ F ])).

Hypothesis derivable_F1 : forall t, derivable_mx F1 t 1.
Hypothesis derivable_F1o : forall t, derivable_mx (@TFrame.o [ringType of R^o] \o F1) t 1.
Hypothesis derivable_r12 : forall t, derivable_mx (fun x => BoundVect.endp (r12 x)) t 1.
Hypothesis derivable_F2 : forall t, derivable_mx F2 t 1.

Lemma eqn310' t : o2 t = o1 t \+b rmap F (FramedVect_of_Bound (r12 t)).
Proof.
rewrite /o2 /o1 /= /r12 /= /rmap /= /BoundFramed_add /=; apply bv_eq => /=.
rewrite -mulmxA FromTo_comp FromToI mulmx1 /= addrCA RFrame_o /=.
by rewrite subrr addr0 -RFrame_o.
Qed.

Definition w1 := ang_vel (fun t => (F1 t) _R^ F).

Lemma eqn314_helper t : FramedVect.v (rmap F `[r12 t $ F1 t]) = \o{F2 t} - \o{F1 t}.
Proof. by rewrite /= -mulmxA FromTo_comp FromToI mulmx1. Qed.

(* lin. vel. of Link i as a function of
   the translational and rotational velocities of Link i-1 *)
Lemma eqn314 t : derive1mx o2 t = derive1mx o1 t +
  FramedVect.v (rmap F `[derive1mx r12 t $ F1 t])
    (* velocity of the origin of Frame i w.r.t. the origin of Frame i-1 *) +
  w1 t *v (\o{F2 t} - \o{F1 t}).
Proof.
rewrite -eqn314_helper.
move: (@eqn312 _ F _ derivable_F1 _ derivable_r12 derivable_F1o t).
have -> : derive1mx (fun x => BoundVect.endp (motion r12 x)) t = derive1mx o2 t.
  rewrite (_ : (fun x => BoundVect.endp (motion r12 x)) = o2) //.
  rewrite funeqE => t' /=; rewrite -mulmxA FromTo_comp FromToI mulmx1.
  rewrite addrCA RFrame_o subrr addr0.
  by rewrite /o2 -RFrame_o.
move=> ->.
rewrite -!{1}addrA /=; apply: f_equal2; last by [].
rewrite (_ : (fun x => BoundVect.endp (motion (fun _ : R => bvec0 (F1 x)) t)) = o1) //.
rewrite funeqE => t'.
by rewrite /motion /= mul0mx addr0.
Qed.

Definition w2 : R -> 'rV_3 := ang_vel (fun t => (F2 t) _R^ F).
Definition w12 : R -> 'rV_3 := ang_vel (fun t => (F2 t) _R^ (F1 t)).

(* ang. vel. of Link i as a function of the ang. vel. of Link i-1 and of Link i w.r.t. Link i-1 *)
Lemma eqn316 t : w2 t = w1 t + w12 t *m ((F1 t) _R^ F).
Proof.
have : (fun t => (F2 t) _R^ F) = (fun t => ((F2 t) _R^ (F1 t)) *m ((F1 t) _R^ F)).
  by rewrite funeqE => ?; rewrite FromTo_comp.
move/(congr1 (fun x => derive1mx x)).
rewrite funeqE.
move/(_ t).
rewrite derive1mxM; last 2 first.
  move=> t'; exact: derivable_mx_FromTo'.
  move=> t'; exact: derivable_mx_FromTo.
rewrite derive1mx_ang_vel; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite derive1mx_ang_vel; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo'.
rewrite derive1mx_ang_vel; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite ang_vel_mxE; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite ang_vel_mxE; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo'.
rewrite ang_vel_mxE; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite mulmxE -[in X in _ = X + _](mulr1 ((F2 t) _R^ (F1 t))).
rewrite -(@orthogonal_tr_mul _ _ (F _R^ (F1 t))) ?FromTo_is_O //.
rewrite -{2}(trmx_FromTo (F1 t) F).
rewrite -!mulrA.
rewrite (mulrA _ _ ((F1 t) _R^ F)).
rewrite (@spin_similarity _ ((F1 t) _R^ F)) ?FromTo_is_SO //.
rewrite mulrA -mulmxE.
rewrite trmx_FromTo.
rewrite FromTo_comp.
rewrite mulmxA.
rewrite FromTo_comp.
rewrite -mulmxDr.
rewrite -spinD.
rewrite -/w2 -/w1 -/w12.
rewrite mulmxE.
move/mulrI.
rewrite FromTo_unit => /(_ isT)/eqP.
rewrite spin_inj => /eqP.
by rewrite addrC.
Qed.

End link_velocity.

Require Import angle.

Definition Cos {R : realType} (x : R) : R := cos (Rad.angle_of x).
Definition Sin {R : realType} (x : R^o) : R^o := sin (Rad.angle_of x).

Axiom derive1_Cos : forall (R : realType) (t : R), derive1 (Cos : R^o -> R^o) t = - Sin t.
Axiom derive1_Sin : forall (R : realType) (t : R), derive1 Sin t = Cos t.
Axiom derivable_Sin : forall (R : realType) (t : R), derivable Sin t 1.
Axiom derivable_Cos : forall (R : realType) (t : R), derivable (Cos : R^o -> R^o) t 1.
Axiom derivable_Cos_comp : forall (R : realType) (t : R) (a : R^o -> R^o), derivable a t 1 ->
  derivable (Cos \o a : R^o -> R^o) t 1.
Axiom derivable_Sin_comp : forall (R : realType) (t : R) (a : R^o -> R^o), derivable a t 1 ->
  derivable (Sin \o a) t 1.

Lemma derive1_Cos_comp (R : realType) t (a : R^o -> R^o) : derivable a t 1 ->
  derive1 (Cos \o a : R^o -> R^o) t = - (derive1 a t) * Sin (a t).
Proof.
move=> H; rewrite (chain_rule H) ?derive1_Cos 1?mulrC ?(mulNr,mulrN).
by [].
exact: derivable_Cos.
Qed.

Lemma derive1mx_RzE (R : realType) (a : R^o -> R^o) t : derivable a t 1 ->
  derive1mx (fun x : R^o => Rz (@Rad.angle_of R (a x)) : 'M[R^o]__) t =
  derive1 a t *: col_mx3 (row3 (- Sin (a t)) (Cos (a t)) 0) (row3 (- Cos (a t)) (- Sin (a t)) 0) 0.
Proof.
move=> Ha.
apply/matrix3P/and9P; split; rewrite !mxE /=.
- rewrite (_ : (fun _ => _) = Cos \o a); last by rewrite funeqE => x; rewrite !mxE.
  rewrite (chain_rule Ha); last exact/derivable_Cos.
  by rewrite derive1_Cos mulrC.
- rewrite (_ : (fun _ => _) = Sin \o a); last by rewrite funeqE => x; rewrite !mxE.
  rewrite (chain_rule Ha); last exact/derivable_Sin.
  by rewrite derive1_Sin mulrC.
- rewrite (_ : (fun _ => _) = \0); last by rewrite funeqE => x; rewrite !mxE.
  by rewrite derive1_cst mulr0.
- rewrite (_ : (fun _ => _) = - Sin \o a); last by rewrite funeqE => x; rewrite !mxE.
  rewrite (_ : - _ \o _ = - (Sin \o a)) // derive1E deriveN; last first.
    apply/derivable1_diffP/differentiable_comp.
    exact/derivable1_diffP.
    exact/derivable1_diffP/derivable_Sin.
  rewrite -derive1E (chain_rule Ha); last exact/derivable_Sin.
  by rewrite derive1_Sin mulrN mulrC.
- rewrite (_ : (fun _ => _) = Cos \o a); last by rewrite funeqE => x; rewrite !mxE.
  rewrite (chain_rule Ha); last exact/derivable_Cos.
  by rewrite derive1_Cos mulrN mulNr mulrC.
- rewrite (_ : (fun _ => _) = \0); last by rewrite funeqE => x; rewrite !mxE.
  by rewrite derive1_cst mulr0.
- rewrite (_ : (fun _ => _) = \0); last by rewrite funeqE => x; rewrite !mxE.
  by rewrite derive1_cst mulr0.
- rewrite (_ : (fun _ => _) = \0); last by rewrite funeqE => x; rewrite !mxE.
  by rewrite derive1_cst mulr0.
- rewrite (_ : (fun _ => _) = cst 1); last by rewrite funeqE => x; rewrite !mxE.
  by rewrite derive1_cst mulr0.
Qed.

(* example 3.1 [sciavicco]*)
(* rotational motion of one degree of freedom manipulator *)
Lemma ang_vel_mx_Rz (R : realType) (a : R^o -> R^o) t : derivable a t 1 ->
  ang_vel_mx (@Rz _ \o (@Rad.angle_of _) \o a) t = \S(row3 0 0 (derive1 a t)).
Proof.
move=> Ha.
rewrite /ang_vel_mx trmx_Rz (derive1mx_RzE Ha) /Rz.
rewrite -!scalerAr -col_mx3_mul.
rewrite mulmx_row3_col3 scale0r addr0.
rewrite mulmx_row3_col3 scale0r addr0.
rewrite e2row mulmx_row3_col3 !(scale0r,scaler0,addr0).
rewrite !row3Z !(cosN,sinN,opprK,mulr0,mulrN,mulNr).
rewrite !row3D mulrC addrC subrr addr0.
rewrite -!expr2 cos2Dsin2 -opprD addrC cos2Dsin2.
by apply/matrix3P; rewrite !spinij !mxE /= !(eqxx,oppr0,mulr0,mulrN1,mulr1).
Qed.

(* see also the end of dh.v *)
Section chain.

Inductive joint (R : rcfType) :=
  Revolute of (R^o -> (*angle*) R) | Prismatic of (R^o -> R).

Definition joint_variable (R : realType) (j : joint [rcfType of R]) : R^o -> R :=
  fun t => match j with Revolute a => (* Rad.f ( *) a t(*) *) | Prismatic a => a t end.

Record chain (R : rcfType) n (* number of joints *) := mkChain {
  joint_of_chain : 'I_n -> joint R ;
  frame_of_chain : 'I_n.+1 -> (R^o -> tframe R) }.

End chain.

Section geometric_jacobian_computation.

Variables (n : nat) (R : realType) (c : chain [rcfType of R^o] n).

Definition prev_frame (i : 'I_n) : 'I_n.+1 := widen_ord (leqnSn n) i.
Definition next_frame (i : 'I_n) : 'I_n.+1 := fintype.lift ord0 i.
Lemma next_frameE i : next_frame i = i.+1 :> nat. Proof. by []. Qed.
Definition last_frame : 'I_n.+1 := ord_max.

Section geo_jac_row.
Variable i : 'I_n.
Let j : joint [rcfType of R^o] := joint_of_chain c i.
Let q : R^o -> R^o := joint_variable j.
Let Fim1 := frame_of_chain c (prev_frame i).
(*Let Fi := frame_of_chain c (next_frame i).*)
Let Fmax := frame_of_chain c last_frame.
(* contribution to the angular velocity *)
Definition geo_jac_ang t : 'rV_3 := if j is Revolute _ then (Fim1 t)~k else 0.
(* contribution to the linear velocity *)
Definition geo_jac_lin t : 'rV_3 :=
  if j is Revolute _ then (Fim1 t)~k *v (\o{Fmax t} - \o{Fim1 t}) else (Fim1 t)~k.
End geo_jac_row.

Definition geo_jac t : 'M_(n, 6) :=
  row_mx (\matrix_(i < n) geo_jac_lin i t) (\matrix_(i < n) geo_jac_ang i t).

End geometric_jacobian_computation.

Require Import scara.

Section scara_geometric_jacobian.
Variable R : realType.

Variable theta1 : R -> angle R.
Variable a1 : R.
Variable theta2 : R -> angle R.
Variable a2 : R.
Variable d3 : R -> R.
Variable theta4 : R -> angle R.
Variable d4 : R.
Let Theta1 : R -> R := @rad R \o theta1.
Let Theta2 : R -> R := @rad R \o theta2.
Let Theta4 : R -> R := @rad R \o theta4.
(* direct kinematics equation written in function of the joint variables,
   from scara.v  *)
Let rot t := scara_rot (theta1 t) (theta2 t) (theta4 t).
Let trans t := scara_trans (theta1 t) a1 (theta2 t) a2 (d3 t) d4.
Definition scara_end_effector t : 'M[R]_4 := hom (rot t) (trans t).

Let scara_lin_vel : R -> 'rV[R]_3 :=
  derive1mx (@trans_of_hom [ringType of R^o] \o scara_end_effector).
Let scara_ang_vel : R -> 'rV[R]_3 :=
  ang_vel (@rot_of_hom [ringType of R^o] \o scara_end_effector).

Definition scara_joints : 'I_4 -> joint R :=
  [eta (fun=> Prismatic 0) with
  0 |-> Revolute Theta1,
  1 |-> Revolute Theta2,
  2%:R |-> Prismatic d3,
  3%:R |-> Revolute Theta4].

Definition scara_joint_variables t : 'rV[R^o]_4 :=
  \row_i (joint_variable (scara_joints i) t).

Let scara_joint_velocities : R -> 'rV[R^o]_4 := derive1mx scara_joint_variables.

(* specification of scara frames *)
Variables scara_frames : 'I_5 -> R -> tframe R.
Let Fim1 (i : 'I_4) := scara_frames (prev_frame i).
Let Fi (i : 'I_4) := scara_frames (next_frame i).
Let Fmax := scara_frames ord_max.
Hypothesis Hzvec : forall t i, (Fim1 i t)~k = 'e_2%:R.
Hypothesis o0E : forall t, \o{Fim1 0 t} = 0.
Hypothesis o1E : forall t, \o{Fim1 1 t} =
  a1 * Cos (Theta1 t) *: 'e_0 + a1 * Sin (Theta1 t) *: 'e_1.
Hypothesis o2E : forall t, \o{Fim1 2%:R t} = \o{Fim1 1 t} +
  (a2 * Cos (Theta1 t + Theta2 t)) *: 'e_0 +
  (a2 * Sin (Theta1 t + Theta2 t)) *: 'e_1.
Hypothesis o3E : forall t, \o{Fim1 3%:R t} = \o{Fim1 2%:R t} + (d3 t) *: 'e_2.
Hypothesis o4E : forall t, \o{Fmax t} = \o{Fim1 3%:R t} + d4 *: 'e_2.

Lemma scale_realType (K : realType) (k1 : K) (k2 : K^o) : k1 *: k2 = k1 * k2.
Proof. by []. Qed.

Import rv3LieAlgebra.Exports.

Lemma scara_geometric_jacobian t :
  derivable (Theta1 : R^o -> R^o) t 1 ->
  derivable (Theta2 : R^o -> R^o) t 1 ->
  derivable (d3 : R^o -> R^o) t 1 ->
  derivable (Theta4 : R^o -> R^o) t 1 ->
  scara_joint_velocities t *m geo_jac (mkChain scara_joints scara_frames) t =
  row_mx (scara_lin_vel t) (scara_ang_vel t).
Proof.
move=> H1 H2 H3 H4.
rewrite /geo_jac; set a := (X in _ *m @row_mx _ _ 3 3 X _).
rewrite (mul_mx_row _ a) {}/a; congr (@row_mx _ _ 3 3 _ _).
- rewrite /scara_lin_vel (_ : @trans_of_hom [rcfType of R] \o _ = trans); last first.
    rewrite funeqE => x /=; exact: trans_of_hom_hom.
  rewrite /trans /scara_trans derive1mxE [RHS]row3_proj /= ![in RHS]mxE [in RHS]/=.
  transitivity (
      derive1 (Theta1 : R^o -> R^o) t *: (Fim1 0 t)~k *v (\o{Fmax t} - \o{Fim1 0 t}) +
      derive1 (Theta2 : R^o -> R^o) t *: (Fim1 1 t)~k *v (\o{Fmax t} - \o{Fim1 1 t}) +
      derive1 (d3 : R^o -> R^o) t *: (Fim1 2 t)~k +
      derive1 (Theta4 : R^o -> R^o) t *: (Fim1 3%:R t)~k *v (\o{Fmax t} - \o{Fim1 3%:R t})).
    rewrite /scara_joint_velocities /scara_joint_variables derive1mxE /geo_jac_lin /=.
    apply/rowP => i; rewrite 3![in RHS]mxE [in LHS]mxE sum4E;
          (repeat apply: f_equal2).
    - by rewrite 2!mxE /= linearZl_LR [in RHS]mxE.
    - by rewrite 2!mxE /= linearZl_LR [in RHS]mxE.
    - by rewrite 2!mxE [in RHS]mxE.
    - by rewrite 2!mxE /= linearZl_LR [in RHS]mxE.
  rewrite o0E subr0.
  rewrite {1}o4E.
  rewrite linearDr /=.
  rewrite (linearZr_LR _ _ _ 'e_2)
   /= {2}Hzvec (linearZl_LR _ _ _ 'e_2) /= liexx 2!{1}scaler0 addr0.
  rewrite (_ : \o{Fmax t} - \o{Fim1 1 t} =
    (a2 * Cos (Theta1 t + Theta2 t) *: 'e_0 +
    (a1 * Sin (Theta1 t) + a2 * Sin (Theta1 t + Theta2 t) - a1 * Sin (Theta1 t)) *: 'e_1 +
    (d3 t + d4) *: 'e_2)); last first.
    rewrite (addrC (a1 * Sin _)) addrK.
    rewrite o4E o3E o2E o1E.
    set a := _ *: 'e_0 + _ *: 'e_1.
    rewrite -3!addrA addrC 3!addrA subrK.
    rewrite addrC -[in RHS]addrA; congr (_ + _).
    by rewrite -addrA -scalerDl.
  rewrite linearDr /=.
  rewrite (linearZr_LR _ _ _ 'e_2) /= (linearZl_LR (crossmul_bilinear _) 'e_2) 
          {2}(Hzvec t 1) /= liexx 2!{1}scaler0 addr0.
  rewrite (addrC (a1 * Sin _)) addrK.
  rewrite (_ : \o{Fmax t} - \o{Fim1 3%:R t} = d4 *: 'e_2%:R); last first.
    by rewrite o4E -addrA addrC subrK.
  rewrite (linearZr_LR _ _ _ 'e_2) /= (linearZl_LR (crossmul_bilinear _) 'e_2)
          {1}(Hzvec t 3%:R) /= liexx 2!scaler0 addr0.
  rewrite o3E.
  rewrite linearDr /= (linearZr_LR _ _ _ 'e_2) (linearZl_LR _ 'e_2) 
          {2}(Hzvec t 0) /= liexx 2!scaler0 addr0.
  rewrite {1}o2E {1}o1E.
  rewrite (_ : (fun _ => _) = 
                (a2 \*: (Cos \o (Theta2 + Theta1) : R^o -> R^o)) + 
                (a1 *: (Cos \o Theta1 : R^o -> R^o))); last first.
    rewrite funeqE => x /=.
    rewrite -[RHS]/(_ x + _ x); congr (_ * _ + _ * _) => /=; last first.
      by rewrite /Theta1 /Cos /= Rad.fK.
    rewrite -[(Theta2 + Theta1) x]/(_ x + _ x).
    rewrite /Theta2 /Theta1 /=.
    admit.
  rewrite (_ : (fun _ => _) = (a2 \*: (Sin \o (Theta2 + Theta1))) + 
                              (a1 *: (Sin \o Theta1))); last first.
    rewrite funeqE => x /=.
    rewrite -[RHS]/(_ x + _ x); congr (_ * _ + _ * _) => /=; last first.
      by rewrite /Theta1 /Sin /= Rad.fK.
    rewrite -[(Theta2 + Theta1) x]/(_ x + _ x).
    rewrite /Theta2 /Theta1 /=.
    admit.
  rewrite row3e2; congr (_ + _ *: _); last first.
  - by rewrite Hzvec.
  - rewrite [in RHS]derive1E [in RHS]deriveD; last 2 first.
      exact: ex_derive.
      exact: H3.
    by rewrite deriveE // diff_cst add0r derive1E.
  - rewrite !linearDr /= !(linearZr_LR (crossmul_bilinear _))
            !(linearZl_LR (crossmul_bilinear _)) /= !Hzvec veckj vecki
            !{1}scalerN.
    rewrite -!addrA addrCA addrC -!addrA (addrCA (- _)) !addrA.
    rewrite -2!addrA [in RHS]addrC; congr (_ + _).
    - rewrite !scalerA -2!scalerDl row3e1; congr (_ *: _).
      rewrite [in RHS]derive1E deriveD; last 2 first.
        apply/derivableZ/derivable_Sin_comp/derivableD; [exact H2 | exact H1].
        exact/derivableZ/derivable_Sin_comp.
      rewrite deriveZ /=; last first.
        apply/derivable_Sin_comp/derivableD; [exact H2 | exact H1].
      rewrite deriveZ /=; last exact/derivable_Sin_comp.
      rewrite -derive1E chain_rule; [|apply: derivableD|exact: derivable_Sin]; last 2 first.
        exact H2.
        exact H1.
      rewrite derive1_Sin.
      rewrite -derive1E chain_rule; [| |exact: derivable_Sin]; last by exact H1.
      rewrite derive1_Sin -addrA addrC; congr (_ + _); last first.
        by rewrite -mulrA.
      rewrite -mulrDr [in RHS]derive1E deriveD; last 2 first.
        exact: H2.
        exact: H1.
      rewrite -mulrA scale_realType; apply: f_equal2; first by [].
      rewrite addrC; apply: f_equal2; first by [].
      by rewrite addrC !derive1E.
    - rewrite !{1}scalerA !addrA -3!{1}scaleNr -2!scalerDl row3e0.
      congr (_ *: _).
      rewrite [in RHS]derive1E deriveD; last 2 first.
        apply/derivableZ/derivable_Cos_comp/derivableD; [exact H2 | exact H1].
        apply/derivableZ/derivable_Cos_comp; exact H1.
      rewrite deriveZ /=; last first.
        apply/derivable_Cos_comp/derivableD.
        exact: H2.
        exact H1.
      rewrite deriveZ /=; last exact/derivable_Cos_comp.
      rewrite -derive1E chain_rule; [|apply: derivableD|exact: derivable_Cos]; last 2 first.
        exact: H2.
        exact: H1.
      rewrite derive1_Cos mulNr scalerN.
      rewrite -derive1E chain_rule; [| | exact: derivable_Cos]; last exact H1.
      rewrite derive1_Cos mulNr scalerN; congr (_ - _); last first.
        by rewrite -mulrA.
      rewrite -opprD; congr (- _).
      rewrite [in RHS]derive1E deriveD; last 2 first.
        exact: H2.
        exact: H1.
      rewrite -mulrDr -!derive1E.
      rewrite addrC (addrC (_^`() _)).
      by rewrite !scalerAl.
- rewrite /scara_ang_vel (_ : @rot_of_hom [ringType of R^o] \o _ = rot); last first.
    rewrite funeqE => x /=; exact: rot_of_hom_hom.
  rewrite /rot /ang_vel /scara_rot.
  rewrite (_ : (fun _ => _) = (@Rz _ \o @Rad.angle_of _ \o (Theta1 + Theta2 + Theta4))); last first.
    rewrite funeqE => x; congr Rz.
    rewrite -[(Theta1 + Theta2 + Theta4) x]/(Theta1 x + Theta2 x + Theta4 x).
    admit.
  rewrite ang_vel_mx_Rz; last first.
    apply derivableD; [apply/derivableD|by []].
    exact: H1.
    exact: H2.
  rewrite [RHS]spinK.
  transitivity (derive1 (Theta1 : R^o -> R^o) t *: (Fim1 0 t)~k +
                derive1 (Theta2 : R^o -> R^o) t *: (Fim1 1 t)~k +
                derive1 (Theta4 : R^o -> R^o) t *: (Fim1 3%:R t)~k).
    rewrite /scara_joint_velocities /scara_joint_variables derive1mxE /geo_jac_ang /=.
    apply/rowP => i; rewrite !mxE sum4E !mxE {1}mulr0 addr0.
    by rewrite -!/(Fim1 _) [Fim1 0 _]lock [Fim1 1 _]lock [Fim1 3%:R _]lock /= -!lock.
  rewrite !Hzvec -2!scalerDl e2row row3Z mulr0 mulr1.
  rewrite [in RHS]derive1E deriveD; [|apply/derivableD|by []]; last 2 first.
    exact: H1.
    exact: H2.
  rewrite deriveD; [| exact: H1| exact H2].
  by rewrite 3!derive1E.
Admitted.

End scara_geometric_jacobian.

Section analytical_jacobian.

Variable n' : nat.
Let n := n'.+1.
Variable (R : realType) (p : 'rV[R^o]_n -> 'rV[R^o]_3).
Let Jp := jacobian p.
Variable (phi : 'rV[R^o]_n -> 'rV[R^o]_3).
Let Jphi := jacobian phi.

Lemma dp (q : R^o -> 'rV[R^o]_n) t :
  derive1mx (p \o q) t = derive1mx q t *m Jp (q t). (* 3.56 *)
Proof.
rewrite /Jp /jacobian mul_rV_lin1.
rewrite /derive1mx.
Abort.

End analytical_jacobian.

(*Section tangent_vectors.

Variable R : realType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.
Implicit Types p : point.

(* tangent vector *)
Record tvec p := TVec {tvec_field :> vector}.
Definition vtvec p (v : tvec p) := let: TVec v := v in v.

Local Notation "p .-vec" := (tvec p) (at level 5).
Local Notation "u :@ p" := (TVec p u) (at level 11).

Definition addt (p : point) (u : p.-vec) (v : vector) : p.-vec :=
  TVec p (tvec_field u + v).

Local Notation "p +@ u" := (addt p u) (at level 41).

End tangent_vectors.

Coercion vtvec_field_coercion := vtvec.

Notation "p .-vec" := (tvec p) (at level 5).
Notation "u :@ p" := (TVec p u) (at level 11).
Notation "p +@ u" := (addt p u) (at level 41).*)
