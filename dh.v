Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp
Require Import complex.
From mathcomp
Require Import finset fingroup perm.

Require Import aux angle euclidean3 skew vec_angle rot frame.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

(* NB: should go to euclidean3.v *)
Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Section TFrame_properties.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := TFrame.t R.

Definition xaxis (f : frame) := mkLine (TFrame.o f) (Frame.i f).
Definition yaxis (f : frame) := mkLine (TFrame.o f) (Frame.j f).
Definition zaxis (f : frame) := mkLine (TFrame.o f) (Frame.k f).

End TFrame_properties.

Module Plucker.
Section plucker.
Variable R : rcfType.
Let vector := 'rV[R]_3.

Record array := mkArray {
  e : vector ;
  n : vector ;
  _ : e *d e == 1 ;
  _ : n *d e == 0 }.

End plucker.
End Plucker.

Coercion plucker_array_mx (R : rcfType) (p : Plucker.array R) :=
  row_mx (Plucker.e p) (Plucker.n p).

(* equation of a line passing through two points p1 p2 *)
Coercion line_pred {R':rcfType} (l : line R') : pred 'rV[R']_3 :=
  let p1 := line_point l in
  [pred p : 'rV[R']_3 |
     (p == p1) ||
     ((line_vector l != 0) && colinear (line_vector l) (p - p1))].

Section line_ext.

Variable R : rcfType.

Lemma line_point_in (l : line R) : line_point l \in (l : pred _).
Proof. by case: l => p v /=; rewrite inE /= eqxx. Qed.

Lemma lineP p (l : line R) :
  reflect (exists k', p = line_point l + k' *: line_vector l)
          (p \in (l : pred _)).
Proof.
apply (iffP idP) => [|].
  rewrite inE.
  case/orP => [/eqP pl|].
    exists 0; by rewrite scale0r addr0.
  case/andP => l0 /colinearP[|].
    rewrite subr_eq0 => /eqP ->.
    exists 0; by rewrite scale0r addr0.
  case=> pl [k [Hk1 Hk2]].
  have k0 : k != 0 by rewrite -normr_eq0 Hk1 mulf_neq0 // ?invr_eq0 norm_eq0.
  exists k^-1.
  by rewrite Hk2 scalerA mulVr ?unitfE // scale1r addrCA subrr addr0.
case=> k' ->.
rewrite inE.
case/boolP : (line_vector l == 0) => [/eqP ->|l0 /=].
  by rewrite scaler0 addr0 eqxx.
by rewrite addrAC subrr add0r colinearvZ colinear_refl 2!orbT.
Qed.

Lemma mem_add_line (l : line R) (p v : 'rV[R]_3) :
  line_vector l != 0 ->
  colinear v (line_vector l) ->
  (p + v \in (l : pred _)) = (p \in (l : pred _)).
Proof.
move=> l0 vl.
apply/lineP/idP => [[] x /eqP|pl].
  rewrite eq_sym -subr_eq => /eqP <-.
  rewrite inE l0 /=; apply/orP; right.
  rewrite -!addrA addrC !addrA subrK colinear_sym.
  by rewrite colinearD // ?colinearZv ?colinear_refl ?orbT // colinearNv.
case/colinearP : vl => [|[_ [k [Hk1 ->]]]]; first by rewrite (negPf l0).
case/lineP : pl => k' ->.
exists (k' + k); by rewrite -addrA -scalerDl.
Qed.

End line_ext.

(* TODO: in progress, [angeles] p.141-142 *)
Section open_chain.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := TFrame.t R.

Record joint := mkJoint {
  joint_vaxis : vector ;
  norm_joint_vaxis : norm joint_vaxis = 1 ;                  
  joint_angle : angle R (* between to successive X axes *) }.

Record link := mkLink {
  link_length : R ; (* nonnegative, distance between to successive joint axes *)
  link_offset : R ; (* between to successive X axes *)
  link_twist : angle R (* or twist angle, between two successive Z axes *) }.
(* NB: link_offset, joint_angle, link_length, link_twist are called 
   Denavit-Hartenberg parameters *)

(*Lemma crossmul_mat (u : 'rV[R]_3) : forall v : 'rV[R]_3,
  u *v v = v *m \S( u ).
Proof. move=> v; by rewrite skew_mxE. Qed.*)

Lemma pluckerP p (l : line R) :
  p \in (l : pred _) ->
  let p1 := line_point l in
  let p2 := line_point2 l in
  p *m (\S( p2 ) - \S( p1 )) + p1 *v (p2 - p1) = 0.
Proof.
rewrite inE => /orP[/eqP -> p1 p2|].
  rewrite -/p1 mulmxBr linearB /= !skew_mxE crossmulvv.
  by rewrite 2!subr0 crossmulC addrC subrr.
case/andP => l0 H p1 p2.
rewrite -/p1 in H.
rewrite /p2 /line_point2 -/p1 addrAC subrr add0r skew_mxD addrAC subrr add0r.
rewrite skew_mxE crossmulC addrC -crossmulBl crossmulC.
rewrite -crossmulvN opprB; by apply/eqP.
Qed.

Definition hPlucker (l : line R) :=
  let p1 := line_point l in
  let p2 := line_point2 l in
  col_mx (\S( p2 ) - \S( p1 )) (p1 *v (p2 - p1)).

Require Import rigid.

Lemma hPluckerP p (l : line R) :
  p \is 'hP[R] ->
  from_h p \in (l : pred _) ->
  let p1 := line_point l in
  let p2 := line_point2 l in
  p *m hPlucker l = 0.
Proof.
move=> hp Hp p1 p2.
move/pluckerP : Hp => /=.
rewrite /hPlucker -/p1 -/p2 => Hp.
move: (hp); rewrite hpoint_from_h => /eqP ->.
by rewrite (mul_row_col (from_h p) 1) mul1mx.
Qed.

Definition plucker_of_line (l : line R) : 'rV[R]_6 :=
  let p1 := line_point l in
  let p2 := line_point2 l in
  row_mx (p2 - p1) (p1 *v (p2 - p1)).

Definition pluckere (l : line R) :=
  let p1 := line_point l in
  let p2 := line_point2 l in
  (norm (p2 - p1))^-1 *: (p2 - p1).

Definition pluckern (l : line R) :=
  let p1 := line_point l in
  p1 *v pluckere l.

Definition nplucker (l : line R) : 'rV[R]_6 := 
  let p1 := line_point l in
  let p2 := line_point2 l in
  row_mx (pluckere l) (pluckern l).

Lemma npluckerP (l : line R) :
  let p1 := line_point l in
  let p2 := line_point2 l in
  line_vector l != 0 ->
  plucker_of_line l = (norm (p2 - p1)) *: nplucker l.
Proof.
move=> p1 p2 l0.
rewrite /nplucker /pluckere /pluckern -/p1 -/p2 crossmulvZ -scale_row_mx scalerA.
by rewrite divrr ?scale1r // unitfE norm_eq0 /p2 /line_point2 -/p1 addrAC subrr add0r.
Qed.

Lemma pluckereP (l : line R) : line_vector l != 0 ->
  let e := pluckere l in e *d e == 1.
Proof.
move=> l0 /=.
rewrite /pluckere dotmulZv dotmulvZ dotmulvv.
rewrite /line_point2 addrAC subrr add0r.
rewrite mulrA mulrAC expr2 mulrA mulVr ?unitfE ?norm_eq0 // mul1r.
by rewrite divrr // unitfE norm_eq0.
Qed.

Lemma pluckernP (l : line R) : pluckern l *d pluckere l == 0.
Proof.
rewrite /pluckern /pluckere /line_point2 addrAC subrr add0r crossmulvZ.
by rewrite dotmulvZ dotmulZv -dotmul_crossmulA crossmulvv dotmulv0 2!mulr0.
Qed.

Lemma plucker_of_lineE (l : line R) (l0 : line_vector l != 0) :
  (norm (line_point2 l - line_point l))^-1 *: plucker_of_line l =
  Plucker.mkArray (pluckereP l0) (pluckernP l).
Proof.
rewrite /plucker_of_line /plucker_array_mx /=.
by rewrite /pluckern /pluckere crossmulvZ -scale_row_mx.
Qed.

Definition is_interpoint (p : point) (l1 l2 : line R) :=
  (p \in (l1 : pred _)) && (p \in (l2 : pred _)).

Definition interpoint_param x (l1 l2 : line R) :=
  let p1 := line_point l1 in let p2 := line_point l2 in
  let v1 := line_vector l1 in let v2 := line_vector l2 in
  \det (col_mx3 (p2 - p1) x (v1 *v v2)) / norm (v1 *v v2) ^+ 2. 

Definition interpoint_s (l1 l2 : line R) := interpoint_param (line_vector l1) l1 l2.

Definition interpoint_t (l1 l2 : line R) := interpoint_param (line_vector l2) l1 l2.

Lemma interpointP p l1 l2 : ~~ parallel l1 l2 ->
  let p1 := line_point l1 in let p2 := line_point l2 in
  let v1 := line_vector l1 in let v2 := line_vector l2 in
  is_interpoint p l1 l2 <->
  let s := interpoint_s l1 l2 in let t := interpoint_t l1 l2 in
  p1 + t *: v1 = p /\ p2 + s *: v2 = p.
Proof.
move=> l1l2 p1 p2 v1 v2; split; last first.
  move=> [Hs Ht]; rewrite /is_interpoint; apply/andP; split; apply/lineP;
  by [exists (interpoint_t l1 l2) | exists (interpoint_s l1 l2)].
case/andP => /lineP[t' Hs] /lineP[s' Ht] s t.
have Ht' : t' = interpoint_t l1 l2.
  have : t' *: (v1 *v v2) = (p2 - p1) *v v2.
    move: (Ht); rewrite Hs -/p1 -/p2 -/v1 -/v2 => /(congr1 (fun x => x - p1)).
    rewrite addrAC subrr add0r addrAC => /(congr1 (fun x => x *v v2)).
    by rewrite crossmulZv crossmulDl crossmulZv crossmulvv scaler0 addr0.
  move/(congr1 (fun x => x *d (v1 *v v2))).
  rewrite dotmulZv dotmulvv.
  move/(congr1 (fun x => x / (norm (v1 *v v2)) ^+ 2)).
  rewrite -mulrA divrr ?mulr1; last by rewrite unitfE sqrf_eq0 norm_eq0.
  by rewrite -dotmul_crossmulA crossmul_triple.
have Hs' : s' = interpoint_s l1 l2.
  have : s' *: (v1 *v v2) = (p2 - p1) *v v1.
    move: (Ht); rewrite Hs -/p1 -/p2 -/v1 -/v2 => /(congr1 (fun x => x - p2)).
    rewrite [in X in _ = X -> _]addrAC subrr add0r addrAC => /(congr1 (fun x => x *v v1)).
    rewrite [in X in _ = X -> _]crossmulZv crossmulDl crossmulZv crossmulvv scaler0 addr0.
    rewrite -(opprB p2 p1) (crossmulC v2) scalerN => /eqP.
    by rewrite crossmulNv eqr_opp => /eqP.
  move/(congr1 (fun x => x *d (v1 *v v2))).
  rewrite dotmulZv dotmulvv.
  move/(congr1 (fun x => x / (norm (v1 *v v2)) ^+ 2)).
  rewrite -mulrA divrr ?mulr1; last by rewrite unitfE sqrf_eq0 norm_eq0.
  by rewrite -dotmul_crossmulA crossmul_triple.
by rewrite /t /s -Ht' -Hs'.
Qed.

Definition intersection (l1 l2 : line R) : option point := 
  if ~~ intersects l1 l2 then
    None
  else
    Some (line_point l1 + interpoint_t l1 l2 *: line_vector l1).
  
Axiom directed_from_to : 'rV[R]_3 -> 'rV[R]_3 -> 'rV[R]_3 -> bool.

Axiom angle_between_lines : 'rV[R]_3 -> 'rV[R]_3 -> 'rV[R]_3 -> angle R.

Variable n' : nat.
Let n := n'.+1.

(* 1. Zi is the axis of the ith joint *)
Definition Z_joint_axis (joints : joint ^ n) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in 
  (joint_vaxis (joints i) == Frame.k (frames i')) ||
  (joint_vaxis (joints i) == - Frame.k (frames i')).

(* 2. Xi is the common perpendicular to Zi-1 and Zi *)
Definition X_Z (frames : frame ^ n.+1) (i : 'I_n) : bool :=
  let i' := widen_ord (leqnSn _) i in 
  let predi : 'I_n.+1 := inord i.-1 in 
  let: (o_predi, z_predi) := let f := frames predi in (TFrame.o f, Frame.k f) in
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, Frame.i f, Frame.k f) in
  if intersects (zaxis (frames predi)) (zaxis (frames i')) then
    x_i == z_predi *v z_i 
  else if colinear z_predi z_i then
    o_predi \in (xaxis (frames i') : pred _)
  else
    (x_i _|_ z_predi, z_i) && (* Xi is the common perpendicular to Zi-1 and Zi *)
    (directed_from_to x_i z_i z_predi) (* xi is directed from zi-1 to zi *).

(*Definition common_normal_xz (i : 'I_n) :=
  (framej (frames i.-1)) _|_ (framek (frames i)), (framei (frames i.-1)).*)
(* x_vec (frames i.-1) _|_ plane (z_vec (frames i.-1)),(z_vec (frames i)) *)

(* 3. distance Zi-1<->Zi = link length *)
Definition link_lengthP (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  link_length (links i') = distance_between_lines (zaxis (frames i')) (zaxis (frames succi)).

Definition link_offsetP (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=  
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (o_succi, x_succi) := let f := frames succi in (TFrame.o f, Frame.i f) in 
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, Frame.i f, Frame.k f) in 
  if intersection (zaxis (frames i')) (xaxis (frames succi)) is some o'_i then
    (norm (o'_i - o_i)(*the Zi-coordiante of o'_i*) == link_offset (links i')) &&
    (`| link_offset (links i') | == distance_between_lines (xaxis (frames i')) (xaxis (frames succi)))
  else
    false (* should not happen since Zi always intersects Xi.+1 (see condidion 2.) *).

Definition link_twistP (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=  
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (x_succi, z_succi) := let f := frames succi in (Frame.i f, Frame.k f) in 
  let z_i := Frame.k (frames i') in 
  link_twist (links i') == angle_between_lines z_i z_succi x_succi.
  (*angle measured about the positive direction of Xi+1*)

Definition joint_angleP (joints : joint ^ n) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: x_succi := Frame.i (frames succi) in 
  let: (x_i, z_i) := let f := frames i' in (Frame.i f, Frame.i f) in 
  joint_angle (joints i) = angle_between_lines x_i x_succi z_i.
  (*angle measured about the positive direction of Zi*)

(* n + 1 links numbered 0,..., n (at least two links: the manipulator base and the end-effector)
   n joints
     the ith joint couples the i-1th and the ith link
   n + 1 frames numbered F_1, F_2, ..., F_n+1 (F_i attached to link i-1)
   *)
Record chain := mkChain {
  links : {ffun 'I_n.+1 -> link} ;
  frames : {ffun 'I_n.+1 -> frame} ;
  joints : {ffun 'I_n -> joint} ;
  (* the six conditions [angeles] p.141-142 *)
  _ : forall i, Z_joint_axis joints frames i ;
  _ : forall i, X_Z frames i ;
  _ : forall i, link_lengthP links frames i ;
  _ : forall i, link_offsetP links frames i ;
  _ : forall i, link_twistP links frames i ;
  _ : forall i, joint_angleP joints frames i 
  (* this leaves the n.+1th frame unspecified (on purpose) *)
  }.

(*
Variables chain : {ffun 'I_n -> frame * link * joint}.
Definition frames := fun i => (chain (insubd ord0 i)).1.1.
Definition links := fun i => (chain (insubd ord0 i)).1.2.
Definition joints := fun i => (chain (insubd ord0 i)).2.
*)

(*
Definition before_after_joint (i : 'I_n) : option (link * link):=
  match ltnP O i with
    | LtnNotGeq H (* 0 < i*) => Some (links i.-1, links i)
    | GeqNotLtn H (* i <= 0*) => None
  end.
 *)

End open_chain.
