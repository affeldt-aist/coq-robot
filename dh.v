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

Definition same_direction (u v : 'rV[R]_3) : bool := 0 <= cos (vec_angle u v).

(* equation of a line passing through two points p1 p2 *)
Coercion line_pred {R':rcfType} (l : line R') : pred 'rV[R']_3 :=
  let p1 := line_point l in
  [pred p : 'rV[R']_3 | 
     (p == p1) ||
     ((line_vector l != 0) && colinear (line_vector l) (p - p1))].

(*Definition intersection (o o' : 'rV[R]_3) (v v' : 'rV[R]_3) : option 'rV[R]_3.
Admitted.*)
(* http://math.stackexchange.com/questions/270767/find-intersection-of-two-3d-lines *)
Definition intersection (l1 l2 : line R) : option point :=
  let: (p1, u1) := (line_point l1, line_vector l1) in
  let: (p2, u2) := (line_point l2, line_vector l2) in
  if p1 \in (l2 : pred _) then Some p1
  else if p2 \in (l1 : pred _) then Some p2
  else let w : vector := p2 - p1 in
  let hw := u2 *v w in
  let h1 := u2 *v u1 in
  if (hw == 0) || (h1 == 0) then
    None
  else
    let k := (norm hw / norm h1) *: u1 in
    if same_direction (u2 *v w) (u2 *v u1) then
      Some (p1 + k)
    else 
      Some (p1 - k).

Lemma line_point_in (l : line R) : line_point l \in (l : pred _).
Proof. 
by case: l => p v /=; rewrite inE /= eqxx.
Qed.

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

Lemma law_of_sinuses (v1 v2 : vector) (p1 p2 : point) p :
  intersection (mkLine p1 v1) (mkLine p2 v2) = Some p ->
  norm (p - p1) * sin (vec_angle v1 v2) =
  norm (p2 - p1) * sin (vec_angle (p2 - p1) v2).
Proof.
rewrite /intersection /=.
case: ifPn.
  rewrite inE /=.
  case/orP => [/eqP -> [->]|/andP[v20 Hv2] [<-]].
    by rewrite subrr norm0 [in RHS]mul0r mul0r.
  rewrite subrr norm0 [in LHS]mul0r.
  case/boolP : (p2 - p1 == 0) => p12; first by rewrite (eqP p12) norm0 mul0r.
  apply/esym/eqP.
  by rewrite mulf_eq0 -colinear_sin // -colinearNv opprB colinear_sym Hv2 orbT.
rewrite inE /= negb_or => /andP[p1p2].
rewrite negb_and negbK => /orP[/eqP ->|].
  rewrite !crossmul0v.
  case: ifPn.
    rewrite inE /= eq_sym (negbTE p1p2) /= => /andP[v10 v1p2p1] [<-].
    case/boolP : (p2 - p1 == 0) => p12. 
      by rewrite (eqP p12) norm0 [in LHS]mul0r mul0r.
    by rewrite 2!vec_angle0.
  rewrite eqxx /= => _ ?; exfalso; done.
move=> v2p1p2.
case: ifPn.
  rewrite inE /= eq_sym (negbTE p1p2) /= => /andP[v10 v1p2p1] [<-].
  case/colinearP : v1p2p1.
    rewrite subr_eq0 eq_sym (negbTE p1p2) => ?; exfalso; done.
  case=> p2p10 [k [Hk1 Hk2]].
  rewrite Hk2.
  case/boolP : (k == 0) => k0.
    exfalso.
    apply/negP : k0.
    apply: contra v10.
    rewrite Hk2 => /eqP ->; by rewrite scale0r.
  move: k0.
  rewrite eqr_le negb_and -2!ltrNge => /orP[] k0.
    by rewrite [in LHS]vec_angleC (vec_angleZ _ _ k0) [in LHS]vec_angleC.
  rewrite [in LHS]vec_angleC (vec_angleZ_neg _ _ k0).
  rewrite [in LHS]vec_angleC [in LHS]sin_vec_angleN //.
  by rewrite -/(colinear (p2 - p1) v2) -colinearNv opprB colinear_sym.
rewrite inE /= negb_or => /andP[_].
rewrite negb_and negbK => /orP[/eqP ->|].
  rewrite crossmulv0 eqxx orbT => ?; exfalso; done.
move=> v1p2p1.
case: ifPn.
  move=> _ abs; exfalso; done.
rewrite negb_or => /andP[v2p2p1 v2v1].
have v10 : v1 != 0.
  apply: contra v2v1 => /eqP ->; by rewrite crossmulv0.
have v20 : v2 != 0.
  apply: contra v2v1 => /eqP ->; by rewrite crossmul0v.
case: ifPn => H [<-].
  rewrite -addrA addrCA subrr addr0.
  rewrite normZ ger0_norm; last by rewrite divr_ge0 // norm_ge0.
  rewrite norm_crossmul (mulrC (norm v2)) -!mulrA; congr (_ * _).
  have sin0 : sin (vec_angle v2 v1) != 0 by rewrite -colinear_sin.
  rewrite norm_crossmul -(mulrA (norm v2)) invrM; last 2 first.
    by rewrite unitfE norm_eq0.
    by rewrite unitfE mulf_neq0 // ?norm_eq0 // normr_eq0.
  rewrite (mulrC _ (norm v2)^-1) !mulrA (mulrC _ (norm v2)^-1) mulrA mulVr; last first.
    by rewrite unitfE norm_eq0.
  rewrite mul1r invrM; last 2 first.
    by rewrite unitfE norm_eq0.
    by rewrite unitfE normr_eq0.
  rewrite -!mulrA (mulrA (norm v1)^-1) mulVr ?mul1r; last first.
    by rewrite unitfE norm_eq0.
  move: sin0.
  rewrite eqr_le negb_and -!ltrNge => /orP[]sin0.
    rewrite mulrC.
    rewrite [in X in X * _ = _](gtr0_norm sin0).
    rewrite (vec_angleC v1 v2) mulVr ?mul1r ?unitfE ?gtr_eqF //.
    rewrite vec_angleC.
    admit.
  rewrite mulrC.
  rewrite [in X in X * _ = _](ltr0_norm sin0).
  rewrite (vec_angleC v1 v2) invrN mulNr mulVr ?mul1r ?unitfE ?ltr_eqF // mulN1r.
  admit.
admit.
Admitted.

Lemma intersectionP l1 l2 p : line_vector l1 != 0 -> line_vector l2 != 0 ->
  intersection l1 l2 = Some p ->
  (p \in (l1 : pred _)) && (p \in (l2 : pred _)).
Proof.
move=> l10 l20 H.
move: (H).
rewrite /intersection.
case: ifPn => [l12 [<-]|l12].
  apply/andP; split; [exact: line_point_in|exact l12].
case: ifPn => [l21 [<-]|l21].
  apply/andP; split; [exact l21|exact: line_point_in].
case: ifPn => [//|].
rewrite negb_or => /andP[H1 H2].
case: ifPn => samedir [<-].
  set k := _ / norm (_ *v _).
  have k_gt0 : 0 < k.
    by rewrite /k divr_gt0 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
  apply/andP; split; first by apply/lineP; exists k.
  rewrite inE l20 /=.
  apply/orP; right.
  move/law_of_sinuses in H.
  admit.
Admitted.

Definition angle_between_lines (u1 u2 w(* direction *) : vector) : angle R :=
  if same_direction w (u1 *v u2) then
    vec_angle u1 u2
  else 
    vec_angle u2 u1.

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
    (same_direction x_i (z_i - z_predi)) (* xi is directed from zi-1 to zi *). 

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
