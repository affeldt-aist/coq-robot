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

(*Definition intersection (o o' : 'rV[R]_3) (v v' : 'rV[R]_3) : option 'rV[R]_3.
Admitted.*)
(* http://math.stackexchange.com/questions/270767/find-intersection-of-two-3d-lines *)

Definition same_direction (u v : 'rV[R]_3) := 0 <= cos (vec_angle u v).

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
    if same_direction hw h1 then
      Some (p1 + k)
    else 
      Some (p1 - k).

Lemma law_of_sinuses (p1 p2 p : point) :
  let v1 := p - p1 in
  let v2 := p2 - p in
  norm v1 * sin (vec_angle v1 v2) =
  norm (p2 - p1) * sin (vec_angle (p2 - p1) v2).
Proof.
move=> v1 v2.
case/boolP : (v1 == 0) => [|v10].
  rewrite /v1 subr_eq0 => /eqP <-.
  case/boolP : (v2 == 0) => [|v20].
    by rewrite /v2 subr_eq0 => /eqP ->.
  by rewrite subrr norm0 vec_angle0 [in RHS]vec_anglevv // sin0 mulr0 mul0r.
case/boolP : (v2 == 0) => [|v20].
  by rewrite /v2 subr_eq0 => /eqP ->.
case/boolP : (p2 - p1 == 0) => [|p1p20].
  rewrite /v1 /v2 subr_eq0 => /eqP ->.
  rewrite subrr norm0 mul0r -{2}opprB sin_vec_angleNv vec_anglevv ?sin0 ?mulr0 //.
  by rewrite subr_eq0 eq_sym -subr_eq0.
set p1H : 'rV[R]_3 := normalcomp v1 v2.
set pH : 'rV[R]_3 := axialcomp v1 v2.
move: (decomp v1 v2) => v1v2.
have H1 : sin (vec_angle v1 v2) = norm p1H / norm v1.
  case/boolP : (v1 *d v2 == 0) => v1v20.
    have Htmp : v1 *v v2 != 0 by apply dotmul_eq0_crossmul_neq0.
    rewrite /sin /vec_angle expi_arg; last first.
      by rewrite (eqP v1v20) eq_complex /= eqxx /= norm_eq0.
    rewrite /= (eqP v1v20) !(mul0r,oppr0,add0r,expr0n,addr0,mulr0).
    rewrite [Num.sqrt (norm (v1 *v v2) ^+ 2) ^+ 2]sqr_sqrtr ?sqr_ge0 //.
    rewrite sqrtr_sqr ger0_norm ?norm_ge0 // mulrA -expr2 divrr ?unitfE ?sqrf_eq0 ?norm_eq0 //.
    rewrite (_ : norm p1H = norm v1) ?divrr ?unitfE ?norm_eq0 //.
    rewrite v1v2 axialcompE.
    rewrite (mx11_scalar (v1 *m v2^T)).
    by rewrite -/(v1 *d v2) (eqP v1v20) mul_scalar_mx scale0r add0r.
  suff H : sin (vec_angle v1 v2) ^+ 2 == (norm p1H ^+ 2 / norm v1 ^+ 2).
    apply/eqP.
    rewrite -(@eqr_expn2 _ 2) // ?sin_vec_angle_ge0 ?oppr_eq0 ?divr_ge0 ?norm_ge0 //.
    by rewrite expr_div_n.
  suff H : norm v1 ^+ 2 * sin (vec_angle v1 v2) ^+ 2 = norm p1H ^+ 2.
    by rewrite -H -mulrA (mulrCA (norm v1 ^+ 2)) divrr ?mulr1 // unitfE sqrf_eq0 norm_eq0.
  rewrite /p1H.
  rewrite /normalcomp.
Abort.

Definition normalcomp_new (v u : 'rV[R]_3) := v - normalize u *d v *: normalize u.

Definition axialcomp_new (v u : 'rV[R]_3) := normalize u *d v *: normalize u.

Lemma decomp_new v u : v = axialcomp_new v u + normalcomp_new v u.
Proof. by rewrite /axialcomp_new /normalcomp_new addrC subrK. Qed.

Lemma normalcomp0v (v : 'rV[R]_3) : normalcomp_new 0 v = 0.
Proof. by rewrite /normalcomp_new dotmulv0 scale0r subrr. Qed.

Lemma normalcompv0 (v : 'rV[R]_3) : normalcomp_new v 0 = v.
Proof. by rewrite /normalcomp_new /normalize scaler0 dotmul0v scaler0 subr0. Qed.

Lemma colinear_axialcomp e p : colinear e (axialcomp_new p e).
Proof. apply/eqP; by rewrite /axialcomp_new linearZ /= crossmulvZ crossmulvv 2!scaler0. Qed.

Lemma colinearD (u v w : 'rV[R]_3) : colinear u w -> colinear v w ->
  colinear (u + v) w.
Proof.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite addr0.
case/colinearP => [/eqP -> _| [w0 [k [Hk1 Hk2]]]]; first by rewrite colinear_sym colinear0.
case/colinearP => [/eqP ->|[_ [k' [Hk'1 Hk'2]]]]; first by rewrite colinear_sym colinear0.
by rewrite Hk2 Hk'2 -scalerDl colinearZv colinear_refl orbT.
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

Lemma law_of_sinuses_helper (p1 p2 p : point) :
  let v1 := p - p1 in
  let v2 := p2 - p in
  v2 != 0 ->
  norm v1 ^+ 2 * sin (vec_angle v1 v2) ^+ 2 = norm (normalcomp_new v1 v2) ^+ 2.
Proof.
move=> v1 v2 v20.
case/boolP : (v1 == 0) => [/eqP ->|v10].
  by rewrite normalcomp0v norm0 expr0n mul0r.
rewrite /normalcomp_new.
rewrite [in RHS]normB.
case/boolP : (0 < normalize v2 *d v1) => [v2v1|].
  rewrite normZ gtr0_norm // norm_normalize // mulr1 scalerA vec_anglevZ //; last first.
    by rewrite divr_gt0 // norm_gt0.
  rewrite dotmul_cos norm_normalize // mul1r vec_angleZv; last first.
    by rewrite invr_gt0 norm_gt0.
  rewrite [in RHS]mulrA (vec_angleC v1) -expr2 -mulrA -expr2 exprMn.
  by rewrite mulr2n opprD addrA subrK sin2cos2 mulrBr mulr1.
rewrite -lerNgt ler_eqVlt => /orP[|v2v1].
  rewrite {1}dotmul_cos norm_normalize // mul1r mulf_eq0 norm_eq0 (negbTE v10) /=.
  rewrite vec_angleZv; last by rewrite invr_gt0 norm_gt0.
  move/eqP=> Hcos.
  rewrite dotmulZv (_ : _ *d _ = 0); last by rewrite dotmul_cos Hcos mulr0.
  rewrite mulr0 scale0r norm0 mulr0 mul0r expr0n mul0rn addr0 subr0.
  by rewrite -(sqr_normr (sin _)) vec_angleC cos0sin1 ?expr1n ?mulr1.
rewrite vec_anglevZN // cos_vec_anglevN // ?normalize_eq0 //.
rewrite scalerA normZ ltr0_norm; last first.
  rewrite mulr_lt0 invr_eq0 norm_eq0 v20 /= ltr_eqF //=.
  by rewrite invr_lt0 (ltrNge (norm v2)) norm_ge0 addbF.
rewrite mulNr -(mulrA _ _ (norm v2)) mulVr ?mulr1 ?unitfE ?norm_eq0 //.
rewrite vec_anglevZ // ?invr_gt0 ?norm_gt0 // sqrrN mulrN mulNr mulrN opprK.
rewrite dotmul_cos norm_normalize // mul1r vec_angleZv ?invr_gt0 ?norm_gt0 //.
rewrite (vec_angleC v2) mulrA -expr2 exprMn.
rewrite addrAC -addrA -mulrA -mulrnAr -mulrBr.
rewrite -{2}(mulr1 (norm v1 ^+ 2)) -mulrDr; congr (_ * _).
by rewrite sin2cos2 -expr2 mulr2n opprD !addrA addrK.
Qed.

Lemma law_of_sinuses (p1 p2 p : point) :
  let v1 := p - p1 in
  let v2 := p2 - p in
  v1 != 0 ->
  v2 != 0 ->
  sin (vec_angle v1 v2) = norm (normalcomp_new v1 v2) / norm v1.
Proof.
move=> v1 v2 v10 v20.
apply/eqP.
rewrite -(@eqr_expn2 _ 2) // ?divr_ge0 // ?norm_ge0 // ?sin_vec_angle_ge0 //.
rewrite exprMn -law_of_sinuses_helper // mulrAC exprVn divrr ?mul1r //.
by rewrite unitfE sqrf_eq0 norm_eq0.
Qed.

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
  set p1 := line_point l1.
  set p2 := line_point l2.
  set v1 := line_vector l1.
  set v2 := line_vector l2.
  set k := _ / norm (_ *v _).
  have k_gt0 : 0 < k.
    by rewrite /k divr_gt0 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
  apply/andP; split; first by apply/lineP; exists k.

  rewrite (decomp_new v1 v2).
  rewrite scalerDr addrA.
  rewrite addrAC mem_add_line //; last first.
    by rewrite -/v2 colinearZv colinear_sym colinear_axialcomp orbT.

  rewrite inE.
  rewrite /k.
  rewrite norm_crossmul ger0_norm ?sin_vec_angle_ge0 //; last first.
    rewrite subr_eq add0r; apply: contra l21 => /eqP.
    by rewrite -/p2 => ->; rewrite inE eqxx.
  rewrite norm_crossmul ger0_norm ?sin_vec_angle_ge0 //.
  rewrite -(mulrA (norm v2) (norm v1)) invrM; last 2 first.
    by rewrite ?unitfE norm_eq0.
    rewrite unitfE.
    move: H2.
    rewrite -norm_eq0.
    rewrite norm_crossmul -/v1 -/v2 ger0_norm ?sin_vec_angle_ge0 //.
    by rewrite -mulrA mulf_eq0 norm_eq0 (negbTE l20) /=.
  rewrite (mulrC (_^-1)).
  rewrite mulrCA !mulrA mulVr ?mul1r ?unitfE ?norm_eq0 //.
Admitted.

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
