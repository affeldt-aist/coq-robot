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

Require Import aux angle euclidean3 skew vec_angle frame.

(* OUTLINE:
  1. section two_dimensional_rotation
  2. section elementary_rotations
     Rx, Ry, Rz
  3. section isRot_definition.
     definition of rotations w.r.t. a vector
     properties of rotations
     sample lemmas:
       all rotations around a vector of angle a have trace "1 + 2 * cos a"
       equivalence SO[R]_3 <-> Rot
  4. section axial_vector
     definition of the axial vector 
     proof that this vector is stable by rotation (like the vector of Rot)
  5. section exponential_map_rot
     specialized exponential map
     sample lemmas: 
       inverse of the exponential map,
       exponential map of a skew matrix is a rotation
     Rodrigues formula: 
       u * e^(phi,w) can be expressed using a lin. comb. of vectors u, (u *d w)w, u *v w)
  6. Module Aa (angle-axis representation)
     section angle_of_angle_axis_representation
     section vector_axis_of_angle_axis_representation
     section angle_axis_of_rot
       sample lemmas:
         a rotation matrix has angle_aa M and normalize (vaxis_aa M) for exp. coor.
  7. section angle_axis_representation
  8. section euler_angles
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Section two_dimensional_rotation.

Variable R : rcfType.
Implicit Types a b : angle R.
Implicit Types M : 'M[R]_2.
  
Definition RO a := col_mx2 (row2 (cos a) (sin a)) (row2 (- sin a) (cos a)).

Lemma tr_RO a : \tr (RO a) = (cos a) *+ 2.
 Proof. by rewrite /mxtrace sum2E !mxE /= mulr2n. Qed.

Lemma orthogonal2P M :
  (row 0 M *d row 0 M = 1) -> (row 0 M *d row 1 M = 0) ->
  (row 1 M *d row 0 M = 0) -> (row 1 M *d row 1 M = 1) ->
  M \is 'O[R]_2.
Proof.
move=> H *; apply/orthogonalP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> //|]; by rewrite ifnot01 => /eqP ->.
rewrite ifnot01 => /eqP ->; case/boolP : (j == 0) => [/eqP -> //|].
by rewrite ifnot01 => /eqP ->; rewrite eqxx.
Qed.

Lemma RO_is_O a : RO a \is 'O[R]_2.
Proof.
by apply/orthogonal2P; rewrite dotmulE sum2E !mxE /= -?expr2 ?sqrrN ?cos2Dsin2 //
   ?(mulrC (cos a)) ?mulNr addrC ?subrr // ?cos2Dsin2.
Qed.

Lemma RO_is_SO a : RO a \is 'SO[R]_2.
Proof.
by rewrite rotationE RO_is_O /= det_mx22 !mxE /= mulrN opprK -!expr2 cos2Dsin2.
Qed.

Lemma rot2d_helper M a b : a - b = - pihalf R ->
  M = col_mx2 (row2 (cos a) (sin a)) (row2 (cos b) (sin b)) ->
  { a0 | M = RO a0}.
Proof.
move=> abpi.
have -> : sin b = cos a.
  by move/eqP : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC cosBpihalf.
have -> : cos b = - sin a.
  by move/eqP : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC sinBpihalf opprK.
move=> ->; by exists a.
Qed.

Lemma rot2d M : M \is 'SO[R]_2 -> {a | M = RO a}.
Proof.
move=> MSO.
move: (MSO); rewrite rotationE => /andP[MO _].
case: (norm1_cossin (norm_row_of_O MO 0)); rewrite !mxE => a [a1 a2].
case: (norm1_cossin (norm_row_of_O MO 1)); rewrite !mxE => b [b1 b2].
move/orthogonalP : (MO) => /(_ 0 1) /=.
rewrite dotmulE sum2E !mxE a1 a2 b1 b2 -cosB.
case/cos0_inv => [abpi|].
  exfalso.
  move/rotation_det : MSO.
  rewrite det_mx22 a1 a2 b1 b2 mulrC -(mulrC (cos b)) -sinB => /esym/eqP.
  by rewrite -eqr_opp -sinN opprB abpi sin_pihalf Neqxx oner_eq0.
move/(@rot2d_helper M a b); apply.
by rewrite -a1 -a2 -b1 -b2 [in LHS](col_mx2_rowE M) 2!row2_of_row.
Qed.

Definition RO' a := col_mx2 (row2 (cos a) (sin a)) (row2 (sin a) (- cos a)).

Lemma rot2d_helper' M a b : a - b = pihalf R ->
  M = col_mx2 (row2 (cos a) (sin a)) (row2 (cos b) (sin b)) ->
  {a0 | M = RO' a0}.
Proof.
move=> /eqP abpi.
have -> : sin b = - cos a.
  by move: (abpi); rewrite subr_eq => /eqP ->; rewrite addrC cosDpihalf opprK.
have -> : cos b = sin a.
  by move : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC sinDpihalf.
move=> ->; by exists a.
Qed.

Lemma rot2d' M : M \is 'O[R]_2 -> { a : angle R & {M = RO a} + {M = RO' a} }.
Proof.
move=> MO.
case: (norm1_cossin (norm_row_of_O MO 0)); rewrite !mxE => a [a1 a2].
case: (norm1_cossin (norm_row_of_O MO 1)); rewrite !mxE => b [b1 b2].
move/orthogonalP : (MO) => /(_ 0 1) /=.
rewrite dotmulE sum2E !mxE a1 a2 b1 b2 -cosB.
have HM : M = col_mx2 (row2 (cos a) (sin a)) (row2 (cos b) (sin b)).
  by rewrite -a1 -a2 -b1 -b2 [in LHS](col_mx2_rowE M) 2!row2_of_row.
case/cos0_inv => [|abpi].
  case/(@rot2d_helper' M)/(_ HM) => a0.
  exists a0; by right.
case: (rot2d_helper abpi HM) => a0 KM.
exists a0; by left.
Qed.

Lemma tr_SO2 M : M \is 'SO[R]_2 -> `|\tr M| <= 2%:R.
Proof.
case/rot2d => a PRO; move: (cos_max a) => ca.
rewrite PRO tr_RO -(mulr_natr (cos a)) normrM normr_nat.
by rewrite -[in X in _ <= X]mulr_natr ler_pmul.
Qed.

End two_dimensional_rotation.

Section elementary_rotations.

Variable R : rcfType.
Implicit Types a : angle R.

Definition Rx a := col_mx3
  'e_0
  (row3 0 (cos a) (sin a))
  (row3 0 (- sin a) (cos a)).

Lemma Rx0 : Rx 0 = 1.
Proof. by rewrite /Rx cos0 sin0 oppr0; apply/matrix3P; rewrite !mxE. Qed.

Lemma Rxpi : Rx pi = diag_mx (row3 1 (-1) (-1)).
Proof. 
rewrite /Rx cospi sinpi oppr0; apply/matrix3P; by rewrite !mxE /= -?mulNrn ?mulr1n ?mulr0n.
Qed.

Lemma Rx_RO a : Rx a = block_mx (1 : 'M_1) (0 : 'M_(1, 2)) 0 (RO a).
Proof.
rewrite -(@submxK _ 1 2 1 2 (Rx a)).
rewrite (_ : ulsubmx _ = 1); last first.
  apply/rowP => i; by rewrite (ord1 i) !mxE /=.
rewrite (_ : ursubmx _ = 0); last first.
  by apply/rowP => i; rewrite !mxE. (*; case: ifPn => //; by case: ifPn.*)
rewrite (_ : dlsubmx _ = 0); last first.
  apply/colP => i; rewrite !mxE /=.
  case: ifPn; first by rewrite !mxE.
  by case: ifPn; rewrite !mxE.
rewrite (_ : drsubmx _ = RO a) //; by apply/matrix2P; rewrite !mxE.
Qed.

Lemma Rx_is_SO a : Rx a \is 'SO[R]_3.
Proof.
(* TODO: pove using RO_is_SO? *)
apply matrix_is_rotation.
- apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
  rewrite -dotmulvv dotmulE sum3E !mxE /=. by Simp.r.
- apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
- rewrite -dotmulvv dotmulE sum3E !mxE /=. Simp.r. by rewrite -!expr2 cos2Dsin2.
- rewrite 2!rowK /= dotmulE sum3E !mxE /=. by Simp.r.
- rewrite 3!rowK /= crossmulE !mxE /=. by Simp.r.
Qed.

Lemma mxtrace_Rx a : \tr (Rx a) = 1 + cos a *+ 2.
Proof. by rewrite /Rx /mxtrace sum3E !mxE /= -addrA -mulr2n. Qed.

Lemma inv_Rx a : (Rx a)^-1 = Rx (- a).
Proof.
move/rotation_inv : (Rx_is_SO a) => ->.
rewrite /Rx cosN sinN opprK.
by apply/matrix3P; rewrite !mxE.
Qed.

Definition Rx' a := col_mx3
  'e_0
  (row3 0 (cos a) (sin a))
  (row3 0 (sin a) (- cos a)).

Lemma det_Rx' a : \det (Rx' a) = -1.
Proof.
rewrite det_mx33 !mxE /=. Simp.r. by rewrite -!expr2 -opprD cos2Dsin2.
Qed.

Definition Ry a := col_mx3
  (row3 (cos a) 0 (- sin a))
  'e_1
  (row3 (sin a) 0 (cos a)).

Definition Rz a := col_mx3
  (row3 (cos a) (sin a) 0)
  (row3 (- sin a) (cos a) 0)
  'e_2%:R.

Lemma RzM a b : Rz a * Rz b = Rz (a + b).
Proof.
rewrite {1 2}/Rz e2row -mulmxE !mulmx_col3 !mulmx_row3_col3. Simp.r.
rewrite !row3Z !row3D. Simp.r. rewrite -e2row; congr col_mx3.
- by rewrite -cosD sinD (addrC (_ * _)).
- by rewrite -opprD -sinD [in X in row3 _ X _]addrC -cosD.
Qed.

Lemma Rz_is_SO a : Rz a \is 'SO[R]_3.
Proof.
apply matrix_is_rotation.
- apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
  by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 addr0 -2!expr2 cos2Dsin2.
- apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
- by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 addr0 mulrN mulNr opprK addrC cos2Dsin2.
- by rewrite 2!rowK /= dotmulE sum3E !mxE /= mulrN mulr0 addr0 addrC mulrC subrr.
- rewrite 3!rowK /= crossmulE !mxE /=. Simp.r. by rewrite -!expr2 cos2Dsin2 e2row.
Qed.

Lemma RzE a : Rz a = (frame_of_SO (Rz_is_SO a)) _R^ (can_frame R).
Proof. rewrite FromTo_to_can; by apply/matrix3P; rewrite !mxE. Qed.

Lemma to_coord_Rz_e0 a :
  to_coord (can_frame R) (Vec (frame_of_SO (Rz_is_SO a)) 'e_0) = Vec _ (row 0 (Rz a)).
Proof. by rewrite to_coordE_to_can rowE [in RHS]RzE FromTo_to_can. Qed.

End elementary_rotations.

Section isRot_definition.

Variable R : rcfType.
Implicit Types a : angle R.

Definition isRot (a : angle R)
  (u : 'rV[R]_3)
  (f : {linear 'rV_3 -> 'rV_3}) : bool :=
  let: j := Base.j u in let: k := Base.k u in
  [&& f u == u,
      f j == cos a *: j + sin a *: k &
      f k == - sin a *: j + cos a *: k].

Lemma isRotP a u (f : {linear 'rV_3 -> 'rV_3}) : reflect
  (let: j := Base.j u in let: k := Base.k u in
  [/\ f u = u, f j = cos a *: j + sin a *: k & f k = - sin a *: j + cos a *: k])
  (isRot a u f).
Proof.
apply: (iffP idP); first by case/and3P => /eqP ? /eqP ? /eqP ?.
by case => H1 H2 H3; apply/and3P; rewrite H1 H2 H3.
Qed.

Section properties_of_isRot.

Variable u : 'rV[R]_3.
Implicit Types M N : 'M[R]_3.

Lemma isRot_axis a M : isRot a u (mx_lin1 M) -> u *m M = u.
Proof. by case/isRotP. Qed.

Lemma isRot1 : isRot 0 u (mx_lin1 1).
Proof.
apply/isRotP; split => /=; first by rewrite mulmx1.
by rewrite cos0 sin0 mulmx1 scale0r addr0 scale1r.
by rewrite mulmx1 sin0 cos0 scaleNr scale0r oppr0 add0r scale1r.
Qed.

Lemma isRotpi (u1 : norm u = 1) : isRot pi u (mx_lin1 (u^T *m u *+ 2 - 1)).
Proof.
apply/isRotP; split => /=.
- by rewrite mulmxBr mulmx1 mulr2n mulmxDr mulmxA dotmul1 // ?mul1mx addrK.
- rewrite cospi sinpi scale0r addr0 scaleN1r mulmxBr mulmx1.
  by rewrite mulmxDr mulmxA Base.j_tr_mul // 2!add0r.
- rewrite sinpi oppr0 scale0r add0r cospi scaleN1r mulmxBr mulmx1.
  by rewrite mulr2n mulmxDr mulmxA Base.k_tr_mul // 2!add0r.
Qed.

Lemma isRotD a b M N : isRot a u (mx_lin1 M) -> isRot b u (mx_lin1 N) ->
  isRot (a + b) u (mx_lin1 (M * N)).
Proof.
move=> /isRotP[/= H1 H2 H3] /isRotP[/= K1 K2 K3]; apply/isRotP; split => /=.
- by rewrite mulmxA H1 K1.
- rewrite mulmxA H2 mulmxDl cosD sinD -2!scalemxAl K2 K3 2!scalerDr addrACA.
  by rewrite !scalerA mulrN -2!scalerDl (addrC (cos a * sin b)).
- rewrite mulmxA H3 mulmxDl -2!scalemxAl K2 K3 2!scalerDr !scalerA sinD cosD.
  rewrite addrACA mulrN -2!scalerDl -opprB mulNr opprK (addrC (- _ * _)) mulNr.
  by rewrite (addrC (cos a * sin b)).
Qed.

Lemma isRotN a M : isRot (- a) u (mx_lin1 M) -> isRot a (- u) (mx_lin1 M).
Proof.
move=> /isRotP[/= H1 H2 H3]; apply/isRotP; split => /=.
by rewrite mulNmx H1.
by rewrite Base.jN H2 cosN sinN Base.kN scalerN scaleNr.
by rewrite Base.kN Base.jN mulNmx H3 sinN opprK cosN scalerN opprD scaleNr.
Qed.

Lemma isRotZ a f k (u0 : u != 0) (k0 : 0 < k) :
  isRot a (k *: u) f = isRot a u f.
Proof.
rewrite /isRot !(Base.jZ u0 k0) !(Base.kZ u0 k0) linearZ; congr andb.
apply/idP/idP => [/eqP/scalerI ->//|/eqP ->//]; by move/gtr_eqF : k0 => /negbT.
Qed.

Lemma isRotZN a f k (u0 : u != 0) (k0 : k < 0):
  isRot a (k *: u) (mx_lin1 f) = isRot (- a) u (mx_lin1 f).
Proof.
rewrite /isRot /= sinN cosN opprK (Base.jZN u0 k0) (Base.kZN u0 k0).
rewrite !scalerN !scaleNr mulNmx eqr_oppLR opprD !opprK -scalemxAl; congr andb.
apply/idP/idP => [/eqP/scalerI ->//|/eqP ->//]; by move/ltr_eqF : k0 => /negbT.
Qed.

Lemma mxtrace_isRot a M (u0 : u != 0) :
  isRot a u (mx_lin1 M) -> \tr M = 1 + cos a *+ 2.
Proof.
case/isRotP=> /= Hu [Hj Hk].
move: (@basis_change _ M (Base.frame u0) (Rx a)).
set i := NOFrame.i _.
set j := NOFrame.j _.
set k := NOFrame.k _.
rewrite !mxE /= !scale1r !scale0r !add0r !addr0.
have H3 : Base.j u = j.
  by rewrite /j /NOFrame.j rowK /=.
have H2 : Base.k u = k.
  by rewrite /k /NOFrame.k rowK /=.
have H1 : i *m M = i.
  by rewrite /i /NOFrame.i rowK /= /Base.i -scalemxAl Hu.
rewrite -H2 -H3.
move/(_ H1 Hj Hk) => ->.
rewrite mxtrace_mulC mulmxA mulmxV ?mul1mx ?mxtrace_Rx //.
rewrite unitmxE unitfE rotation_det ?oner_neq0 //.
rewrite /i /NOFrame.i rowK /=.

(* TODO: move *)
Lemma Base_is_frame (u0 : u != 0) : col_mx3 (Base.i u) (Base.j u) (Base.k u) \is 'SO[R]_3.
Proof.
move=> [:X].
apply matrix_is_rotation; rewrite !rowK //=.
abstract: X; by rewrite /Base.i norm_normalize.
by rewrite /Base.j Base1.normj.
by rewrite /Base.k Base1.idotj.
Qed.

exact: Base_is_frame.
Qed.

Lemma Frame_iE (u0 : u != 0) : Frame.i (Base.frame u0) = NOFrame.i (Base.frame u0).
Proof. done. Qed.

Lemma Frame_jE (u0 : u != 0) : Frame.j (Base.frame u0) = NOFrame.j (Base.frame u0).
Proof. done. Qed.

Lemma Frame_kE (u0 : u != 0) : Frame.k (Base.frame u0) = NOFrame.k (Base.frame u0).
Proof. done. Qed.

Lemma same_isRot M N v k (u0 : u != 0) (k0 : 0 < k) a :
  u = k *: v ->
  isRot a u (mx_lin1 M) -> isRot a v (mx_lin1 N) ->
  M = N.
Proof.
move=> mkp /isRotP[/= HMi HMj HMk] /isRotP[/= HNi HNj HNk].
apply/eqP/mulmxP => w.
rewrite (orthogonal_expansion (Base.frame u0) w) !mulmxDl.
rewrite -Frame_iE -Frame_jE -Frame_kE -Base.iE -Base.jE -Base.kE.
rewrite -!scalemxAl.
have v0 : v != 0 by apply: contra u0; rewrite mkp => /eqP ->; rewrite scaler0.
congr (_ *: _ + _ *: _ + _ *: _).
- congr (_ *: _).
  by rewrite HMi {1}mkp -HNi scalemxAl -mkp.
- by rewrite HMj /= mkp (Base.jZ v0 k0) (Base.kZ v0 k0) -HNj.
- by rewrite HMk /= mkp (Base.jZ v0 k0) (Base.kZ v0 k0) -HNk.
Qed.

Lemma isRot_0_inv (u0 : u != 0) M : isRot 0 u (mx_lin1 M) -> M = 1.
Proof.
move=> H; move/(same_isRot u0 ltr01 _ H) : isRot1; apply; by rewrite scale1r.
Qed.

Lemma isRot_tr a (u0 : u != 0) M : M \in unitmx ->
  isRot (- a) u (mx_lin1 M) -> isRot a u (mx_lin1 M^-1).
Proof.
move=> Hf /isRotP[/= H1 H2 H3].
have K1 : normalize u *m M = normalize u by rewrite /normalize -scalemxAl H1.
move: (@basis_change _ M (Base.frame u0) (Rx (- a))).
rewrite -Frame_iE -Frame_jE -Frame_kE -Base.iE -Base.jE -Base.kE.
rewrite !mxE /= K1 !scale0r 2!add0r !addr0 -H2 -H3 scale1r => /(_ erefl erefl erefl).
move=> fRx.
have HfRx : M^-1 = (col_mx3 (normalize u) (Base.j u) (Base.k u))^T *m
   (Rx (- a))^-1 *m col_mx3 (normalize u) (Base.j u) (Base.k u).
  rewrite fRx invrM /= ?(noframe_is_unit (Base.frame u0)) //; last first.
    rewrite unitrMl ?unitrV ?(noframe_is_unit (Base.frame u0)) //.
    by rewrite orthogonal_unit // rotation_sub // Rx_is_SO.
  rewrite invrM; last 2 first.
    by rewrite unitrV (noframe_is_unit (Base.frame u0)).
    by rewrite orthogonal_unit // rotation_sub // Rx_is_SO.
  by rewrite invrK (rotation_inv (frame_is_rot (Base.frame u0))) mulmxE mulrA.
apply/isRotP; split => /=.
- by rewrite -{1}H1 -mulmxA mulmxV // mulmx1.
- rewrite HfRx !mulmxA.
  rewrite (_ : Base.j u *m _ = 'e_1); last first.
    rewrite col_mx3_mul dotmulC /normalize dotmulZv (Base.udotj u0) mulr0 dotmulvv.
    rewrite Base.jE.
    rewrite (NOFrame.normj (Base.frame u0)) // expr1n.
    by rewrite Base.kE (NOFrame.jdotk (Base.frame u0)) e1row.
  rewrite (_ : 'e_1 *m _ = row3 0 (cos (- a)) (sin a)); last first.
    rewrite (rotation_inv (Rx_is_SO (- a))) /Rx col_mx3_mul.
    rewrite dote2 /= 2!dotmulE 2!sum3E !mxE /= cosN sinN opprK. by Simp.r.
  by rewrite mulmx_row3_col3 scale0r add0r cosN.
- rewrite HfRx !mulmxA.
  rewrite (_ : Base.k u *m _ = 'e_2%:R); last first.
    rewrite col_mx3_mul dotmulC /normalize dotmulZv (Base.udotk u0) mulr0 dotmulC.
    by rewrite Base.jE Base.kE (NOFrame.jdotk (Base.frame u0)) dotmulvv (NOFrame.normk (Base.frame u0)) // expr1n e2row.
  rewrite (_ : 'e_2%:R *m _ = row3 0 (- sin a) (cos a)); last first.
    rewrite (rotation_inv (Rx_is_SO (- a))) /Rx col_mx3_mul.
    rewrite dote2 /= 2!dotmulE 2!sum3E !mxE /= cosN sinN opprK. by Simp.r.
  by rewrite mulmx_row3_col3 scale0r add0r.
Qed.

Lemma isRot_SO a f (u0 : u != 0) : isRot a u f -> lin1_mx f \is 'SO[R]_3.
Proof.
move/isRotP=> [Hu Hj Hk].
move: (@basis_change _ (lin1_mx f) (Base.frame u0) (Rx a)).
rewrite !mxE /= !(scale1r,scale0r,add0r,addr0) 3!mul_rV_lin1.
rewrite -Frame_iE -Frame_jE -Frame_kE -Base.iE -Base.jE -Base.kE.
rewrite linearZ Hu => /(_ erefl).
rewrite -/(Base.j _) -/(Base.k _) => /(_ Hj Hk) ->.
move=> [:abs].
rewrite rpredM //; last first.
  abstract: abs.
  exact: (frame_is_rot (Base.frame u0)).
by rewrite rpredM // ?Rx_is_SO // rotation_inv // rotationV.
Qed.

End properties_of_isRot.

Section relation_with_rotation_matrices.

Lemma SO_isRot M : M \is 'SO[R]_3 ->
  exists a, isRot a (vaxis_euler M) (mx_lin1 M).
Proof.
move=> MSO.
set e := vaxis_euler M.
case/boolP : (M == 1) => [/eqP ->|M1]; first by exists 0; exact: isRot1.
have v0 := vaxis_euler_neq0 MSO.
rewrite -/e in v0.
have vMv := vaxis_eulerP MSO.
rewrite -/e in vMv.
set f := Base.frame v0. set i := Base.i e. set j := Base.j e. set k := Base.k e.
have iv : i = normalize e by rewrite /i /Base.i.
have iMi : i *m M = i.
  by rewrite iv /normalize -scalemxAl vMv.
have iMj : i *d (j *m M) = 0.
  rewrite -iMi (proj2 (orth_preserves_dotmul M) (rotation_sub MSO) i j).
  rewrite /i /j Base.iE Base.jE.
  by rewrite (NOFrame.idotj f).
have iMk : i *d (k *m M) = 0.
  rewrite -iMi (proj2 (orth_preserves_dotmul M) (rotation_sub MSO) i k).
  rewrite /i /k Base.iE Base.kE.
  by rewrite (NOFrame.idotk f).
set a := (j *m M) *d j.
set b := (j *m M) *d k.
have ab : j *m M = a *: j + b *: k.
  rewrite {1}(orthogonal_expansion f (j *m M)). -/j -/k dotmulC iMj scale0r add0r.
set c := (k *m M) *d j.
set d := (k *m M) *d k.
have cd : k *m M = c *: j + d *: k.
  by rewrite {1}(orthogonal_expansion f (k *m M)) -/j -/k dotmulC iMk scale0r add0r.
have H1 : a ^+ 2 + b ^+ 2 = 1.
  move: (NOFrame.normj f) => /eqP.
  rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n -dotmulvv -/j.
  rewrite -(proj2 (orth_preserves_dotmul M) (rotation_sub MSO) j j) ab.
  rewrite dotmulDr 2!dotmulDl 4!dotmulvZ 4!dotmulZv 2!dotmulvv.
  rewrite (NOFrame.normj f) // (NOFrame.normk f) // !(expr1n,mulr1) -!expr2.
  by rewrite dotmulC (NOFrame.jdotk f) !(mulr0,add0r,addr0) => /eqP.
have H2 : a * c + b * d = 0.
  move: (NOFrame.jdotk f).
  rewrite -/j -/k -(proj2 (orth_preserves_dotmul M) (rotation_sub MSO) j k) ab cd.
  rewrite dotmulDr 2!dotmulDl 4!dotmulvZ 4!dotmulZv 2!dotmulvv.
  rewrite (NOFrame.normk f) // (NOFrame.normj f) //.
  by rewrite expr1n !mulr1 dotmulC (NOFrame.jdotk f) 4!mulr0 add0r addr0 mulrC (mulrC d).
have H3 : c ^+ 2 + d ^+ 2 = 1.
  move: (NOFrame.normk f) => /eqP.
  rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n -dotmulvv -/j.
  rewrite -(proj2 (orth_preserves_dotmul M) (rotation_sub MSO) k k) cd.
  rewrite dotmulDr 2!dotmulDl 4!dotmulvZ 4!dotmulZv 2!dotmulvv.
  rewrite (NOFrame.normj f) // (NOFrame.normk f) //.
  by rewrite expr1n 2!mulr1 -2!expr2 dotmulC (NOFrame.jdotk f) !(mulr0,addr0,add0r) => /eqP.
set P := col_mx2 (row2 a b) (row2 c d).
have PO : P \is 'O[R]_2.
  apply/orthogonal2P.
  by rewrite rowK /= dotmulE sum2E !mxE /= -2!expr2.
  by rewrite rowK /= dotmulE sum2E !mxE.
  by rewrite 2!rowK /= dotmulE sum2E !mxE /= mulrC (mulrC d).
  by rewrite dotmulE sum2E !mxE /= -!expr2.
case: (rot2d' PO) => phi [phiRO | phiRO']; subst P.
- case/eq_col_mx2 : phiRO => Ha Hb Hc Hd.
  exists phi.
  rewrite -(@isRotZ _ phi (mx_lin1 M) 1 _ _) // scale1r; apply/isRotP; split => //.
  by rewrite -!(Ha,Hb,Hc).
  by rewrite -!(Hb,Hc,Hd).
- exfalso.
  case/eq_col_mx2 : phiRO' => Ha Hb Hc Hd.
  move: (@basis_change _ M f (Rx' phi)).
  rewrite !mxE /= !(addr0,add0r,scale0r,scale1r) -/i -/j -/k.
  rewrite -{1}Ha -{1}Hb -{1}Hc -{1}Hd.
  rewrite -ab iMi -cd => /(_ erefl erefl erefl) => HM.
  move: (rotation_det MSO).
  rewrite HM 2!det_mulmx det_Rx' detV -crossmul_triple.
  rewrite -/(NOFrame.sgn f) (Frame.P f) invr1 mulr1 mul1r => /eqP.
  by rewrite Neqxx oner_eq0.
Qed.

End relation_with_rotation_matrices.

End isRot_definition.

Section axial_vector.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition axial_vec (M : 'M[R]_3) : 'rV[R]_3 :=
  row3 (M 1 2%:R - M 2%:R 1) (M 2%:R 0 - M 0 2%:R) (M 0 1 - M 1 0).

Lemma tr_axial_vec M : axial_vec M^T = - axial_vec M.
Proof. by rewrite /axial_vec !mxE row3N 3!opprB. Qed.

Lemma skew_axial_vec M : \S( axial_vec M ) = M - M^T.
Proof.
by apply/matrix3P; rewrite ?skewii ![in RHS]mxE ?subrr // skewij !mxE /= ?opprB.
Qed.

Lemma axial_vecE M : axial_vec M = unskew (M - M^T).
Proof. by rewrite -(skew_axial_vec M) skew_mxK. Qed.

Lemma axial_vecD (A B : 'M[R]_3) : axial_vec (A + B) = axial_vec A + axial_vec B.
Proof. by rewrite axial_vecE linearD /= opprD addrACA 2!axial_vecE unskewD. Qed.

Lemma axial_vec_sym M : (M \is sym 3 R) = (axial_vec M == 0).
Proof.
apply/idP/idP => [|/eqP H]; rewrite symE.
  move/eqP => HM; by rewrite /axial_vec {2 4 6}HM !mxE !subrr row30.
by rewrite -subr_eq0 -skew_axial_vec H skew_mx0.
Qed.

Lemma axial_vecZ k (M : 'M[R]_3) : axial_vec (k *: M) = k *: axial_vec M.
Proof. by rewrite /axial_vec !mxE -!mulrBr row3Z. Qed.

Lemma axial_vecP (M : 'M[R]_3) u : u *v axial_vec M = u *m antip M.
Proof.
rewrite /antip.
rewrite crossmulC.
rewrite -skew_mxE.
rewrite axial_vecE.
rewrite unskewK.
Abort.

Lemma is_eigenvector1_colinear r (Hr : r \is 'SO[R]_3) n :
  (n <= eigenspace r 1)%MS -> colinear n (axial_vec r).
Proof.
move=> Hn.
have HnT : n *m r^T = n.
  move/eigenspace_trmx : Hn => /(_ (rotation_sub Hr))/eigenspaceP.
  by rewrite scale1r.
set Q := r^T - r.
have nrrT : n *m Q = 0.
 rewrite mulmxDr [in LHS]mulmxN HnT.
 move/eigenspaceP : Hn; rewrite scale1r => ->.
 by rewrite subrr.
have skewrrT : \S( - axial_vec r ) = Q.
  rewrite axial_vecE // -scaleN1r skew_mxZ scaleN1r unskewK ?opprB //.
  by rewrite antiE linearD /= linearN /= trmxK opprB.
move/eqP: nrrT.
by rewrite -skewrrT skew_mxE crossmulC crossmulvN opprK.
Qed.

Lemma axial_vec_vec_eigenspace M : M \is 'SO[R]_3 ->
  (axial_vec M <= eigenspace M 1)%MS.
Proof.
move=> MSO; apply/eigenspaceP; rewrite scale1r.
case: (euler MSO) => u /andP[u0 /eqP uMu].
have /is_eigenvector1_colinear : (u <= eigenspace M 1)%MS.
  by apply/eigenspaceP; rewrite scale1r.
move/(_ MSO) => uax.
suff [k Hk] : exists k, axial_vec M = k *: u by rewrite Hk -scalemxAl uMu.
case/colinearP : uax => [/eqP ->| [_ [k [? ukv]]]].
  exists 0; by rewrite scale0r.
exists (1 / k); rewrite ukv scalerA div1r mulVr ?scale1r // unitfE.
apply: contra u0; rewrite ukv => /eqP ->; by rewrite scale0r.
Qed.

(* NB: useful? *)
Lemma isRot_axial_vec M : M \is 'SO[R]_3 ->
  forall u a, isRot a u (mx_lin1 M) -> colinear u (axial_vec M).
Proof.
move=> MSO u a /isRotP[/= H1 ? ?]; apply is_eigenvector1_colinear => //.
apply/eigenspaceP; by rewrite H1 scale1r.
Qed.

End axial_vector.

Section exponential_map_rot.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Type u v : vector.
Implicit Type a b : angle R.

Definition emx3 a (M : 'M[R]_3) : 'M_3 :=
  1 + sin a *: M + (1 - cos a) *: M ^+ 2.

Local Notation "'`e(' a ',' M ')'" := (emx3 a M) (format "'`e(' a ','  M ')'").

Lemma emx3a0 a : `e(a, 0) = 1.
Proof. by rewrite /emx3 expr0n /= 2!scaler0 2!addr0. Qed.

Lemma emx30M (M : 'M[R]_3) : `e(0, M) = 1.
Proof. by rewrite /emx3 sin0 cos0 subrr 2!scale0r 2!addr0. Qed.

Lemma emx3M a b M : M ^+ 3 = - M -> `e(a, M) * `e(b, M) = `e(a + b, M).
Proof.
move=> cube_u.
rewrite /emx3 sinD cosD !mulrDr !mulrDl.
Simp.r => /=.
rewrite -scalerCA -2!scalerAl -expr2.
rewrite -scalerAl -scalerAr -exprSr cube_u (scalerN (sin b) M) (scalerN (1 - cos a)).
rewrite -(scalerAl (sin a)) -(scalerCA (1 - cos b) M) -(scalerAl (1 - cos b)) -exprS.
rewrite cube_u (scalerN _ M) (scalerN (sin a) (_ *: _)).
rewrite -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA.
rewrite addrC scalerA (mulrC (sin b)) -!addrA.
rewrite [in RHS]addrC [in RHS]scalerBl [in RHS]scalerBl [in RHS]opprB [in RHS]addrCA -![in RHS]addrA; congr (_ + _).
rewrite scalerBl scale1r opprB (scalerA (cos a)) -!addrA.
rewrite [in RHS]scalerDl ![in RHS]addrA [in RHS]addrC -[in RHS]addrA; congr (_ + _).
rewrite addrC ![in LHS]addrA addrK.
rewrite -![in LHS]addrA addrC scalerBl scale1r scalerBr opprB scalerA -![in LHS]addrA.
rewrite [in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite addrCA ![in LHS]addrA subrK -scalerCA -2!scalerAl -exprD.
rewrite (_ : M ^+ 4 = - M ^+ 2); last by rewrite exprS cube_u mulrN -expr2.
rewrite 2!scalerN scalerA.
rewrite addrC -scaleNr -2!scalerDl -scalerBl; congr (_ *: _).
rewrite -!addrA; congr (_ + _).
rewrite mulrBr mulr1 mulrBl mul1r opprB opprB !addrA subrK addrC.
rewrite -(addrC (cos a)) !addrA -(addrC (cos a)) subrr add0r.
by rewrite addrC addrA subrr add0r mulrC.
Qed.

Lemma tr_emx3 a M : `e(a, M)^T = `e(a, M^T).
Proof.
by rewrite /emx3 !linearD /= !linearZ /= trmx1 expr2 trmx_mul expr2.
Qed.

Lemma inv_emx3 a M : M ^+ 4 = - M ^+ 2 -> `e(a, M) * `e(a, - M) = 1.
Proof.
move=> aM.
case/boolP : (cos a == 1) => [/eqP|] ca; rewrite /emx3.
  rewrite ca subrr (_ : sin a = 0) ; last by rewrite cos1sin0 // ca normr1.
  by rewrite !scale0r !addr0 mulr1.
rewrite !mulrDr !mulrDl !mulr1 !mul1r -[RHS]addr0 -!addrA; congr (_ + _).
rewrite !addrA sqrrN -!addrA (addrCA (_ *: M ^+ 2)) !addrA scalerN subrr add0r.
rewrite (_ : (1 - _) *: _ * _ = - (sin a *: M * ((1 - cos a) *: M ^+ 2))); last first.
  rewrite mulrN; congr (- _).
  by rewrite -2!scalerAr -!scalerAl -exprS -exprSr 2!scalerA mulrC.
rewrite -!addrA (addrCA (- (sin a *: _ * _))) !addrA subrK.
rewrite mulrN -scalerAr -scalerAl -expr2 scalerA -expr2.
rewrite -[in X in _ - _ + _ + X = _]scalerAr -scalerAl -exprD scalerA -expr2.
rewrite -scalerBl -scalerDl sin2cos2.
rewrite -{2}(expr1n _ 2) subr_sqr -{1 3}(mulr1 (1 - cos a)) -mulrBr -mulrDr.
rewrite opprD addrA subrr add0r -(addrC 1) -expr2 -scalerDr.
apply/eqP; rewrite scaler_eq0 sqrf_eq0 subr_eq0 eq_sym (negbTE ca) /=.
by rewrite aM subrr.
Qed.

Local Notation "'`e^(' a ',' w ')'" := (emx3 a \S( w )) (format "'`e^(' a ','  w ')'").

Lemma eskew_v0 a : `e^(a, 0) = 1.
Proof. by rewrite skew_mx0 emx3a0. Qed.

Lemma unskew_eskew a w : unskew `e^(a, w) = (sin a) *: w.
Proof.
rewrite /emx3 !(unskewD,unskewZ,skew_mx2,unskewN,skew_mxK,unskew_cst,scaler0,add0r,subr0).
by rewrite unskew_sym ?scaler0 ?addr0 // mul_tr_vec_sym.
Qed.

Lemma tr_eskew a w : `e^(a, w)^T = `e^(a, - w).
Proof. by rewrite tr_emx3 tr_skew /emx3 skew_mxN. Qed.

Lemma eskewM a b (w : 'rV[R]_3) : norm w = 1 ->
  `e^(a, w) * `e^(b, w) = `e^(a + b, w).
Proof. move=> w1; by rewrite emx3M // skew_mx3 w1 expr1n scaleN1r. Qed.

Lemma trace_eskew a u : norm u = 1 -> \tr `e^(a, u) = 1 + 2%:R * cos a.
Proof.
move=> w1.
rewrite 2!mxtraceD !mxtraceZ /= mxtrace1.
rewrite (trace_anti (anti_skew _)) mulr0 addr0 mxtrace_skew_mx2 w1.
rewrite (_ : - _ = - 2%:R); last by rewrite expr1n mulr1.
by rewrite mulrDl addrA mul1r -natrB // mulrC mulrN -mulNr opprK.
Qed.

(* table 1.1 of [springer] 
   'equivalent rotation matrices for various representations of orientation'
   angle-axis angle a, vector u *)
Definition angle_axis_rot a u :=
  let va := 1 - cos a in let ca := cos a in let sa := sin a in
  col_mx3
  (row3 (u``_0 ^+2 * va + ca)
        (u``_0 * u``_1 * va + u``_2%:R * sa)
        (u``_0 * u``_2%:R * va - u``_1 * sa))
  (row3 (u``_0 * u``_1 * va - u``_2%:R * sa)
        (u``_1 ^+2 * va + ca)
        (u``_1 * u``_2%:R * va + u``_0 * sa))
  (row3 (u``_0 * u``_2%:R * va + u``_1 * sa)
        (u``_1 * u``_2%:R * va - u``_0 * sa)
        (u``_2%:R ^+2 * va + ca)).

Lemma eskewE a u : norm u = 1 ->
  let va := 1 - cos a in let ca := cos a in let sa := sin a in
  `e^(a, u) = angle_axis_rot a u.
Proof.
move=> w1 va ca sa; apply/matrix3P.
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  rewrite skew_mx2' !mxE /=.
  rewrite (_ : - _ - _ = u``_0 ^+ 2 - 1); last first.
    rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
  by rewrite !opprD !addrA subrr add0r addrC.
- rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
  by rewrite /va opprB addrC subrK.
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  by rewrite skew_mx2' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  by rewrite skew_mx2' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  by rewrite skew_mx2' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  rewrite skew_mx2' !mxE /=.
  rewrite (_ : - _ - _ = u``_1 ^+ 2 - 1); last first.
    rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
    by rewrite 2!opprD addrCA addrA subrK addrC.
  rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
  by rewrite /va opprB addrC subrK.
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  by rewrite skew_mx2' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  by rewrite skew_mx2' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  by rewrite skew_mx2' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; Simp.r => /=.
  rewrite skew_mx2' !mxE /=.
  rewrite (_ : - _ - _ = u``_2%:R ^+ 2 - 1); last first.
    rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
    by rewrite 2!opprD [in RHS]addrC subrK addrC.
  rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
  by rewrite /va opprB addrC subrK.
Qed.

Lemma eskew_is_O a u : norm u = 1 -> `e^(a, u) \is 'O[R]_3.
Proof.
move=> u1.
by rewrite orthogonalE tr_emx3 tr_skew inv_emx3 // skew_mx4 u1 expr1n scaleN1r.
Qed.

Lemma rank_eskew a w : norm w = 1 -> \rank `e^(a, w) = 3.
Proof.
move=> w1; by rewrite mxrank_unit // orthogonal_unit // eskew_is_O.
Qed.

Lemma det_eskew a w : norm w = 1 -> \det `e^(a, w) = 1.
Proof.
move=> w1.
move/orthogonal_det/eqP : (eskew_is_O (half_angle a) w1).
rewrite -(@eqr_expn2 _ 2) // expr1n sqr_normr expr2 -det_mulmx.
rewrite mulmxE emx3M; last by rewrite skew_mx3 w1 expr1n scaleN1r.
move/eqP; by rewrite halfP.
Qed.

Lemma eskew_is_SO a w : norm w = 1 -> `e^(a, w) \is 'SO[R]_3.
Proof. by move=> w1; rewrite rotationE eskew_is_O //= det_eskew. Qed.

Definition eskew_eigenvalues a : seq R[i] := [:: 1; expi a; expi (- a)].

Lemma eigenvalue_ekew a w : norm w = 1 ->
  eigenvalue (map_mx (fun x => x%:C%C) `e^(a, w)) =1
    [pred k | k \in eskew_eigenvalues a].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly.
Abort.

Lemma Rz_eskew a : Rz a = `e^(a, 'e_2%:R).
Proof.
rewrite /Rz eskewE /angle_axis_rot ?norm_delta_mx //.
rewrite !mxE /= expr0n /=. Simp.r.
by rewrite expr1n mul1r subrK -e2row.
Qed.

(* the w vector of e(phi,w) is an axis *)
Lemma axial_vec_eskew a w : axial_vec `e^(a, w) = sin a *+ 2 *: w.
Proof.
rewrite axial_vecE unskewD unskew_eskew tr_eskew unskewN unskew_eskew scalerN.
by rewrite opprK -mulr2n scalerMnl.
Qed.

Section rodrigues_formula.

Definition rodrigues_gen (u : vector) a w :=
  u - (1 - cos a) *: (norm w ^+ 2 *: u) + (1 - cos a) * (u *d w) *: w + sin a *: (w *v u).

Lemma rodrigues_genP u a w : rodrigues_gen u a w = u *m `e^(a, w).
Proof.
rewrite /rodrigues_gen.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE -!addrA; congr (_ + _).
rewrite !addrA.
rewrite [in X in _ = _ + X]crossmulC scalerN.
rewrite [in X in _ = _ - X]crossmulC.
rewrite double_crossmul dotmulvv.
rewrite scalerN opprK.
rewrite scalerBr [in RHS]addrA [in RHS]addrC -!addrA; congr (_ + (_ + _)).
by rewrite dotmulC scalerA. 
Qed.

Definition rodrigues u a w :=
  cos a *: u + (1 - cos a) * (u *d w) *: w + sin a *: (w *v u).

Lemma rodriguesP u a w : norm w = 1 -> rodrigues u a w = u *m `e^(a, w).
Proof.
move=> w1; rewrite -(rodrigues_genP u a w).
rewrite /rodrigues_gen /rodrigues w1 expr1n scale1r; congr (_ + _ + _).
by rewrite scalerBl opprB scale1r addrCA addrA addrK.
Qed.

End rodrigues_formula.

Lemma isRot_eskew a w : w != 0 -> isRot a w (mx_lin1 `e^(a, normalize w)).
Proof.
move=> w0.
pose f := Base.frame w0.
apply/isRotP; split => /=.
- rewrite -rodrigues_genP // /rodrigues_gen (norm_normalize w0) expr1n scale1r.
  rewrite dotmul_normalize_norm scalerA -mulrA divrr ?mulr1 ?unitfE ?norm_eq0 //.
  by rewrite subrK crossmulZv crossmulvv 2!scaler0 addr0.
- rewrite -rodrigues_genP // /rodrigues_gen dotmulC.
  rewrite (_ : normalize w *d Base.j w = 0) ?mulr0 ?scale0r ?addr0; last first.
    by move: (NOFrame.idotj f).
  rewrite (Base.icrossj w0) norm_normalize // expr1n scale1r scalerBl scale1r.
  by rewrite opprB addrCA subrr addr0.
- rewrite -rodrigues_genP // /rodrigues_gen dotmulC.
  rewrite (_ : normalize w *d Base.k w = 0) ?mulr0 ?scale0r ?addr0; last first.
    by move: (NOFrame.idotk f).
  rewrite (norm_normalize w0) expr1n scale1r scalerBl scale1r opprB addrCA subrr.
  rewrite addr0 addrC; congr (_ + _).
  rewrite (_ : Base.j w = - Base.i w *v Base.k w); last first.
    by rewrite crossmulNv (Base.icrossk w0) opprK.
  by rewrite crossmulNv scalerN scaleNr opprK.
Qed.

Lemma eskew_is_onto_SO M : M \is 'SO[R]_3 ->
  exists a, M = `e^(a, normalize (vaxis_euler M)).
Proof.
move=> MSO.
set w : vector := normalize _.
case: (SO_isRot MSO) => a Ha.
exists a.
move: (isRot_eskew a (vaxis_euler_neq0 MSO)).
rewrite -/w.
by move/(@same_isRot _ _ _ _ _ 1 (vaxis_euler_neq0 MSO) ltr01 _ (esym (scale1r _)) Ha).
Qed.

Section alternative_definition_of_eskew.

(* TODO: rename *)
Definition eskew' (a : angle R) (e : 'rV[R]_3) :=
  e^T *m e + (cos a) *: (1 - e^T *m e) + sin a *: \S( e ).

(* [angeles] p.42, eqn 2.49 *)
Lemma isRot_exp_eskew' a Q u : norm u = 1 ->
  isRot a u (mx_lin1 Q) -> Q = eskew' a u.
Proof.
move=> e1 Maxis.
apply/eqP/mulmxP => p.
have QO : Q \is 'O[R]_3.
  have : u != 0 by rewrite -norm_eq0 e1 oner_eq0.
  by move/isRot_SO => /(_ _ _ Maxis); rewrite mx_lin1K rotationE => /andP[].
rewrite (decomp (p *m Q) u).
have -> : axialcomp (p *m Q) u = axialcomp p u.
  rewrite axialcompE.
  case/isRotP : (Maxis) => /= H2 _ _.
  rewrite -{2}H2 trmx_mul mulmxA -(mulmxA p).
  move: QO; rewrite orthogonalE mulmxE => /eqP ->.
  by rewrite mulmx1 axialcompE.
rewrite /eskew'.
rewrite -[in RHS]addrA mulmxDr axialcompE mulmxA; congr (_ + _).
  by rewrite e1 expr1n invr1 scale1r.
have H1 : normalcomp (p *m Q) u = cos a *: normalcomp p u - sin a *: (p *v u).
  transitivity (normalcomp p u *m Q).
    (* TODO: lemma? *)
    rewrite /normalcomp mulmxBl; congr (_ - _).
    case/isRotP: Maxis => /= H1 _ _.
    rewrite -2!scalemxAl H1; congr (_ *: _).
    rewrite 2!dotmulZv -{2}H1.
    by rewrite (proj2 (orth_preserves_dotmul Q) QO u).
  case/isRotP: Maxis => /= H1 H2 H3.
  move: (orthogonal_expansion (Base.frame (norm1_neq0 e1))) => /(_ (normalcomp p (Base.i u))) /= Hp.
  rewrite (_ : Base.i u = u) in Hp; last by rewrite /Base.i normalizeI.
  rewrite dotmul_normalcomp // scale0r add0r in Hp.
  rewrite Hp mulmxDl -2!scalemxAl.
  rewrite (_ : Base1.j u = Base.j u); last first.
    by rewrite /Base.j /Base.i normalizeI.
  rewrite (_ : Base1.k u = Base.k u); last first.
    by rewrite /Base.k /Base.i normalizeI.
  rewrite H2 H3.
  rewrite (scalerDr (normalcomp p u *d Base.j u)) scalerA mulrC -scalerA.
  rewrite [in RHS]scalerDr -!addrA; congr (_ + _).
  rewrite (scalerDr (normalcomp p u *d Base.k u)) addrA addrC.
  rewrite scalerA mulrC -scalerA; congr (_ + _).
  rewrite scalerA mulrC -scalerA addrC scalerA mulrC -scalerA addrC.
  rewrite -{1}(opprK (sin a)) 3!scaleNr -opprB opprK -scalerBr; congr (- (_ *: _)).
  rewrite -double_crossmul.
  (* TODO: shouldn't be using Base1... *)
  move: (Frame.jcrossk (Base.frame (norm1_neq0 e1))).
  rewrite -Base.jE -Base.kE -Base.iE => ->.
  rewrite {2}(decomp p u) [in RHS]crossmulC linearD /=.
  rewrite crossmul_axialcomp add0r -[in RHS]crossmulC.
  by rewrite /Base.i normalizeI.
rewrite {}H1 /normalcomp scalerBr mulmxDr -scalemxAr mulmxBr mulmx1.
rewrite scalerBr -2!addrA; congr (_ + _).
rewrite -scalemxAr -(scalerN (sin a)) crossmulC opprK -(skew_mxE p u).
congr (- (_ *: _) + _).
rewrite normalizeI //.
by rewrite dotmulC mulmxA (mx11_scalar (p *m _)) mul_scalar_mx.
Qed.

Lemma eskew'E w (a : angle R) : norm w = 1 -> eskew' a w = `e^(a, w).
Proof.
move=> w1.
rewrite /eskew' /emx3 addrAC skew_mx2 -addrA addrCA.
rewrite -[in RHS]addrA [in RHS]addrCA; congr (_ + _).
rewrite scalerBl scale1r addrCA -addrA; congr (_ + _).
rewrite scalerBr [in RHS]scalerBr opprB !addrA; congr (_ - _).
by rewrite addrC w1 expr1n !scalemx1 (addrC _ 1) subrr addr0.
Qed.

Lemma isRot_skew' e (e0 : e != 0) (a : angle R) :
  isRot a e (mx_lin1 (eskew' a (normalize e))).
Proof. move: (isRot_eskew a e0); by rewrite eskew'E ?norm_normalize. Qed.

Lemma axial_vec_exp_skew' (e : vector) a : axial_vec (eskew' a e) = sin a *: e *+ 2.
Proof.
rewrite /eskew' 2!axial_vecD (_ : axial_vec _ = 0) ?add0r; last first.
  apply/eqP; by rewrite -axial_vec_sym mul_tr_vec_sym.
rewrite (_ : axial_vec _ = 0) ?add0r; last first.
  apply/eqP; rewrite -axial_vec_sym sym_scaler_closed (* TODO: delcare the right canonical to be able to use rpredZ *) //.
  by rewrite rpredD // ?sym_cst // rpredN mul_tr_vec_sym.
rewrite axial_vecZ axial_vecE scalerMnr; congr (_ *: _).
by rewrite unskewD skew_mxK unskewN tr_skew unskewN skew_mxK opprK mulr2n.
Qed.

Lemma isRot_pi_inv (M : 'M[R]_3) u :
  u != 0 -> isRot pi u (mx_lin1 M) ->
  M = (normalize u)^T *m normalize u *+ 2 - 1.
Proof.
move=> u0 H.
have /isRot_exp_eskew' {H} : isRot pi (normalize u) (mx_lin1 M).
  by rewrite isRotZ // invr_gt0 norm_gt0.
rewrite norm_normalize // => /(_ erefl) ->.
by rewrite /eskew' cospi sinpi scale0r addr0 scaleN1r opprB addrA -mulr2n.
Qed.

End alternative_definition_of_eskew.

End exponential_map_rot.

Notation "'`e(' a ',' M ')'" := (emx3 a M) (format "'`e(' a ','  M ')'").
Notation "'`e^(' a ',' w ')'" := (emx3 a \S( w )) (format "'`e^(' a ','  w ')'").

Module Aa.
Section angle_of_angle_axis_representation.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types M : 'M[R]_3.

Definition angle M := acos ((\tr M - 1) / 2%:R).

Lemma angle1 : angle 1 = 0.
Proof.
rewrite /angle mxtrace1 (_ : 3%:R - 1 = 2%:R); last first.
  by apply/eqP; rewrite subr_eq -(natrD _ 2 1).
by rewrite divrr ?unitfE ?pnatr_eq0 // acos1.
Qed.

Lemma anglepi (u : 'rV[R]_3) (u1 : norm u = 1) : angle (u^T *m u *+ 2 - 1) = pi.
Proof.
rewrite /angle mxtraceD linearN /= mxtrace1 mulr2n linearD /=.
rewrite mxtrace_tr_mul u1 expr1n (_ : _ - 1 = - 2%:R); last first.
  by apply/eqP; rewrite -opprB eqr_opp opprB (_ : 1 + 1 = 2%:R) // -natrB.
by rewrite -mulr_natl mulNr divrr ?mulr1 ?unitfE ?pnatr_eq0 // acosN1.
Qed.

Lemma sym_angle M : M \is 'SO[R]_3 ->
  M \is sym 3 R -> angle M = 0 \/ angle M = pi.
Proof.
move=> MSO Msym.
case/eskew_is_onto_SO : (MSO) => a Ma.
move: (Msym).
rewrite {1}Ma /emx3.
rewrite symE !linearD /= trmx1 /= !linearZ /= skew_mx2 !linearD /= !linearN /=.
rewrite trmx_mul trmxK scalemx1 tr_scalar_mx tr_skew.
rewrite !addrA subr_eq subrK.
rewrite [in X in _ == X]addrC -subr_eq0 !addrA !opprD !addrA addrK.
rewrite scalerN opprK -addrA addrCA !addrA (addrC _ 1) subrr add0r.
rewrite -mulr2n scalerMnl scaler_eq0 mulrn_eq0 /=.
rewrite -skew_mx0 skew_inj -norm_eq0 norm_normalize ?vaxis_euler_neq0 // oner_eq0 orbF.
case/eqP/sin0_inv => [a0|api]; move: Ma.
- rewrite a0 emx30M => ->; rewrite angle1; by left.
- rewrite api -eskew'E ?norm_normalize // ?vaxis_euler_neq0 //. 
  rewrite /eskew' cospi scaleN1r sinpi scale0r addr0 opprB.
  rewrite addrA -mulr2n => ->; rewrite anglepi // ?norm_normalize // ?vaxis_euler_neq0 //.
  by right.
Qed.

Lemma tr_angle M : angle M^T = angle M.
Proof. by rewrite /angle mxtrace_tr. Qed.

Lemma isRot_angle M u a : u != 0 -> a \in Opi_closed R ->
  isRot a u (mx_lin1 M) -> a = angle M.
Proof.
move=> u0 Ha.
move/(mxtrace_isRot u0); rewrite /angle => ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr ?mulr1 ?cosK //.
by rewrite unitfE pnatr_eq0.
Qed.

Lemma isRot_angleN M u a :
  u != 0 -> a \in piO_closed R ->
  isRot a u (mx_lin1 M) -> a = - angle M.
Proof.
move=> u0 Ha /(mxtrace_isRot u0); rewrite /angle=> ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr; last first.
  by rewrite unitfE pnatr_eq0.
by rewrite mulr1 cosKN // opprK.
Qed.

(* NB: useful? *)
Lemma angle_Rx a :
  (a \in Opi_closed R -> angle (Rx a) = a) /\
  (a \in piO_closed R -> angle (Rx a) = - a).
Proof.
split => Ha; rewrite /angle mxtrace_Rx addrAC subrr add0r
  -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1;
  by [rewrite cosK | rewrite cosKN].
Qed.

Lemma angle_RO M a : M = block_mx (1 : 'M_1) 0 0 (RO a) ->
  (a \in Opi_closed R -> angle M = a) /\
  (a \in piO_closed R -> angle M = - a).
Proof.
move=> Ma.
rewrite /angle Ma (mxtrace_block (1 : 'M_1)) tr_RO mxtrace1 addrAC.
rewrite subrr add0r -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1.
split => Ha; by [rewrite cosK | rewrite cosKN].
Qed.

Lemma angle_eskew a u : norm u = 1 -> a \in Opi_closed R ->
  angle `e^(a, u) = a.
Proof.
move=> u1 Ha.
rewrite /angle trace_eskew // addrAC subrr add0r.
by rewrite mulrAC divrr ?mul1r ?unitfE // ?pnatr_eq0 // cosK.
Qed.

Lemma angle0_tr M : M \is 'SO[R]_3 -> angle M = 0 -> \tr M = 3%:R.
Proof.
move=> MSO /(congr1 (fun x => cos x)).
rewrite cos0 /angle acosK; last first.
  case: (SO_isRot MSO) => a HM.
  case: (angle_in a).
    move/(isRot_angle (vaxis_euler_neq0 MSO))/(_ HM) => ?; subst a.
    move/(mxtrace_isRot (vaxis_euler_neq0 MSO)) : HM => ->.
    rewrite addrAC subrr add0r.
    rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
    by rewrite -ler_norml cos_max.
  move/(isRot_angleN (vaxis_euler_neq0 MSO))/(_ HM) => ?; subst a.
  move/(mxtrace_isRot (vaxis_euler_neq0 MSO)) : HM => ->.
  rewrite addrAC subrr add0r.
  rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
  by rewrite -ler_norml cos_max.
move/(congr1 (fun x => x * 2%:R)).
rewrite -mulrA mulVr ?unitfE ?pnatr_eq0 // mulr1 mul1r.
move/(congr1 (fun x => x + 1)).
rewrite subrK => ->.
by rewrite (natrD _ 2 1).
Qed.

Lemma angle_pi_tr M : M \is 'SO[R]_3 -> angle M = pi -> \tr M = - 1.
Proof.
move=> MSO /(congr1 (fun x => cos x)).
rewrite cospi /angle acosK; last first.
  (* TODO: factorize with angle0_tr *)
  case: (SO_isRot MSO) => a HM.
  case: (angle_in a).
    move/(isRot_angle (vaxis_euler_neq0 MSO))/(_ HM) => ?; subst a.
    move/(mxtrace_isRot (vaxis_euler_neq0 MSO)) : HM => ->.
    rewrite addrAC subrr add0r.
    rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
    by rewrite -ler_norml cos_max.
  move/(isRot_angleN (vaxis_euler_neq0 MSO))/(_ HM) => ?; subst a.
  move/(mxtrace_isRot (vaxis_euler_neq0 MSO)) : HM => ->.
  rewrite addrAC subrr add0r.
  rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
  by rewrite -ler_norml cos_max.
move/(congr1 (fun x => x * 2%:R)).
rewrite -mulrA mulVr ?unitfE ?pnatr_eq0 // mulr1.
move/(congr1 (fun x => x + 1)).
by rewrite subrK mulN1r mulr2n opprD subrK.
Qed.

Lemma SO_pi_inv M : M \is 'SO[R]_3 -> angle M = pi ->
  let u := normalize (vaxis_euler M) in
  M = u^T *m u *+ 2 - 1.
Proof.
move=> MSO Mpi u.
have [a H] := SO_isRot MSO.
have ? : a = pi.
  case: (angle_in a) => Ha.
     by move/isRot_angle : H => /(_ (vaxis_euler_neq0 MSO)) -> //.
  by move/isRot_angleN : H => /(_ (vaxis_euler_neq0 MSO)) -> //; rewrite piNpi Mpi.
subst a.
by move/isRot_pi_inv : H => /(_ (vaxis_euler_neq0 MSO)).
Qed.

Lemma SO_pi_axial_vec M : M \is 'SO[R]_3 -> angle M = pi -> axial_vec M = 0.
Proof.
move=> MSO.
move/SO_pi_inv => /(_ MSO) ->.
apply/eqP; rewrite -axial_vec_sym rpredD // ?rpredN ?sym_cst //.
by rewrite mulr2n rpredD // mul_tr_vec_sym.
Qed.

Lemma rotation_is_Rx M k (k0 : 0 < k) : M \is 'SO[R]_3 ->
  axial_vec M = k *: 'e_0 ->
  angle M \in Opi_closed R /\
  (M = Rx (- angle M) \/ M = Rx (angle M)).
Proof.
move=> MSO axialVi.
have [M02 M01] : M 0 2%:R = M 2%:R 0 /\ M 0 1 = M 1 0.
  move/matrixP/(_ 0 1) : (axialVi).
  rewrite !mxE /= mulr0 => /eqP; rewrite subr_eq add0r => /eqP ->.
  move/matrixP/(_ 0 2%:R) : (axialVi).
  by rewrite !mxE /= mulr0 => /eqP; rewrite subr_eq add0r => /eqP ->.
have axial_eigen : axial_vec M *m M = axial_vec M.
  move: (axial_vec_vec_eigenspace MSO) => /eigenspaceP; by rewrite scale1r.
have [M010 [M020 M001]] : M 0 1 = 0 /\ M 0 2%:R = 0 /\ M 0 0 = 1.
  move: axial_eigen.
  rewrite axialVi -scalemxAl => /scalerI.
  rewrite gtr_eqF // => /(_ isT) ViM.
  have : 'e_0 *m M = row 0 M by rewrite rowE.
  rewrite {}ViM => ViM.
  move/matrixP : (ViM) => /(_ 0 1); rewrite !mxE /= => <-.
  move/matrixP : (ViM) => /(_ 0 2%:R); rewrite !mxE /= => <-.
  by move/matrixP : (ViM) => /(_ 0 0); rewrite !mxE /= => <-.
have [P MP] : exists P : 'M[R]_2, M = block_mx (1 : 'M_1) 0 0 P.
  exists (@drsubmx _ 1 2 1 2 M).
  rewrite -{1}(@submxK _ 1 2 1 2 M).
  rewrite (_ : ulsubmx _ = 1); last first.
    apply/matrixP => i j.
    rewrite (ord1 i) (ord1 j) !mxE /= -M001 mulr1n; congr (M _ _); by apply val_inj.
  rewrite (_ : ursubmx _ = 0); last first.
    apply/rowP => i.
    case/boolP : (i == 0) => [/eqP ->|].
      rewrite !mxE -[RHS]M010; congr (M _ _); by apply val_inj.
    rewrite ifnot01 => /eqP ->; rewrite !mxE -[RHS]M020; congr (M _ _); by apply val_inj.
  rewrite (_ : dlsubmx _ = 0) //.
  apply/colP => i.
  case/boolP : (i == 0) => [/eqP ->|].
    rewrite !mxE -[RHS]M010 M01; congr (M _ _); by apply val_inj.
  rewrite ifnot01 => /eqP ->; rewrite !mxE -[RHS]M020 M02; congr (M _ _); by apply val_inj.
have PSO : P \is 'SO[R]_2 by have := MSO; rewrite MP (@SOSn_SOn _ 1 2).
move=> [: Hangle].
split.
  abstract: Hangle.
  rewrite inE /angle MP (mxtrace_block (1 : 'M_1)) mxtrace1 addrAC.
  rewrite subrr add0r sin_acos.
    by rewrite sqrtr_ge0.
  rewrite normrM normrV ?unitfE ?pnatr_eq0 // normr_nat ler_pdivr_mulr // mul1r.
  exact: tr_SO2.
case/rot2d : PSO => a PRO; rewrite {}PRO in MP.
case: (angle_in a) => Ha.
- move: (proj1 (angle_RO MP) Ha) => MHa.
  right; by rewrite MHa MP Rx_RO.
- move: (proj2 (angle_RO MP) Ha) => MHa.
  left; by rewrite MHa opprK MP Rx_RO.
Qed.

End angle_of_angle_axis_representation.

Section vector_axis_of_angle_axis_representation.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition vaxis M : 'rV[R]_3 :=
  let a := angle M in 
  if a == pi then 
    vaxis_euler M
  else
    1 / ((sin a) *+ 2) *: axial_vec M.

Lemma vaxis_ortho_of_iso (M : 'M[R]_3) (MSO : M \is 'SO[R]_3) :
  vaxis M *m M = vaxis M.
Proof.
rewrite /vaxis.
case: ifPn => [_|pi]; first by apply/eqP; rewrite vaxis_eulerP.
move/axial_vec_vec_eigenspace : MSO => /eigenspaceP.
rewrite -scalemxAl => ->; by rewrite scale1r.
Qed.

Lemma isRot_vaxis (M : 'M[R]_3) u a : u != 0 -> sin a != 0 ->
  isRot a u (mx_lin1 M) ->
  normalize u = (1 / (sin a *+ 2)) *: axial_vec M.
Proof.
move=> u0 sina0 H.
have -> : M = `e^(a, normalize u).
  apply: (@same_isRot _ _ _ _ _ 1 u0 _ a) => //.
  by rewrite scale1r.
  exact: (isRot_eskew _ u0).
rewrite axial_vec_eskew scalerA div1r.
by rewrite mulVr ?scale1r // unitfE mulrn_eq0 negb_or.
Qed.

End vector_axis_of_angle_axis_representation.
End Aa.

Section angle_axis_of_rot.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition log_rot (M : 'M[R]_3) : angle R * 'rV[R]_3 :=
  (Aa.angle M, Aa.vaxis M).

Lemma log_exp_eskew (a : angle R) (w : 'rV[R]_3) :
  sin a != 0 -> a \in Opi_closed R -> norm w = 1 ->
  log_rot `e^(a, w) = (a, w).
Proof.
move=> sphi Ha w1 [:Hphi].
congr pair.
  abstract: Hphi.
  rewrite /Aa.angle trace_eskew // addrAC subrr add0r.
  by rewrite mulrC mulrA mulVr ?mul1r ?(cosK Ha) // unitfE pnatr_eq0.
apply/rowP => i.

rewrite /Aa.vaxis Hphi.
move: (sphi).
rewrite sin_eq0 negb_or => /andP[_]/negbTE ->.

rewrite 2!mxE /= => [:twosphi].
case: ifPn => [/eqP ->|].
  rewrite 4!mxE /= skewij mxE skew_mx2' 2!mxE /= add0r.
  rewrite 4!mxE /= skewij mxE skew_mx2' 2!mxE /= add0r opprD addrAC addrA subrK.
  rewrite mulrN opprK -mulr2n -mulrnAl div1r mulrA mulVr ?mul1r //.
  abstract: twosphi.
  by rewrite unitfE mulrn_eq0 negb_or.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite 4!mxE /= skewij mxE skew_mx2' 2!mxE /= add0r.
  rewrite 4!mxE /= skewij mxE skew_mx2' 2!mxE /= add0r opprD addrAC addrA subrK.
  by rewrite mulrN opprK -mulr2n -mulrnAl mulrA div1r mulVr // mul1r.
rewrite 4!mxE /= skewij mxE skew_mx2' 2!mxE /= add0r.
rewrite 4!mxE /= skewij mxE skew_mx2' 2!mxE /= add0r opprD addrAC addrA subrK.
by rewrite mulrN opprK -mulr2n -mulrnAl mulrA div1r mulVr // mul1r.
Qed.

Lemma angle_axis_eskew M : M \is 'SO[R]_3 ->
  M = `e^(Aa.angle M, normalize (Aa.vaxis M)).
Proof.
move=> MSO; case/boolP : (axial_vec M == 0) => [|M0].
  rewrite -axial_vec_sym => M0'.
  case/(Aa.sym_angle MSO) : (M0') => [a0|api].
    clear M0'.
    rewrite /Aa.vaxis {1}a0 emx30M.
    move/(Aa.angle0_tr MSO): (a0).
    move/O_tr_idmx => M1; rewrite {1}M1 //; by apply rotation_sub.
  move/(Aa.SO_pi_inv MSO) : (api) => api'.
  rewrite /Aa.vaxis api eqxx.
  rewrite /emx3 sinpi scale0r addr0 cospi opprK -(natrD _ 1 1).
  rewrite skew_mx2 norm_normalize // ?vaxis_euler_neq0 // expr1n scalerDl scale1r.
  rewrite [in RHS]addrC -![in RHS]addrA (addrC _ 1) scalemx1 subrr addr0.
  by rewrite [in RHS]addrCA -mulr2n [in RHS]addrC.
case/boolP : (Aa.angle M == 0) => [/eqP H|a0].
  rewrite H.
  move/(Aa.angle0_tr MSO) : H.
  move/O_tr_idmx => ->; by [rewrite emx30M | apply rotation_sub].
case/boolP : (Aa.angle M == pi) => [/eqP H|api].
  rewrite -eskew'E; last first.
    by rewrite /Aa.vaxis H eqxx norm_normalize // vaxis_euler_neq0.
  rewrite H /eskew' cospi scaleN1r sinpi scale0r addr0 opprB addrA -mulr2n.
  rewrite /Aa.vaxis H eqxx //; by apply Aa.SO_pi_inv.
have sina0 : sin (Aa.angle M) != 0.
  apply: contra a0 => /eqP/sin0_inv [->//|/eqP]; by rewrite (negbTE api).
set w : 'rV_3 := normalize _.
have [a Rota] := SO_isRot MSO.
have {Rota}Rota : isRot a (normalize (vaxis_euler M)) (mx_lin1 M).
  by rewrite (isRotZ a _ (vaxis_euler_neq0 MSO)) // invr_gt0 norm_gt0 vaxis_euler_neq0.
have w0 : normalize (vaxis_euler M) != 0 by rewrite normalize_eq0 vaxis_euler_neq0.
have Htmp0 : Aa.vaxis M != 0.
  rewrite /Aa.vaxis (negbTE api) scaler_eq0 negb_or M0 andbT div1r.
  by rewrite invr_eq0 mulrn_eq0 /= sin_eq0 negb_or a0 api.
have w1 : norm w = 1 by rewrite norm_normalize.
case: (angle_in a) => Ha.
- move: (Aa.isRot_angle w0 Ha Rota) => a_angle_of_rot.
  rewrite a_angle_of_rot in Rota.
  move: (Aa.isRot_vaxis w0 sina0 Rota) => w'axial.
  set k := (1 / _) in w'axial.
  have k0 : 0 < k.
    rewrite /k div1r invr_gt0 pmulrn_lgt0 // ltr_neqAle eq_sym sina0 /=.
    by rewrite inE a_angle_of_rot in Ha.
  apply: (@same_isRot _ _ _ _ (norm (Aa.vaxis M) *: w) ((sin (Aa.angle M) *+ 2) * k) w0 _ (Aa.angle M) _ Rota).
  - by rewrite pmulr_rgt0 // pmulrn_lgt0 // ltr_neqAle eq_sym sina0 -a_angle_of_rot.
  - rewrite -(norm_scale_normalize (normalize (vaxis_euler M))).
    rewrite norm_normalize ?vaxis_euler_neq0 // w'axial.
    rewrite scale1r {2}/k div1r divrr ?unitfE ?mulrn_eq0 //= scale1r.
    by rewrite /w norm_scale_normalize /Aa.vaxis (negbTE api).
  - move: (isRot_eskew (Aa.angle M) (norm1_neq0 w1)).
    rewrite {3}/w norm_scale_normalize (normalizeI w1) {1}/w {1}/normalize.
    by rewrite isRotZ // invr_gt0 norm_gt0.
- move: (Aa.isRot_angleN w0 Ha Rota) => a_angle_of_rot.
  have : M \in unitmx by rewrite orthogonal_unit // rotation_sub // -rotationV.
  move/(@isRot_tr _ _ (Aa.angle M^T) w0 M).
  rewrite {1}Aa.tr_angle -a_angle_of_rot => /(_ Rota).
  rewrite (rotation_inv MSO) Aa.tr_angle.
  move/(Aa.isRot_vaxis w0 sina0) => w'axial.
  set k := (1 / _) in w'axial.
  have k0 : 0 < k.
    rewrite /k div1r invr_gt0 pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  apply: (@same_isRot _ _ _ _ (- norm (Aa.vaxis M) *: w) ((sin (Aa.angle M) *+ 2) * k) w0 _ (- Aa.angle M)).
  - rewrite pmulr_rgt0 // pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  - rewrite -(norm_scale_normalize (normalize (vaxis_euler M))).
    rewrite norm_normalize ?vaxis_euler_neq0 // w'axial.
    rewrite scale1r {2}/k div1r divrr ?unitfE ?mulrn_eq0 //= scale1r.
    rewrite /w scaleNr norm_scale_normalize /Aa.vaxis (negbTE api).
    by rewrite tr_axial_vec scalerN.
  - by rewrite -a_angle_of_rot.
  - move: (isRot_eskew (Aa.angle M) (norm1_neq0 w1)).
    rewrite {3}/w scaleNr norm_scale_normalize (normalizeI w1) => H.
    rewrite isRotN // opprK.
    by move: H; rewrite {1}/w {1}/normalize isRotZ // invr_gt0 norm_gt0.
Qed.

Lemma angle_axis_isRot (Q : 'M[R]_3) : axial_vec Q != 0 ->
  Q \is 'SO[R]_3 ->
  isRot (Aa.angle Q) (normalize (Aa.vaxis Q)) (mx_lin1 Q).
Proof.
move=> Q0 QSO.
move/angle_axis_eskew : (QSO) => H.
case/boolP : (Aa.angle Q == 0) => [|a0].
  move/eqP/(Aa.angle0_tr QSO).
  move/(O_tr_idmx (rotation_sub QSO)) => Q1; subst Q.
  rewrite Aa.angle1; by apply isRot1.
case/boolP : (Aa.angle Q == pi) => [api|api].
  move/eqP/(Aa.SO_pi_inv QSO) : (api) => HQ.
  rewrite /Aa.vaxis api (eqP api) {2}HQ.
  apply isRotpi; by rewrite norm_normalize // vaxis_euler_neq0.
move=> [:vaxis0].
rewrite {3}H isRotZ; last 2 first.
  abstract: vaxis0.
  rewrite /Aa.vaxis (negbTE api) scaler_eq0 negb_or Q0 andbT div1r. 
  by rewrite invr_eq0 mulrn_eq0 /= sin_eq0 negb_or a0 api.
  by rewrite invr_gt0 norm_gt0.
by apply isRot_eskew.
Qed.

End angle_axis_of_rot.

Section angle_axis_representation.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Record angle_axis := AngleAxis {
  angle_axis_val : angle R * vector ;
  _ : norm (angle_axis_val.2) == 1 }.

Canonical angle_axis_subType := [subType for angle_axis_val].

Definition aangle (a : angle_axis) := (val a).1.
Definition aaxis (a : angle_axis) := (val a).2.

Lemma norm_axis a : norm (aaxis a) = 1.
Proof. by case: a => *; apply/eqP. Qed.

Fact norm_e1_subproof : norm (@delta_mx R _ 3 0 0) == 1.
Proof. by rewrite norm_delta_mx. Qed.

Definition angle_axis_of (a : angle R) (v : vector) :=
  insubd (@AngleAxis (a,_) norm_e1_subproof) (a, normalize v).

Lemma aaxis_of (a : angle R) (v : vector) : v != 0 ->
  aaxis (angle_axis_of a v) = normalize v.
Proof.
move=> v_neq0 /=; rewrite /angle_axis_of /aaxis val_insubd /=.
by rewrite normZ normfV normr_norm mulVf ?norm_eq0 // eqxx.
Qed.

Lemma aangle_of (a : angle R) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

(*Coercion exp_skew_of_angle_axis r :=
  let (a, w) := (aangle r, aaxis r) in `e^(a, w).*)

Definition angle_axis_of_rot M := angle_axis_of (Aa.angle M) (Aa.vaxis M).

Lemma angle_axis_eskew_old M : M \is 'SO[R]_3 ->
  Aa.vaxis M != 0 ->
  let a := aangle (angle_axis_of_rot M) in
  let w := aaxis (angle_axis_of_rot M) in
  M = `e^(a, w).
Proof.
move=> MSO M0 a w.
rewrite (angle_axis_eskew MSO) /a aangle_of; congr (`e^(_, _)).
by rewrite /w /angle_axis_of_rot /= aaxis_of.
Qed.

End angle_axis_representation.

(* NB: work in progress *)
Section euler_angles.

Variable R : rcfType.

Definition Rxyz (c b a : angle R) := Rx c * Ry b * Rz a.

Definition euler_angles_rot (a b c : angle R) :=
  let ca := cos a in let cb := cos b in let cc := cos c in
  let sa := sin a in let sb := sin b in let sc := sin c in
  col_mx3
  (row3 (ca * cb) (sa * cb) (- sb))
  (row3 (ca * sb * sc - sa * cc) (sa * sb * sc + ca * cc) (cb * sc))
  (row3 (ca * sb * cc + sa * sc) (sa * sb * cc - ca * sc) (cb * cc)).

Lemma euler_angles_rotE a b c : Rxyz c b a = euler_angles_rot a b c.
Proof.
rewrite /Rxyz.
apply/matrix3P; rewrite !mxE /= sum3E !mxE /= !sum3E !mxE /=; Simp.r => //.
by rewrite mulrC.
by rewrite mulrC.
by rewrite mulrAC -mulrA mulrC (mulrC (cos c)).
by rewrite mulrC (mulrC (sin c)) mulrA (mulrC (cos c)).
by rewrite mulrC.
by rewrite mulrC (mulrC (cos c)) mulrA (mulrC (sin c)).
by rewrite mulrC (mulrC (cos c)) mulrA (mulrC (sin c)).
by rewrite mulrC.
Qed.

Lemma sqr_Mi0E M i : M \is 'O[R]_3 -> 
  M i 1 ^+ 2 + M i 2%:R ^+ 2 = 1 - M i 0 ^+ 2.
Proof.
move/norm_row_of_O => /(_ i)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite -addrA addrC eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_Mi1E M i : M \is 'O[R]_3 ->
  M i 0 ^+ 2 + M i 2%:R ^+ 2 = 1 - M i 1 ^+ 2.
Proof.
move/norm_row_of_O => /(_ i)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite addrAC eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_Mi2E M i : M \is 'O[R]_3 ->
  M i 0 ^+ 2 + M i 1 ^+ 2 = 1 - M i 2%:R ^+ 2.
Proof.
move/norm_row_of_O => /(_ i)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_M2jE M j : M \is 'O[R]_3 ->
  M 0 j ^+ 2 + M 1 j ^+ 2 = 1 - M 2%:R j ^+ 2.
Proof.
move/norm_col_of_O => /(_ j)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_M0jE M j : M \is 'O[R]_3 ->
  M 1 j ^+ 2 + M 2%:R j ^+ 2 = 1 - M 0 j ^+ 2.
Proof.
move/norm_col_of_O => /(_ j)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite -addrA addrC eq_sym -subr_eq => /eqP <-.
Qed.

Lemma Mi2_1 M i : M \is 'O[R]_3 -> 
  (`| M i 2%:R | == 1) = (M i 0 == 0) && (M i 1 == 0).
Proof.
move=> MO; move/eqP: (sqr_Mi2E i MO) => {MO}MO.
apply/idP/idP => [Mi2|/andP[/eqP Mi0 /eqP Mi1]]; last first.
  move: MO; by rewrite Mi0 Mi1 expr2 mulr0 addr0 eq_sym subr_eq add0r eq_sym sqr_norm_eq1.
move: MO; rewrite -(sqr_normr (M i 2%:R)) (eqP Mi2) expr1n subrr.
by rewrite paddr_eq0 ?sqr_ge0 // => /andP[]; rewrite 2!sqrf_eq0 => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Lemma M2j_1 M j : M \is 'O[R]_3 ->
  (`| M 2%:R j | == 1) = (M 0 j == 0) && (M 1 j == 0).
Proof.
move=> MO; move/eqP: (sqr_M2jE j MO) => {MO}MO.
apply/idP/idP => [Mi2|/andP[/eqP Mi0 /eqP Mi1]]; last first.
  move: MO; by rewrite Mi0 Mi1 expr2 mulr0 addr0 eq_sym subr_eq add0r eq_sym sqr_norm_eq1.
move: MO; rewrite -(sqr_normr (M 2%:R j)) (eqP Mi2) expr1n subrr.
by rewrite paddr_eq0 ?sqr_ge0 // => /andP[]; rewrite 2!sqrf_eq0 => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Lemma sqrtr_sqrN2 (x : R) : x != 0 -> Num.sqrt (x ^- 2) = `|x|^-1.
Proof.
move=> x0.
apply (@mulrI _ `|x|); first by rewrite unitfE normr_eq0.
rewrite -{1}(sqrtr_sqr x) -sqrtrM ?sqr_ge0 // divrr; last by rewrite unitfE normr_eq0.
by rewrite divrr ?sqrtr1 // unitfE sqrf_eq0.
Qed.

Lemma N1x2_gt0 (x : R) : `| x | < 1 -> 0 < 1 - x ^+ 2.
Proof. move=> x1; by rewrite subr_gt0 -sqr_normr expr_lt1. Qed.

Definition yarc (x : R) := Num.sqrt (1 - x ^+ 2).

Lemma yarc_neq0 (x : R) : `| x | < 1 -> yarc x != 0.
Proof. by move=> x1; rewrite sqrtr_eq0 -ltrNge N1x2_gt0. Qed.

Lemma yarc_gt0 (x : R) : `| x | < 1 -> 0 < yarc x.
Proof. by move=> x1; rewrite ltr_neqAle sqrtr_ge0 andbT eq_sym yarc_neq0. Qed.

Lemma sqr_yarc (x : R) : `| x | < 1 -> (yarc x) ^+ 2 = 1 - x ^+ 2.
Proof. move=> x1; by rewrite /yarc sqr_sqrtr // ltrW // N1x2_gt0. Qed.

Lemma inv_yarc (x : R) : `| x | < 1 -> (yarc x)^-1 = Num.sqrt (1 - x ^+ 2)^-1.
Proof.
move=> x1.
apply (@mulrI _ (yarc x)); first by rewrite unitfE yarc_neq0.
rewrite divrr; last by rewrite unitfE yarc_neq0.
rewrite -sqrtrM; last by rewrite ltrW // N1x2_gt0.
by rewrite divrr ?sqrtr1 // unitfE gtr_eqF // N1x2_gt0.
Qed.

Lemma inv_yarc_gt0 (x : R) : `| x | < 1 -> 0 < (yarc x)^-1.
Proof. move=> x1; by rewrite inv_yarc // sqrtr_gt0 invr_gt0 N1x2_gt0. Qed.

Lemma atan2_x_gt0E (x y : R) : y > 0 -> atan2 x y = atan (x / y).
Proof. move=> y0; by rewrite /atan2 y0. Qed.

Lemma atan2_ge0_lt0E (x y : R) : x >= 0 -> y < 0 -> atan2 x y = atan (x / y) + pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltrNge ltrW. Qed.

Lemma atan2_lt0_lt0E (x y : R) : x < 0 -> y < 0 -> atan2 x y = atan (x / y) - pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltrNge ltrW //= lerNgt x0. Qed.

Lemma atan2_gt0_0E (x y : R) : x > 0 -> atan2 x 0 = pihalf _.
Proof. by move=> x0; rewrite /atan2 x0 ltrr. Qed.

Lemma atan2_lt0_0E (x y : R) : x < 0 -> atan2 x 0 = - pihalf _.
Proof. move=> x0; by rewrite /atan2 ltrr ltrNge ltrW //= x0. Qed.

Lemma cos_atan2 (x y : R) : y != 0 -> cos (atan2 x y) = y / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neqr_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // cosDpi ?eqxx // cos_atan mul1r expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 ltr_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?ltr_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltrNge ltr_paddr // ?sqr_ge0 // exprn_even_gt0 // orbC ltr_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 ltr_eqF.
    by rewrite !invrN invrK mulNr opprK.
  rewrite atan2_lt0_lt0E // -piNpi cosDpi ?eqxx ?orbT // cos_atan mul1r expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // cos_atan mul1r.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gtr_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gtr_eqF // gtr0_norm // invrM ?invrK //.
by rewrite unitfE sqrtr_eq0 -ltrNge ltr_paddr // ?sqr_ge0 // exprn_gt0.
by rewrite unitfE invr_neq0 // gtr_eqF.
Qed.

Lemma cos_atan2_yarc (x : R) : `| x | < 1 -> cos (atan2 (- x) (yarc x)) = yarc x.
Proof.
move=> x1; by rewrite cos_atan2 ?yarc_neq0 // sqr_yarc // sqrrN subrK sqrtr1 divr1.
Qed.

Lemma sin_atan2 (x y : R) : y != 0 -> sin (atan2 x y) = x / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neqr_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // sinDpi ?eqxx // sin_atan expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 ltr_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?ltr_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltrNge ltr_paddr // ?sqr_ge0 // exprn_even_gt0 // orbC ltr_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 ltr_eqF.
    rewrite !invrN invrK mulNr mulrN opprK -mulrA (mulrA _^-1) mulVr ?mul1r //.
    by rewrite unitfE ltr_eqF.
  rewrite atan2_lt0_lt0E // -piNpi sinDpi ?eqxx ?orbT // sin_atan expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // sin_atan.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gtr_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gtr_eqF // gtr0_norm // invrM; last 2 first.
  by rewrite unitfE sqrtr_eq0 -ltrNge ltr_paddr // ?sqr_ge0 // exprn_gt0.
  by rewrite unitfE invr_neq0 // gtr_eqF.
rewrite invrK -(mulrA x) (mulrA _^-1) mulVr ?mul1r //.
by rewrite unitfE gtr_eqF.
Qed.

Lemma sin_atan2_yarc (x : R) : `| x | < 1 -> sin (atan2 x (yarc x)) = x.
Proof.
move=> x1; by rewrite sin_atan2 ?yarc_neq0 // sqr_yarc // subrK sqrtr1 divr1.
Qed.

Lemma cos_atan2_0 (x : R) : cos (atan2 x 0) = (x == 0)%:R.
Proof.
rewrite /atan2 ltrr; case: ifPn => [x0|]; first by rewrite cos_pihalf gtr_eqF.
rewrite -lerNgt ler_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltrr cos0 eqxx.
by rewrite x0 cosN cos_pihalf ltr_eqF.
Qed.

Lemma sin_atan2_0 (x : R) : sin (atan2 x 0) = Num.sg x.
Proof.
rewrite /atan2 ltrr; case: ifPn => [x0|]; first by rewrite sin_pihalf gtr0_sg.
rewrite -lerNgt ler_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltrr sin0 sgr0.
by rewrite x0 sinN sin_pihalf ltr0_sg.
Qed.

Definition euler_b (M : 'M[R]_3) : angle R := (* theta *)
  if `| M 0 2%:R | != 1 then
    - asin (M 0 2%:R)
  else if M 0 2%:R == 1 then
    - pihalf R
  else (* M 0 2%:R == - 1*) pihalf R.

Definition euler_c (M : 'M[R]_3) : angle R := (* psi *)
  if `| M 0 2%:R | != 1 then
    atan2 (M 1 2%:R / cos (euler_b M)) (M 2%:R 2%:R / cos (euler_b M))
  else if M 0 2%:R == 1 then
    atan2 (- M 1 0) (- M 2%:R 0)
  else
    atan2 (M 1 0) (M 2%:R 1).

Definition euler_a (M : 'M[R]_3) : angle R := (* phi *)
  if `| M 0 2%:R | != 1 then
    atan2 (M 0 1 / cos (euler_b M)) (M 0 0 / cos (euler_b M))
  else
    0.

Lemma rot_euler_anglesE M : M \is 'SO[R]_3 ->
  M = Rxyz (euler_c M) (euler_b M) (euler_a M).
Proof.
move=> MSO.
rewrite euler_angles_rotE.
apply/matrix3P; rewrite !mxE /=.
- (* 0 0 *) rewrite /euler_a /euler_b; case: ifPn => [M02|].
    rewrite M02.
    have M02' : `|M 0 2%:R| < 1.
      by rewrite ltr_neqAle M02 andTb Oij_ub // rotation_sub.
    rewrite cosN cos_asin //.
    case/boolP : (M 0 0 == 0) => [/eqP|]M00.
      rewrite M00 mul0r cos_atan2_0.
      case/boolP : (M 0 1 == 0) => [/eqP|]M01.
        by rewrite M01 mul0r eqxx mul1r /yarc -sqr_Mi2E ?rotation_sub // M00 M01 expr0n addr0 sqrtr0.
      by rewrite mulf_eq0 (negbTE M01) /= invr_eq0 (negbTE (yarc_neq0 _)) // mul0r.
    rewrite cos_atan2; last by rewrite mulf_neq0 // invr_neq0 // yarc_neq0.
    rewrite 2!expr_div_n -mulrDl sqr_Mi2E ?rotation_sub // sqrtrM; last first.
      by rewrite subr_ge0 -sqr_normr expr_le1 // ltrW.
    rewrite -/(yarc _) sqrtr_sqrN2 ?yarc_neq0 // gtr0_norm ?yarc_gt0 // divrr; last first.
      by rewrite unitfE yarc_neq0.
    by rewrite divr1 -mulrA mulVr ?mulr1 // unitfE yarc_neq0.
  rewrite negbK cos0 mul1r => M02.
  have -> : M 0 0 = 0 by move: M02; rewrite Mi2_1 ?rotation_sub // => /andP[/eqP].
  move: M02; rewrite eqr_norml ler01 andbT => /orP[] /eqP ->.
    by rewrite eqxx cosN cos_pihalf.
  by rewrite Neqxx oner_eq0 cos_pihalf.
- (* 0 1 *)
  rewrite /euler_a /euler_b; case: ifPn => [M02|].
    rewrite M02.
    have M02' : `|M 0 2%:R| < 1.
      by rewrite ltr_neqAle M02 andTb Oij_ub // rotation_sub.
    rewrite cosN cos_asin //.
    case/boolP : (M 0 0 == 0) => [/eqP|]M00.
      rewrite M00 mul0r sin_atan2_0 sgrM sgrV (gtr0_sg (yarc_gt0 _)) // mulr1 /yarc.
      by rewrite -sqr_Mi2E ?rotation_sub // M00 expr0n add0r sqrtr_sqr -numEsg.
    rewrite sin_atan2; last by rewrite mulf_neq0 // invr_neq0 // yarc_neq0.
    rewrite 2!expr_div_n -mulrDl sqr_Mi2E ?rotation_sub // sqrtrM; last first.
      by rewrite subr_ge0 -sqr_normr expr_le1 // ltrW.
    rewrite -/(yarc _) sqrtr_sqrN2 ?yarc_neq0 // gtr0_norm ?yarc_gt0 // divrr; last first.
      by rewrite unitfE yarc_neq0.
    by rewrite divr1 -mulrA mulVr ?mulr1 // unitfE yarc_neq0.
 by rewrite negbK sin0 mul0r Mi2_1 ?rotation_sub // => /andP[_ /eqP].
- (* 0 2 *) rewrite /euler_b; case: ifPn => [M02|].
  + have {M02}M02 : `|M 0 2%:R| < 1.
      by rewrite ltr_neqAle M02 andTb Oij_ub // ?rotation_sub.
    by rewrite sinN opprK asinK // -lter_norml ltrW.
  + rewrite negbK eqr_norml ler01 andbT => /orP[]/eqP ->.
       by rewrite eqxx sinN sin_pihalf opprK.
     by rewrite Neqxx oner_eq0 sin_pihalf.
- (* 1 0 *)
  rewrite /euler_a /euler_c /euler_b; case: ifPn => [M02|].
    rewrite M02.
    have M02' : `|M 0 2%:R| < 1.
      by rewrite ltr_neqAle M02 andTb Oij_ub // rotation_sub.
    rewrite cosN sinN cos_asin // asinK // -?lter_norml ?ltrW //.
    rewrite -/(yarc _).
    case/boolP : (M 0 0 == 0) => [/eqP|]M00.
      rewrite M00 mul0r cos_atan2_0 sin_atan2_0.
      rewrite mulf_eq0 invr_eq0 (negbTE (yarc_neq0 _)) // orbF.
      rewrite sgrM sgrV (gtr0_sg (yarc_gt0 _)) // mulr1.
      case/boolP : (M 0 1 == 0) => [/eqP|]M01.
        exfalso.
        move: (sqr_Mi0E 0 (rotation_sub MSO)).
        rewrite M00 M01 expr0n subr0 add0r => /(congr1 Num.sqrt).
        rewrite sqrtr1 sqrtr_sqr; by apply/eqP.
      rewrite 2!mul0r add0r.
      have [x [Hcx Hsx]] : {x | M 0 1 = cos x /\ M 0 2%:R = sin x}.
        apply sqrD1_cossin.
        by rewrite sqr_Mi0E ?rotation_sub // M00 expr0n subr0.
      rewrite Hcx Hsx /yarc -cos2sin2 sqrtr_sqr.
      case/boolP: (M 2%:R 2%:R == 0) => [/eqP|]M22.
        rewrite M22 mul0r cos_atan2_0 mulf_eq0 invr_eq0 normr_eq0 -Hcx (negbTE M01) orbF.
        rewrite -normr_eq0.
        move: (sqr_M2jE 2%:R (rotation_sub MSO)).
        rewrite Hsx M22 expr0n subr0 => /eqP; rewrite eq_sym addrC -subr_eq => /eqP/esym.
        move/(congr1 Num.sqrt); rewrite sqrtr_sqr => ->.
        rewrite -cos2sin2 sqrtr_sqr normr_eq0 -Hcx (negbTE M01) mulr0 oppr0.
        have M12 : M 1 2%:R != 0.
          rewrite -sqrf_eq0.
          move: (norm_col_of_O (rotation_sub MSO) 2%:R).
          move/(congr1 (fun x => x ^+ 2))/eqP.
          rewrite -dotmulvv expr1n dotmulE sum3E tr_col !mxE M22 mulr0 addr0 Hsx -!expr2.
          rewrite eq_sym addrC -subr_eq => /eqP <-.
          by rewrite -cos2sin2 sqrf_eq0 -Hcx.
        move: (rotation_sub MSO).
        move/orthogonalPcol/(_ 0 2%:R)/eqP.
        rewrite /= dotmulE sum3E tr_col !mxE M00 mul0r add0r M22 mulr0 addr0.
        by rewrite mulf_eq0 (negbTE M12) orbF => /eqP.
      rewrite cos_atan2; last first.
        by rewrite mulf_neq0 // invr_eq0 normr_eq0 -Hcx.
      rewrite !expr_div_n -mulrDl (addrC (_^+2)) sqr_M0jE ?rotation_sub // sqrtrM; last first.
        by rewrite subr_ge0 -sqr_normr expr_le1 // ltrW.
      rewrite sqr_normr sqrtr_sqrN2; last first.
        by rewrite -Hcx.
      rewrite Hsx -cos2sin2 sqrtr_sqr divrr ?unitfE ?normr_eq0; last first.
        by rewrite -Hcx.
      rewrite divr1.
      rewrite mulrCA.
      rewrite -invr_sg -invrM; last 2 first.
        by rewrite unitfE normr_eq0 -Hcx.
        by rewrite unitfE sgr_eq0 -Hcx.
      rewrite (mulrC (`| _|)) -numEsg -Hcx.
      admit.
    admit.
  rewrite negbK cos0 mul1r sin0 mul0r subr0.
  rewrite eqr_norml ler01 andbT => /orP[]/eqP M02.
    rewrite M02 eqxx sinN sin_pihalf mulN1r.
    case/boolP : (M 2%:R 0 == 0) => [/eqP|]M20.
      rewrite M20 oppr0 sin_atan2_0 sgrN opprK.
      admit.
    rewrite sin_atan2 // ?eqr_oppLR ?oppr0 //.
    rewrite mulNr opprK.
    admit.
  rewrite M02 Neqxx oner_eq0 sin_pihalf mul1r.
  case/boolP : (M 2%:R 1 == 0) => [/eqP|]M21.
    rewrite M21 sin_atan2_0.
    admit.
  rewrite sin_atan2 //.
  admit.
- (* 1 1 *) admit.
- (* 1 2 *) admit.
- (* 2 0 *) admit.
- (* 2 1 *) admit.
- (* 2 2 *) admit.
Abort.

End euler_angles.
