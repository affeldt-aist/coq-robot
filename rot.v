(* coq-robot (c) 2017 AIST and INRIA. License: LGPL v3. *)
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

Require Import ssr_ext angle euclidean3 skew vec_angle frame.

(* OUTLINE:
  1. section two_dimensional_rotation
  2. section elementary_rotations
     Rx, Ry, Rz
  3. section isRot.
     definition of rotations w.r.t. a vector
     section properties_of_isRot
     section relation_with_rotation_matrices
     sample lemmas:
       all rotations around a vector of angle a have trace "1 + 2 * cos a"
       equivalence SO[R]_3 <-> Rot
  4. section exponential_map_rot
     specialized exponential map
     sample lemmas:
       inverse of the exponential map,
       exponential map of a skew matrix is a rotation
     Rodrigues formula:
       u * e^(phi,w) can be expressed using a lin. comb. of vectors u, (u *d w)w, u *v w)
  5. Module Aa (angle-axis representation)
     section angle_of_angle_axis_representation
     section vector_axis_of_angle_axis_representation
     section angle_axis_of_rot
       sample lemmas:
         a rotation matrix has angle_aa M and normalize (vaxis_aa M) for exp. coor.
  6. section angle_axis_representation
  7. section euler_angles (wip)
*)

Reserved Notation "'`e(' a ',' M ')'" (format "'`e(' a ','  M ')'").
Reserved Notation "'`e^(' a ',' w ')'" (format "'`e^(' a ','  w ')'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section two_dimensional_rotation.

Variable T : rcfType.
Implicit Types (a b : angle T) (M : 'M[T]_2).

Definition RO a := col_mx2 (row2 (cos a) (sin a)) (row2 (- sin a) (cos a)).

Lemma trmx_RO a : (RO a)^T = RO (- a).
Proof.
apply/matrixP => i j.
rewrite !mxE /= cosN sinN opprK.
case: ifPn => [/eqP ->{j}|].
  case: ifPn => [/eqP ->{i}|]; first by rewrite !mxE.
  by rewrite ifnot01 => /eqP ->{i}; rewrite eqxx !mxE.
rewrite ifnot01 => /eqP ->; rewrite eqxx.
case: ifPn => [/eqP ->{i}|]; rewrite ?mxE //= ifnot01 => /eqP ->{i}.
by rewrite eqxx /= mxE.
Qed.

Lemma tr_RO a : \tr (RO a) = (cos a) *+ 2.
Proof. by rewrite /mxtrace sum2E !mxE /= mulr2n. Qed.

Lemma RO_is_O a : RO a \is 'O[T]_2.
Proof.
apply/orthogonal2P; rewrite !rowK /= !dotmulE !sum2E !mxE /= -!expr2 cos2Dsin2.
by rewrite addrC mulrN mulrC subrr addrC mulNr mulrC subrr sqrrN addrC cos2Dsin2 !eqxx.
Qed.

Lemma RO_is_SO a : RO a \is 'SO[T]_2.
Proof.
by rewrite rotationE RO_is_O /= det_mx22 !mxE /= mulrN opprK -!expr2 cos2Dsin2.
Qed.

Lemma rot2d_helper M a b : a - b = - pihalf T ->
  M = col_mx2 (row2 (cos a) (sin a)) (row2 (cos b) (sin b)) ->
  { a0 | M = RO a0 }.
Proof.
move=> abpi.
have -> : sin b = cos a.
  by move/eqP : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC cosBpihalf.
have -> : cos b = - sin a.
  by move/eqP : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC sinBpihalf opprK.
move=> ->; by exists a.
Qed.

Lemma rot2d M : M \is 'SO[T]_2 -> {a | M = RO a}.
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

Lemma rot2d_helper' M a b : a - b = pihalf T ->
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

Lemma rot2d' M : M \is 'O[T]_2 -> { a : angle T & {M = RO a} + {M = RO' a} }.
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

Lemma tr_SO2 M : M \is 'SO[T]_2 -> `|\tr M| <= 2%:R.
Proof.
case/rot2d => a PRO; move: (cos_max a) => ca.
rewrite PRO tr_RO -(mulr_natr (cos a)) normrM normr_nat.
by rewrite -[in X in _ <= X]mulr_natr ler_pmul.
Qed.

End two_dimensional_rotation.

Section elementary_rotations.

Variable T : rcfType.
Implicit Types a b : angle T.

Definition Rx a := col_mx3
  'e_0
  (row3 0 (cos a) (sin a))
  (row3 0 (- sin a) (cos a)).

Lemma Rx0 : Rx 0 = 1.
Proof.
by rewrite /Rx cos0 sin0 oppr0; apply/matrix3P/and9P; split; rewrite !mxE.
Qed.

Lemma Rxpi : Rx pi = diag_mx (row3 1 (-1) (-1)).
Proof.
rewrite /Rx cospi sinpi oppr0; apply/matrix3P/and9P; split;
  by rewrite !mxE /= -?mulNrn ?mulr1n ?mulr0n.
Qed.

Lemma Rx_RO a : Rx a = block_mx (1 : 'M_1) 0 0 (RO a).
Proof.
rewrite -(@submxK _ 1 2 1 2 (Rx a)) (_ : ulsubmx _ = 1); last first.
  apply/rowP => i; by rewrite (ord1 i) !mxE /=.
rewrite (_ : ursubmx _ = 0); last by apply/rowP => i; rewrite !mxE.
rewrite (_ : dlsubmx _ = 0); last first.
  apply/colP => i; rewrite !mxE /=.
  case: ifPn; [by rewrite !mxE | by case: ifPn; rewrite !mxE].
rewrite (_ : drsubmx _ = RO a) //; by apply/matrix2P; rewrite !mxE /= !eqxx.
Qed.

Lemma Rx_is_SO a : Rx a \is 'SO[T]_3.
Proof. by rewrite Rx_RO (SOSn_SOn 1) RO_is_SO. Qed.

Lemma mxtrace_Rx a : \tr (Rx a) = 1 + cos a *+ 2.
Proof. by rewrite /Rx /mxtrace sum3E !mxE /= -addrA -mulr2n. Qed.

Lemma inv_Rx a : (Rx a)^-1 = Rx (- a).
Proof.
move/rotation_inv : (Rx_is_SO a) => ->.
rewrite /Rx cosN sinN opprK; by apply/matrix3P/and9P; split; rewrite !mxE.
Qed.

Definition Rx' a := col_mx3
  'e_0
  (row3 0 (cos a) (sin a))
  (row3 0 (sin a) (- cos a)).

Lemma Rx'_RO a : Rx' a = block_mx (1 : 'M_1) 0 0 (RO' a).
Proof.
rewrite -(@submxK _ 1 2 1 2 (Rx' a)) (_ : ulsubmx _ = 1); last first.
  apply/rowP => i; by rewrite (ord1 i) !mxE /=.
rewrite (_ : ursubmx _ = 0); last by apply/rowP => i; rewrite !mxE.
rewrite (_ : dlsubmx _ = 0); last first.
  apply/colP => i; rewrite !mxE /=.
  case: ifPn; first by rewrite !mxE.
  by case: ifPn; rewrite !mxE.
rewrite (_ : drsubmx _ = RO' a) //; by apply/matrix2P; rewrite !mxE /= !eqxx.
Qed.

Lemma det_Rx' a : \det (Rx' a) = -1.
Proof.
rewrite det_mx33 !mxE /=. Simp.r. by rewrite -!expr2 -opprD cos2Dsin2.
Qed.

Definition Ry a := col_mx3
  (row3 (cos a) 0 (- sin a))
  'e_1
  (row3 (sin a) 0 (cos a)).

Lemma Ry_is_SO a : Ry a \is 'SO[T]_3.
Proof.
apply/rotation3P/and4P; split.
- rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
  by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 addr0 -2!expr2 sqrrN cos2Dsin2.
- rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
   by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 addr0 add0r mulr1.
- by rewrite 2!rowK /= dotmulE sum3E !mxE /= !mulr0 mul0r !add0r.
- rewrite 3!rowK /= crossmulE !mxE /=. by Simp.r.
Qed.

Definition Rz a := col_mx3
  (row3 (cos a) (sin a) 0)
  (row3 (- sin a) (cos a) 0)
  'e_2%:R.

Lemma Rz_RO a : Rz a = block_mx (RO a) 0 0 (1 : 'M_1).
Proof.
rewrite -(@submxK _ 2 1 2 1 (Rz a)) (_ : drsubmx _ = 1); last first.
  apply/rowP => i; by rewrite (ord1 i) !mxE.
rewrite (_ : ulsubmx _ = RO a); last by apply/matrix2P; rewrite !mxE !eqxx.
rewrite (_ : ursubmx _ = 0); last first.
  apply/colP => i; case/boolP : (i == 0) => [|/ifnot01P]/eqP->; by rewrite !mxE.
rewrite (_ : dlsubmx _ = 0) //; apply/rowP => i; rewrite !mxE /=.
by case/boolP : (i == 0) => [|/ifnot01P]/eqP->.
Qed.

Lemma trmx_Rz a : (Rz a)^T = Rz (- a).
Proof. by rewrite Rz_RO (tr_block_mx (RO a)) !(trmx0,trmx1) trmx_RO -Rz_RO. Qed.

Lemma RzM a b : Rz a * Rz b = Rz (a + b).
Proof.
rewrite {1 2}/Rz e2row -mulmxE !mulmx_col3 !mulmx_row3_col3. Simp.r.
rewrite !row3Z !row3D. Simp.r. rewrite -e2row; congr col_mx3.
- by rewrite -cosD sinD (addrC (_ * _)).
- by rewrite -opprD -sinD [in X in row3 _ X _]addrC -cosD.
Qed.

Lemma Rz_is_SO a : Rz a \is 'SO[T]_3.
Proof.
apply/rotation3P/and4P; split.
- rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
  by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 addr0 -2!expr2 cos2Dsin2.
- rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
- by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 addr0 mulrN mulNr opprK addrC cos2Dsin2.
- by rewrite 2!rowK /= dotmulE sum3E !mxE /= mulrN mulr0 addr0 addrC mulrC subrr.
- rewrite 3!rowK /= crossmulE !mxE /=. Simp.r. by rewrite -!expr2 cos2Dsin2 e2row.
Qed.

Lemma RzE a : Rz a = (frame_of_SO (Rz_is_SO a)) _R^ (can_frame T).
Proof. rewrite FromTo_to_can; by apply/matrix3P/and9P; split; rewrite !mxE. Qed.

Lemma rmap_Rz_e0 a :
  rmap (can_tframe T) `[ 'e_0 $ frame_of_SO (Rz_is_SO a) ] =
                      `[ row 0 (Rz a) $ can_tframe T ].
Proof. by rewrite rmapE_to_can rowE [in RHS]RzE FromTo_to_can. Qed.

Definition Rzy a b := col_mx3
    (row3 (cos a * cos b) (sin a) (- cos a * sin b))
    (row3 (- sin a * cos b) (cos a) (sin a * sin b))
    (row3 (sin b) 0 (cos b)).

Lemma RzyE a b : Rz a * Ry b = Rzy a b.
Proof.
rewrite /Rz /Ry -mulmxE mulmx_col3(* TODO * -> *m *).
congr col_mx3.
- rewrite mulmx_row3_col3 scale0r addr0 row3Z mulr0.
  by rewrite e1row row3Z row3D ?(addr0,mulr0,add0r,mulr1,mulrN,mulNr).
- rewrite mulmx_row3_col3 scale0r addr0 row3Z mulr0.
  by rewrite e1row row3Z row3D mulr0 addr0 add0r mulr1 addr0 mulrN !mulNr opprK.
- by rewrite e2row mulmx_row3_col3 scale0r add0r scale0r add0r scale1r.
Qed.

Lemma Rzy_is_SO a b : Rzy a b \is 'SO[T]_3.
Proof. by rewrite -RzyE rpredM // ?Rz_is_SO // Ry_is_SO. Qed.

End elementary_rotations.

Section isRot.

Local Open Scope frame_scope.

Variable T : rcfType.
Implicit Types a : angle T.

Definition isRot a (u : 'rV[T]_3) (f : {linear 'rV_3 -> 'rV_3}) : bool :=
  let: j := (Base.frame u) |, 1 in let: k := (Base.frame u) |, 2%:R in
  [&& f u == u,
      f j == cos a *: j + sin a *: k &
      f k == - sin a *: j + cos a *: k].

Lemma isRotP a u (f : {linear 'rV_3 -> 'rV_3}) : reflect
  (let: j := (Base.frame u) |, 1 in let: k := (Base.frame u) |, 2%:R in
  [/\ f u = u, f j = cos a *: j + sin a *: k & f k = - sin a *: j + cos a *: k])
  (isRot a u f).
Proof.
apply: (iffP idP); first by case/and3P => /eqP ? /eqP ? /eqP ?.
by case => H1 H2 H3; apply/and3P; rewrite H1 H2 H3.
Qed.

Section properties_of_isRot.

Variable u : 'rV[T]_3.
Implicit Types M N : 'M[T]_3.

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
- rewrite cospi sinpi scale0r addr0 scaleN1r -Base.jE ?norm1_neq0 //=.
  rewrite mulmxDr -scaler_nat -scalemxAr mulmxA.
  by rewrite Base.j_tr_mul // mul0mx scaler0 add0r mulmxN mulmx1.
- rewrite sinpi oppr0 scale0r add0r cospi scaleN1r.
  rewrite -Base.kE ?norm1_neq0 //= mulmxBr mulmx1.
  by rewrite -scaler_nat -scalemxAr mulmxA Base.k_tr_mul // scaler0 add0r.
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

Lemma isRotN a M (u0 : u != 0) :
  isRot (- a) u (mx_lin1 M) -> isRot a (- u) (mx_lin1 M).
Proof.
move=> /isRotP [/= H1 H2 H3]; apply/isRotP; split => /=.
by rewrite mulNmx H1.
by rewrite Base.jN (Base.kN u0) H2 cosN sinN scalerN scaleNr.
by rewrite (Base.kN u0) Base.jN mulNmx H3 sinN cosN opprK scalerN scaleNr opprD.
Qed.

Lemma isRotZ a f k (u0 : u != 0) (k0 : 0 < k) :
  isRot a (k *: u) f = isRot a u f.
Proof.
rewrite /isRot !Base.Z // !linearZ; congr andb.
apply/idP/idP => [/eqP/scalerI ->//|/eqP ->//]; by move/gt_eqF : k0 => /negbT.
Qed.

Lemma isRotZN a f k (u0 : u != 0) (k0 : k < 0):
  isRot a (k *: u) (mx_lin1 f) = isRot (- a) u (mx_lin1 f).
Proof.
rewrite /isRot /= sinN cosN opprK Base.ZN // Base.jN (Base.kN u0).
rewrite !scalerN !scaleNr mulNmx eqr_oppLR opprD !opprK -scalemxAl; congr andb.
apply/idP/idP => [/eqP/scalerI ->//|/eqP ->//]; by move/lt_eqF : k0 => /negbT.
Qed.

Lemma mxtrace_isRot a M (u0 : u != 0) :
  isRot a u (mx_lin1 M) -> \tr M = 1 + cos a *+ 2.
Proof.
case/isRotP=> /= Hu Hj Hk.
move: (@basis_change _ M (Base.frame u) (Rx a)).
rewrite /= !mxE /= !scale1r !scale0r !add0r !addr0.
rewrite (invariant_colinear u0 Hu) ?colinear_frame0 // => /(_ erefl Hj Hk) ->.
rewrite mxtrace_mulC mulmxA mulmxV ?mul1mx ?mxtrace_Rx //.
by rewrite unitmxE unitfE rotation_det ?oner_neq0 // Base.is_SO.
Qed.

Lemma same_isRot M N v k (u0 : u != 0) (k0 : 0 < k) a :
  u = k *: v ->
  isRot a u (mx_lin1 M) -> isRot a v (mx_lin1 N) ->
  M = N.
Proof.
move=> mkp /isRotP[/= HMi HMj HMk] /isRotP[/= HNi HNj HNk].
apply/eqP/mulmxP => w.
rewrite (orthogonal_expansion (Base.frame u) w).
rewrite !mulmxDl -!scalemxAl.
have v0 : v != 0 by apply: contra u0; rewrite mkp => /eqP ->; rewrite scaler0.
congr (_ *: _ + _ *: _ + _ *: _).
- by rewrite (Base.frame0E u0) /normalize -scalemxAl HMi {2}mkp -HNi scalemxAl -mkp
    scalemxAl.
- by rewrite HMj /= mkp (Base.Z _ k0) -HNj.
- by rewrite HMk /= mkp (Base.Z _ k0) -HNk.
Qed.

Lemma isRot_0_inv (u0 : u != 0) M : isRot 0 u (mx_lin1 M) -> M = 1.
Proof.
move=> H; move/(same_isRot u0 ltr01 _ H) : isRot1; apply; by rewrite scale1r.
Qed.

Lemma isRot_tr a (u0 : u != 0) M : M \in unitmx ->
  isRot (- a) u (mx_lin1 M) -> isRot a u (mx_lin1 M^-1).
Proof.
move=> Hf /isRotP /= [/= H1 H2 H3].
move: (@basis_change _ M (Base.frame u) (Rx (- a))).
rewrite /= !mxE /= !(scale0r,addr0,add0r,scale1r) -H2 -H3.
rewrite (invariant_colinear u0 H1) ?colinear_frame0 //.
move/(_ erefl erefl erefl) => fRx.
have HfRx : M^-1 = (col_mx3 (Base.frame u)|,0 (Base.frame u)|,1 (Base.frame u)|,2%:R)^T *m
   (Rx (- a))^-1 *m col_mx3 (Base.frame u)|,0 (Base.frame u)|,1 (Base.frame u)|,2%:R.
  rewrite fRx invrM /=; last 2 first.
    rewrite unitrMr orthogonal_unit // ?(rotation_sub (Rx_is_SO _)) //.
    by rewrite rotation_inv ?Base.is_SO // rotation_sub // rotationV Base.is_SO.
    by rewrite orthogonal_unit // rotation_sub // Base.is_SO.
  rewrite invrM; last 2 first.
    rewrite rotation_inv ?Base.is_SO // orthogonal_unit // rotation_sub //.
    by rewrite rotationV // Base.is_SO.
    by rewrite orthogonal_unit // ?(rotation_sub (Rx_is_SO _)).
  by rewrite invrK rotation_inv ?Base.is_SO // mulmxE mulrA.
apply/isRotP; split => /=.
- by rewrite -{1}H1 -mulmxA mulmxV // mulmx1.
- rewrite HfRx !mulmxA.
  rewrite (_ : (Base.frame u)|,1 *m _ = 'e_1); last first.
    by rewrite mul_tr_col_mx3 dotmulC dotmulvv normj // expr1n idotj // jdotk // e1row.
  rewrite (_ : 'e_1 *m _ = row3 0 (cos (- a)) (sin a)); last first.
    rewrite (rotation_inv (Rx_is_SO (- a))) /Rx mul_tr_col_mx3.
    rewrite dote2 /= 2!dotmulE 2!sum3E !mxE /= cosN sinN opprK. by Simp.r.
  by rewrite mulmx_row3_col3 scale0r add0r cosN.
- rewrite HfRx !mulmxA.
  rewrite (_ : (Base.frame u)|,2%:R *m _ = 'e_2%:R); last first.
    by rewrite mul_tr_col_mx3 dotmulC idotk // dotmulC jdotk // dotmulvv normk // expr1n e2row.
  rewrite (_ : 'e_2%:R *m _ = row3 0 (- sin a) (cos a)); last first.
    rewrite (rotation_inv (Rx_is_SO (- a))) /Rx mul_tr_col_mx3.
    rewrite dote2 /= 2!dotmulE 2!sum3E !mxE /= cosN sinN opprK. by Simp.r.
  by rewrite mulmx_row3_col3 scale0r add0r.
Qed.

Lemma isRot_SO a M (u0 : u != 0) : isRot a u (mx_lin1 M) -> M \is 'SO[T]_3.
Proof.
move/isRotP=> /= [Hu Hj Hk].
move: (@basis_change _ M (Base.frame u) (Rx a)).
rewrite /= !mxE /= !(scale1r,scale0r,add0r,addr0).
rewrite (invariant_colinear u0 Hu) ?colinear_frame0 // => /(_ erefl Hj Hk) ->.
by rewrite rpredM // ?Base.is_SO // rpredM // ?Rx_is_SO // rotation_inv // ?Base.is_SO // rotationV Base.is_SO.
Qed.

End properties_of_isRot.

Section relation_with_rotation_matrices.

Lemma SO_isRot M : M \is 'SO[T]_3 ->
  {a | isRot a (vaxis_euler M) (mx_lin1 M)}.
Proof.
move=> MSO.
set e := vaxis_euler M.
case/boolP : (M == 1) => [/eqP ->|M1]; first by exists 0; exact: isRot1.
have v0 := vaxis_euler_neq0 MSO.
rewrite -/e in v0.
have vMv := vaxis_eulerP MSO.
rewrite -/e in vMv.
set i := (Base.frame e)|,0. set j := (Base.frame e)|,1. set k := (Base.frame e)|,2%:R.
have iMi : i *m M = i.
  by rewrite (invariant_colinear v0) // ?colinear_frame0.
have iMj : i *d (j *m M) = 0.
  rewrite -iMi (proj2 (orth_preserves_dotmul M) (rotation_sub MSO) i j).
  by rewrite /i /j 2!rowframeE dot_row_of_O // NOFrame.MO.
have iMk : i *d (k *m M) = 0.
  rewrite -iMi (proj2 (orth_preserves_dotmul M) (rotation_sub MSO) i k).
  by rewrite /i /k 2!rowframeE dot_row_of_O // NOFrame.MO.
set a := (j *m M) *d j.
set b := (j *m M) *d k.
have ab : j *m M = a *: j + b *: k.
  by rewrite {1}(orthogonal_expansion (Base.frame e) (j *m M)) dotmulC iMj
    scale0r add0r.
set c := (k *m M) *d j.
set d := (k *m M) *d k.
have cd : k *m M = c *: j + d *: k.
  by rewrite {1}(orthogonal_expansion (Base.frame e) (k *m M)) dotmulC iMk
    scale0r add0r.
have H1 : a ^+ 2 + b ^+ 2 = 1.
  move/eqP: (norm_row_of_O (NOFrame.MO (Base.frame e)) 1).
  rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n -dotmulvv.
  rewrite -(proj2 (orth_preserves_dotmul M) (rotation_sub MSO)).
  rewrite -rowframeE ab dotmulDr 2!dotmulDl 4!dotmulvZ 4!dotmulZv 2!dotmulvv.
  by rewrite normj // normk // !(expr1n,mulr1) -!expr2 dotmulC jdotk // !(mulr0,add0r,addr0) => /eqP.
have H2 : a * c + b * d = 0.
  move/eqP: (dot_row_of_O (NOFrame.MO (Base.frame e)) 1 2%:R).
  rewrite -2!rowframeE -(proj2 (orth_preserves_dotmul M) (rotation_sub MSO) j k) ab cd.
  rewrite dotmulDr 2!dotmulDl 4!dotmulvZ 4!dotmulZv 2!dotmulvv normj // normk //.
  by rewrite expr1n !mulr1 dotmulC jdotk // 4!mulr0 add0r addr0 mulrC (mulrC d) => /eqP.
have H3 : c ^+ 2 + d ^+ 2 = 1.
  move/eqP: (norm_row_of_O (NOFrame.MO (Base.frame e)) 2%:R).
  rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n -dotmulvv.
  rewrite -(proj2 (orth_preserves_dotmul M) (rotation_sub MSO)) -!rowframeE -/k cd.
  rewrite dotmulDr 2!dotmulDl 4!dotmulvZ 4!dotmulZv 2!dotmulvv normj // normk //.
  by rewrite expr1n 2!mulr1 -2!expr2 dotmulC jdotk // !(mulr0,addr0,add0r) => /eqP.
set P := col_mx2 (row2 a b) (row2 c d).
have PO : P \is 'O[T]_2.
  apply/orthogonal2P; rewrite !rowK /= !dotmulE !sum2E !mxE /=.
  by rewrite -!expr2 H1 H2 mulrC (mulrC d) H2 H3 !eqxx.
case: (rot2d' PO) => phi [phiRO | phiRO']; subst P.
- case/eq_col_mx2 : phiRO => Ha Hb Hc Hd.
  exists phi.
  rewrite -(@isRotZ _ phi (mx_lin1 M) 1 _ _) // scale1r; apply/isRotP; split => //.
  by rewrite -!(Ha,Hb,Hc).
  by rewrite -!(Hb,Hc,Hd).
- exfalso.
  case/eq_col_mx2 : phiRO' => Ha Hb Hc Hd.
  move: (@basis_change _ M (Base.frame e) (Rx' phi)).
  rewrite !mxE /= !(addr0,add0r,scale0r,scale1r) -/i -/j -/k.
  rewrite -{1}Ha -{1}Hb -{1}Hc -{1}Hd.
  rewrite -ab iMi -cd => /(_ erefl erefl erefl) => HM.
  move: (rotation_det MSO).
  rewrite HM 2!det_mulmx det_Rx' detV -crossmul_triple.
  move: (Frame.MSO (Base.frame e)).
  rewrite rotationE => /andP[_] /=.
  rewrite crossmul_triple => /eqP.
  rewrite /i /j /k.
  rewrite !rowframeE.
  rewrite -col_mx3_rowE => ->.
  rewrite invr1 mulr1 mul1r => /eqP.
  by rewrite Neqxx oner_eq0.
Qed.

End relation_with_rotation_matrices.

End isRot.

Section exponential_map_rot.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Implicit Types (u v w : vector) (a b : angle T) (M : 'M[T]_3).

Definition emx3 a M : 'M_3 := 1 + sin a *: M + (1 - cos a) *: M ^+ 2.

Local Notation "'`e(' a ',' M ')'" := (emx3 a M).

Lemma emx3a0 a : `e(a, 0) = 1.
Proof. by rewrite /emx3 expr0n /= 2!scaler0 2!addr0. Qed.

Lemma emx30M M : `e(0, M) = 1.
Proof. by rewrite /emx3 sin0 cos0 subrr 2!scale0r 2!addr0. Qed.

Lemma tr_emx3 a M : `e(a, M)^T = `e(a, M^T).
Proof.
by rewrite /emx3 !linearD /= !linearZ /= trmx1 expr2 trmx_mul expr2.
Qed.

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

Local Notation "'`e^(' a ',' w ')'" := (emx3 a \S( w )).

Lemma eskew_pi w : norm w = 1 -> `e^(pi, w) = w^T *m w *+ 2 - 1.
Proof.
move=> w1.
rewrite /emx3 sinpi scale0r addr0 cospi opprK -(natrD _ 1 1).
rewrite sqr_spin w1 expr1n scalerDr addrCA scalerN scaler_nat; congr (_ + _).
rewrite scaler_nat mulr2n opprD addrCA.
by rewrite (_ : 1%:A = 1) // ?subrCA ?subrr ?addr0 // -idmxE scale1r.
Qed.

Lemma eskew_v0 a : `e^(a, 0) = 1.
Proof. by rewrite spin0 emx3a0. Qed.

Lemma unspin_eskew a w : unspin `e^(a, w) = sin a *: w.
Proof.
rewrite /emx3 !(unspinD,unspinZ,unspinN,sqr_spin,spinK,unspin_cst,scaler0,add0r,subr0).
by rewrite unspin_sym ?scaler0 ?addr0 // mul_tr_vec_sym.
Qed.

Lemma tr_eskew a w : `e^(a, w)^T = `e^(a, - w).
Proof. by rewrite tr_emx3 tr_spin /emx3 spinN. Qed.

Lemma eskewM a b w : norm w = 1 -> `e^(a, w) * `e^(b, w) = `e^(a + b, w).
Proof. move=> w1; by rewrite emx3M // spin3 w1 expr1n scaleN1r. Qed.

Lemma trace_eskew a w : norm w = 1 -> \tr `e^(a, w) = 1 + 2%:R * cos a.
Proof.
move=> w1.
rewrite 2!mxtraceD !mxtraceZ /= mxtrace1.
rewrite (trace_anti (spin_is_so w)) mulr0 addr0 mxtrace_sqr_spin w1.
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

Lemma eskewE a u : norm u = 1 -> `e^(a, u) = angle_axis_rot a u.
Proof.
pose va := 1 - cos a. pose ca := cos a. pose sa := sin a.
move=> w1; apply/matrix3P/and9P; split; apply/eqP.
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  rewrite sqr_spin' !mxE /=.
  rewrite (_ : - _ - _ = u``_0 ^+ 2 - 1); last first.
    rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
  by rewrite !opprD !addrA subrr add0r addrC.
- rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
  by rewrite /va opprB addrC subrK.
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  by rewrite sqr_spin' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  by rewrite sqr_spin' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  by rewrite sqr_spin' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  rewrite sqr_spin' !mxE /=.
  rewrite (_ : - _ - _ = u``_1 ^+ 2 - 1); last first.
    rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
    by rewrite 2!opprD addrCA addrA subrK addrC.
  rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
  by rewrite /va opprB addrC subrK.
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  by rewrite sqr_spin' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  by rewrite sqr_spin' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  by rewrite sqr_spin' !mxE /= addrC mulrC (mulrC sa).
- rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !spinij; Simp.r => /=.
  rewrite sqr_spin' !mxE /=.
  rewrite (_ : - _ - _ = u``_2%:R ^+ 2 - 1); last first.
    rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
    by rewrite 2!opprD [in RHS]addrC subrK addrC.
  rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
  by rewrite /va opprB addrC subrK.
Qed.

Lemma eskew_is_O a u : norm u = 1 -> `e^(a, u) \is 'O[T]_3.
Proof.
move=> u1.
by rewrite orthogonalE tr_emx3 tr_spin inv_emx3 // exp_spin u1 expr1n scaleN1r.
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
rewrite mulmxE emx3M; last by rewrite spin3 w1 expr1n scaleN1r.
move/eqP; by rewrite halfP.
Qed.

Lemma eskew_is_SO a w : norm w = 1 -> `e^(a, w) \is 'SO[T]_3.
Proof. by move=> w1; rewrite rotationE eskew_is_O //= det_eskew. Qed.

Definition eskew_eigenvalues a : seq T[i] := [:: 1; expi a; expi (- a)].

Lemma eigenvalue_ekew a w : norm w = 1 ->
  eigenvalue (map_mx (fun x => x%:C%C) `e^(a, w)) =1
    [pred k | k \in eskew_eigenvalues a].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly.
rewrite /= !inE.
rewrite  char_poly3 /= trace_eskew // det_eskew //.
rewrite [`e(_,_) ^+ _]expr2 eskewM // trace_eskew //.
rewrite (_ : _ - _ = (1 + cos a *+ 2) *+ 2); last first.
  rewrite !mulr_natl cosD -!expr2 sin2cos2 [1 + _]addrC sqrrD1.
  rewrite exprMn_n -mulrnA opprB addrA -mulr2n mulrnBl 2!opprD opprK -mulrnA.
  rewrite addrA addrK addrAC addrA subrr add0r.
  by rewrite [RHS]mulrnDl addrC mulrnA.
rewrite -[(_ + _) *+ _]mulr_natl mulrA divfK ?(eqr_nat _ 2 0) // mul1r.
rewrite linearB /= map_polyC /= !(linearB, linearD, linearZ) /=.
rewrite !map_polyXn map_polyX.
  rewrite (_ : _ - _ = ('X - 1) * ('X - (expi a)%:P) * ('X - (expi (-a))%:P)).
  by rewrite !rootM !root_XsubC orbA.
have expiDexpiN  : expi a + expi (-a) = (cos a + cos a)%:C%C.
  rewrite !expi_cos_sin cosN sinN.
  by apply/eqP; rewrite eq_complex /= subrr !eqxx.
rewrite !(mulrBr, mulrBl, mulrDr, mulrDl, mul1r, mulr1).
rewrite -expr2 -exprSr !addrA !scalerN.
rewrite ['X * _ * 'X]mulrAC -expr2 !['X * _]mulrC !['X^2 * _]mulrC.
rewrite [_* 'X * _]mulrAC -rmorphM /= -expiD subrr expi0 mul1r.
rewrite -!addrA; congr (_ + _); rewrite !(addrA, opprB, opprD).
rewrite -[_ - _ * 'X^2]addrA -opprD -mulrDl -rmorphD /= expiDexpiN.
rewrite -[1 + _ + _]addrA ![_%:C%C]rmorphD /= scalerDl !(opprB, opprD).
rewrite -!addrA scale1r; congr (_ + _); rewrite !addrA opprK.
rewrite [RHS]addrC !addrA -mulrDl.
rewrite -[_%:P + _]rmorphD /= [expi (- _) + _]addrC expiDexpiN.
rewrite -![RHS]addrA [RHS]addrC -!addrA; congr (- _ + _).
  by rewrite -rmorphD /= mul_polyC.
rewrite scalerDl scale1r -!addrA; congr (_ + _).
by rewrite addrC mul_polyC.
Qed.

Lemma Rz_eskew a : Rz a = `e^(a, 'e_2%:R).
Proof.
rewrite /Rz eskewE /angle_axis_rot ?norm_delta_mx //.
rewrite !mxE /= expr0n /=. Simp.r.
by rewrite expr1n mul1r subrK -e2row.
Qed.

(* the w vector of e(phi,w) is an axis *)
Lemma axial_eskew a w : axial `e^(a, w) = sin a *+ 2 *: w.
Proof.
rewrite axialE unspinD unspin_eskew tr_eskew unspinN unspin_eskew scalerN.
by rewrite opprK -mulr2n scalerMnl.
Qed.

Section rodrigues_formula.

Definition rodrigues u a w :=
  u - (1 - cos a) *: (norm w ^+ 2 *: u) + (1 - cos a) * (u *d w) *: w + sin a *: (w *v u).

Lemma rodriguesP u a w : rodrigues u a w = u *m `e^(a, w).
Proof.
rewrite /rodrigues.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !spinE -!addrA; congr (_ + _).
rewrite !addrA.
rewrite [in X in _ = _ + X]crossmulC scalerN.
rewrite [in X in _ = _ - X]crossmulC.
rewrite double_crossmul dotmulvv.
rewrite scalerN opprK.
rewrite scalerBr [in RHS]addrA [in RHS]addrC -!addrA; congr (_ + (_ + _)).
by rewrite dotmulC scalerA.
Qed.

Definition rodrigues_unit u a w :=
  cos a *: u + (1 - cos a) * (u *d w) *: w + sin a *: (w *v u).

Lemma rodrigues_unitP u a w : norm w = 1 -> rodrigues_unit u a w = u *m `e^(a, w).
Proof.
move=> w1; rewrite -(rodriguesP u a w).
rewrite /rodrigues /rodrigues_unit w1 expr1n scale1r; congr (_ + _ + _).
by rewrite scalerBl opprB scale1r addrCA addrA addrK.
Qed.

End rodrigues_formula.

Lemma isRot_eskew_normalize a w : w != 0 -> isRot a w (mx_lin1 `e^(a, normalize w)).
Proof.
move=> w0.
pose f := Base.frame w.
apply/isRotP; split => /=.
- rewrite -rodriguesP // /rodrigues (norm_normalize w0) expr1n scale1r.
  rewrite dotmul_normalize_norm scalerA -mulrA divrr ?mulr1 ?unitfE ?norm_eq0 //.
  by rewrite subrK crossmulZv crossmulvv 2!scaler0 addr0.
- rewrite -rodriguesP // /rodrigues dotmulC norm_normalize // expr1n scale1r.
  rewrite (_ : normalize w = Base.i w) (*NB: lemma?*); last by rewrite /Base.i (negbTE w0).
  rewrite -Base.jE -Base.kE.
  rewrite Base.idotj // mulr0 scale0r addr0 -Base.icrossj /=  scalerBl scale1r.
  by rewrite opprB addrCA subrr addr0.
- rewrite -rodriguesP /rodrigues dotmulC norm_normalize // expr1n scale1r.
  rewrite (_ : normalize w = Base.i w) (*NB: lemma?*); last by rewrite /Base.i (negbTE w0).
  rewrite -Base.jE -Base.kE.
  rewrite Base.idotk // mulr0 scale0r addr0 scalerBl scale1r opprB addrCA subrr.
  rewrite addr0 addrC; congr (_ + _).
  by rewrite -/(Base.i w) Base.icrossk // scalerN scaleNr.
Qed.

Lemma isRot_eskew a w w' : normalize w' = w -> norm w = 1 -> isRot a w' (mx_lin1 `e^(a, w)).
Proof.
move=> <- w1.
by rewrite isRot_eskew_normalize // -normalize_eq0 -norm_eq0 w1 oner_eq0.
Qed.

Lemma eskew_is_onto_SO M : M \is 'SO[T]_3 ->
  { a | M = `e^(a, normalize (vaxis_euler M)) }.
Proof.
move=> MSO.
set w : vector := normalize _.
case: (SO_isRot MSO) => a Ha.
exists a.
apply: (@same_isRot _ _ _ _ _ (norm (vaxis_euler M)) _ _ _ _ Ha); last first.
  apply (@isRot_eskew _ _ w).
  by rewrite normalizeI // norm_normalize // vaxis_euler_neq0.
  by rewrite norm_normalize // vaxis_euler_neq0.
by rewrite norm_scale_normalize.
by rewrite norm_gt0 vaxis_euler_neq0.
by rewrite vaxis_euler_neq0.
Qed.

Section alternative_definition_of_eskew.

(* rotation of angle a around (unit) vector e *)
Definition eskew_unit (a : angle T) (e : 'rV[T]_3) :=
  e^T *m e + (cos a) *: (1 - e^T *m e) + sin a *: \S( e ).

Lemma eskew_unitE w (a : angle T) : norm w = 1 -> eskew_unit a w = `e^(a, w).
Proof.
move=> w1.
rewrite /eskew_unit /emx3 addrAC sqr_spin -addrA addrCA.
rewrite -[in RHS]addrA [in RHS]addrCA; congr (_ + _).
rewrite scalerBl scale1r addrCA -addrA; congr (_ + _).
rewrite scalerBr [in RHS]scalerBr opprB !addrA; congr (_ - _).
by rewrite addrC w1 expr1n !scalemx1 (addrC _ 1) subrr addr0.
Qed.

Local Open Scope frame_scope.

(* TODO: move? *)
Lemma normalcomp_double_crossmul p (e : 'rV[T]_3) : norm e = 1 ->
  normalcomp p e *v ((Base.frame e)|,2%:R *v (Base.frame e)|,1) = e *v p.
Proof.
move=> u1.
rewrite 2!rowframeE (crossmulC (row _ _)) SO_jcrossk; last first.
  by rewrite (col_mx3_rowE (NOFrame.M (Base.frame e))) -!rowframeE Base.is_SO.
rewrite -rowframeE Base.frame0E ?norm1_neq0 //.
rewrite normalizeI // {2}(axialnormalcomp p e) linearD /=.
by rewrite crossmul_axialcomp add0r crossmulC crossmulNv opprK.
Qed.

Lemma normalcomp_mulO' a Q u p : norm u = 1 -> isRot a u (mx_lin1 Q) ->
  normalcomp p u *m Q = cos a *: normalcomp p u + sin a *: (u *v p).
Proof.
move=> u1 H.
set v := normalcomp p u.
move: (orthogonal_expansion (Base.frame u) v).
set p0 := _|,0. set p1 := _|,1. set p2 := _|,2%:R.
rewrite (_ : (v *d p0) *: _ = 0) ?add0r; last first.
  by rewrite /p0 Base.frame0E ?norm1_neq0 // normalizeI // dotmul_normalcomp scale0r.
move=> ->.
rewrite mulmxDl -2!scalemxAl.
case/isRotP : H => /= _ -> ->.
rewrite -/p1 -/p2.
rewrite (scalerDr (normalcomp p u *d p1)) scalerA mulrC -scalerA.
rewrite [in RHS]scalerDr -!addrA; congr (_ + _).
rewrite (scalerDr (normalcomp p u *d p2)) addrA addrC.
rewrite scalerA mulrC -scalerA; congr (_ + _).
rewrite scalerA mulrC -scalerA [in X in _ + X = _]scalerA mulrC -scalerA.
rewrite scaleNr -scalerBr; congr (_ *: _).
by rewrite -double_crossmul normalcomp_double_crossmul.
Qed.

(* [angeles] p.42, eqn 2.49 *)
Lemma isRot_eskew_unit_inv a Q u : norm u = 1 ->
  isRot a u (mx_lin1 Q) -> Q = eskew_unit a u.
Proof.
move=> u1 H; apply/eqP/mulmxP => p.
rewrite (axialnormalcomp (p *m Q) u) axialcomp_mulO; last 2 first.
  exact/rotation_sub/(isRot_SO (norm1_neq0 u1) H).
  exact: isRot_axis H.
rewrite normalcomp_mulO //; last 2 first.
  exact/rotation_sub/(isRot_SO (norm1_neq0 u1) H).
  exact: isRot_axis H.
rewrite axialcompE u1 expr1n invr1 scale1r.
rewrite /eskew_unit -addrA mulmxDr mulmxA; congr (_ + _).
rewrite (@normalcomp_mulO' a) // mulmxDr.
rewrite -[in X in _ = _ + X]scalemxAr spinE; congr (_ + _).
by rewrite normalcompE u1 expr1n invr1 scale1r scalemxAr.
Qed.

Lemma isRot_eskew_unit e (e0 : e != 0) (a : angle T) :
  isRot a e (mx_lin1 (eskew_unit a (normalize e))).
Proof.
move: (isRot_eskew_normalize a e0); by rewrite eskew_unitE ?norm_normalize.
Qed.

Lemma axial_skew_unit (e : vector) a : axial (eskew_unit a e) = sin a *: e *+ 2.
Proof.
rewrite /eskew_unit 2!axialD (_ : axial _ = 0) ?add0r; last first.
  apply/eqP; by rewrite -axial_sym mul_tr_vec_sym.
rewrite (_ : axial _ = 0) ?add0r; last first.
  apply/eqP; rewrite -axial_sym sym_scaler_closed (* TODO: declare the right canonical to be able to use rpredZ *) //.
  by rewrite rpredD // ?sym_cst // rpredN mul_tr_vec_sym.
rewrite axialZ axialE scalerMnr; congr (_ *: _).
by rewrite unspinD spinK unspinN tr_spin unspinN spinK opprK mulr2n.
Qed.

(* [angeles], p.42, 2.50 *)
Lemma isRot_pi_inv (R : 'M[T]_3) u :
  u != 0 -> isRot pi u (mx_lin1 R) ->
  R = (normalize u)^T *m normalize u *+ 2 - 1.
Proof.
move=> u0 H.
have /isRot_eskew_unit_inv {H} : isRot pi (normalize u) (mx_lin1 R).
  by rewrite isRotZ // invr_gt0 norm_gt0.
rewrite norm_normalize // => /(_ erefl) ->.
by rewrite eskew_unitE ?norm_normalize // eskew_pi // norm_normalize.
Qed.

End alternative_definition_of_eskew.

End exponential_map_rot.

Notation "'`e(' a ',' M ')'" := (emx3 a M).
Notation "'`e^(' a ',' w ')'" := (emx3 a \S( w )).

Module Aa.
Section angle_of_angle_axis_representation.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Implicit Types M : 'M[T]_3.

Definition angle M := acos ((\tr M - 1) / 2%:R).

Lemma angle1 : angle 1 = 0.
Proof.
rewrite /angle mxtrace1 (_ : 3%:R - 1 = 2%:R); last first.
  by apply/eqP; rewrite subr_eq -(natrD _ 2 1).
by rewrite divrr ?unitfE ?pnatr_eq0 // acos1.
Qed.

(* reflection w.r.t. plan of normal u *)
Lemma anglepi (n : vector) (n1 : norm n = 1) : angle (n^T *m n *+ 2 - 1) = pi.
Proof.
rewrite /angle mxtraceD linearN /= mxtrace1 mulr2n linearD /=.
rewrite mxtrace_tr_mul n1 expr1n (_ : _ - 1 = - 2%:R); last first.
  by apply/eqP; rewrite -opprB eqr_opp opprB (_ : 1 + 1 = 2%:R) // -natrB.
by rewrite -mulr_natl mulNr divrr ?mulr1 ?unitfE ?pnatr_eq0 // acosN1.
Qed.

Lemma tr_angle M : angle M^T = angle M.
Proof. by rewrite /angle mxtrace_tr. Qed.

Lemma isRot_angle M u a : u != 0 -> a \in Opi_closed T ->
  isRot a u (mx_lin1 M) -> a = angle M.
Proof.
move=> u0 Ha.
move/(mxtrace_isRot u0); rewrite /angle => ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr ?mulr1 ?cosK //.
by rewrite unitfE pnatr_eq0.
Qed.

Lemma isRot_angleN M u a : u != 0 -> a \in piO_closed T ->
  isRot a u (mx_lin1 M) -> a = - angle M.
Proof.
move=> u0 Ha /(mxtrace_isRot u0); rewrite /angle=> ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr; last first.
  by rewrite unitfE pnatr_eq0.
by rewrite mulr1 cosKN // opprK.
Qed.

Lemma sym_angle M : M \is 'SO[T]_3 ->
  M \is sym 3 T -> angle M = 0 \/ angle M = pi.
Proof.
move=> MSO Msym.
case/eskew_is_onto_SO : (MSO) => a Ma.
move: (Msym).
rewrite {1}Ma /emx3.
rewrite symE !linearD /= trmx1 /= !linearZ /= sqr_spin !linearD /= !linearN /=.
rewrite trmx_mul trmxK scalemx1 tr_scalar_mx tr_spin.
rewrite !addrA subr_eq subrK.
rewrite [in X in _ == X]addrC -subr_eq0 !addrA !opprD !addrA addrK.
rewrite scalerN opprK -addrA addrCA !addrA (addrC _ 1) subrr add0r.
rewrite -mulr2n scalerMnl scaler_eq0 mulrn_eq0 /=.
rewrite -spin0 spin_inj -norm_eq0 norm_normalize ?vaxis_euler_neq0 // oner_eq0 orbF.
case/eqP/sin0_inv => [a0|api]; move: Ma.
- rewrite a0 emx30M => ->; rewrite angle1; by left.
- rewrite api -eskew_unitE ?norm_normalize // ?vaxis_euler_neq0 //.
  rewrite eskew_unitE ?norm_normalize // ?vaxis_euler_neq0 //.
  rewrite eskew_pi ?norm_normalize // ?vaxis_euler_neq0 // => ->.
  rewrite anglepi // ?norm_normalize // ?vaxis_euler_neq0 //.
  by right.
Qed.

Lemma tr_interval M : M \is 'SO[T]_3 -> -1 <= (\tr M - 1) / 2%:R <= 1.
Proof.
move=> MSO; case/SO_isRot : (MSO) => a HM.
case: (angle_in a).
- move/(isRot_angle (vaxis_euler_neq0 MSO))/(_ HM) => ?; subst a.
  move/(mxtrace_isRot (vaxis_euler_neq0 MSO)) : HM => ->.
  rewrite addrAC subrr add0r -(mulr_natl (cos _) 2) mulrC mulrA.
  by rewrite mulVr ?unitfE ?pnatr_eq0 // mul1r -ler_norml cos_max.
- move/(isRot_angleN (vaxis_euler_neq0 MSO))/(_ HM) => ?; subst a.
  move/(mxtrace_isRot (vaxis_euler_neq0 MSO)) : HM => ->.
  rewrite addrAC subrr add0r -(mulr_natl (cos _) 2) mulrC mulrA.
  by rewrite mulVr ?unitfE ?pnatr_eq0 // mul1r -ler_norml cos_max.
Qed.

(* NB: useful? *)
Lemma angle_Rx a :
  (a \in Opi_closed T -> angle (Rx a) = a) /\
  (a \in piO_closed T -> angle (Rx a) = - a).
Proof.
split => Ha; rewrite /angle mxtrace_Rx addrAC subrr add0r
  -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1;
  by [rewrite cosK | rewrite cosKN].
Qed.

Lemma angle_RO M a : M = block_mx (1 : 'M_1) 0 0 (RO a) ->
  (a \in Opi_closed T -> angle M = a) /\
  (a \in piO_closed T -> angle M = - a).
Proof.
move=> Ma.
rewrite /angle Ma (mxtrace_block (1 : 'M_1)) tr_RO mxtrace1 addrAC.
rewrite subrr add0r -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1.
split => Ha; by [rewrite cosK | rewrite cosKN].
Qed.

Lemma angle_eskew a u : norm u = 1 -> a \in Opi_closed T ->
  angle `e^(a, u) = a.
Proof.
move=> u1 Ha.
rewrite /angle trace_eskew // addrAC subrr add0r.
by rewrite mulrAC divrr ?mul1r ?unitfE // ?pnatr_eq0 // cosK.
Qed.

Lemma angle0_tr M : M \is 'SO[T]_3 -> angle M = 0 -> \tr M = 3%:R.
Proof.
move=> MSO /(congr1 (fun x => cos x)).
rewrite cos0 /angle acosK; last by apply tr_interval.
move/(congr1 (fun x => x * 2%:R)).
rewrite -mulrA mulVr ?unitfE ?pnatr_eq0 // mulr1 mul1r.
move/(congr1 (fun x => x + 1)).
rewrite subrK => ->; by rewrite (natrD _ 2 1).
Qed.

Lemma angle_pi_tr M : M \is 'SO[T]_3 -> angle M = pi -> \tr M = - 1.
Proof.
move=> MSO /(congr1 (fun x => cos x)).
rewrite cospi /angle acosK; last by apply tr_interval.
move/(congr1 (fun x => x * 2%:R)).
rewrite -mulrA mulVr ?unitfE ?pnatr_eq0 // mulr1.
move/(congr1 (fun x => x + 1)).
by rewrite subrK mulN1r mulr2n opprD subrK.
Qed.

Lemma SO_pi_reflection M : M \is 'SO[T]_3 -> angle M = pi ->
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

Lemma SO_pi_axial M : M \is 'SO[T]_3 -> angle M = pi -> axial M = 0.
Proof.
move=> MSO.
move/SO_pi_reflection => /(_ MSO) ->.
apply/eqP; rewrite -axial_sym rpredD // ?rpredN ?sym_cst //.
by rewrite mulr2n rpredD // mul_tr_vec_sym.
Qed.

Lemma rotation_is_Rx M k (k0 : 0 < k) : M \is 'SO[T]_3 ->
  axial M = k *: 'e_0 ->
  angle M \in Opi_closed T /\
  (M = Rx (- angle M) \/ M = Rx (angle M)).
Proof.
move=> MSO axialVi.
have [M02 M01] : M 0 2%:R = M 2%:R 0 /\ M 0 1 = M 1 0.
  move/matrixP/(_ 0 1) : (axialVi).
  rewrite !mxE /= mulr0 => /eqP; rewrite subr_eq add0r => /eqP ->.
  move/matrixP/(_ 0 2%:R) : (axialVi).
  by rewrite !mxE /= mulr0 => /eqP; rewrite subr_eq add0r => /eqP ->.
have axial_eigen : axial M *m M = axial M.
  move: (axial_vec_eigenspace MSO) => /eigenspaceP; by rewrite scale1r.
have [M010 [M020 M001]] : M 0 1 = 0 /\ M 0 2%:R = 0 /\ M 0 0 = 1.
  move: axial_eigen.
  rewrite axialVi -scalemxAl => /scalerI.
  rewrite gt_eqF // => /(_ isT) ViM.
  have : 'e_0 *m M = row 0 M by rewrite rowE.
  rewrite {}ViM => ViM.
  move/matrixP : (ViM) => /(_ 0 1); rewrite !mxE /= => <-.
  move/matrixP : (ViM) => /(_ 0 2%:R); rewrite !mxE /= => <-.
  by move/matrixP : (ViM) => /(_ 0 0); rewrite !mxE /= => <-.
have [P MP] : exists P : 'M[T]_2, M = block_mx (1 : 'M_1) 0 0 P.
  exists (@drsubmx _ 1 2 1 2 M).
  rewrite -{1}(@submxK _ 1 2 1 2 M).
  rewrite (_ : ulsubmx _ = 1); last first.
    apply/matrixP => i j.
    rewrite (ord1 i) (ord1 j) !mxE /= -M001 mulr1n; congr (M _ _); by apply val_inj.
  rewrite (_ : ursubmx _ = 0); last first.
    apply/rowP => i.
    case/boolP : (i == 0) => [|/ifnot01P]/eqP->;
      [ rewrite !mxE -[RHS]M010; congr (M _ _); exact: val_inj |
        rewrite !mxE -[RHS]M020; congr (M _ _); exact: val_inj ].
  rewrite (_ : dlsubmx _ = 0) //.
  apply/colP => i.
  case/boolP : (i == 0) => [|/ifnot01P]/eqP->;
    [ rewrite !mxE -[RHS]M010 M01; congr (M _ _); exact: val_inj |
      rewrite !mxE -[RHS]M020 M02; congr (M _ _); exact: val_inj ].
have PSO : P \is 'SO[T]_2 by have := MSO; rewrite MP (SOSn_SOn 1).
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

Section axis_of_angle_axis_representation.

Variable T : rcfType.
Let vector := 'rV[T]_3.

Definition naxial a (M : 'M[T]_3) := ((sin a) *+ 2)^-1 *: axial M.

Lemma naxial_eskew a w : sin a != 0 -> naxial a `e^(a, w) = w.
Proof.
move=> sa.
by rewrite /naxial axial_eskew scalerA mulVr ?unitfE ?mulrn_eq0 // scale1r.
Qed.

Definition vaxis M : 'rV[T]_3 :=
  if angle M == pi then vaxis_euler M else naxial (angle M) M.

Lemma vaxis_neq0 (M : 'M[T]_3) : M \is 'SO[T]_3 ->
  angle M != 0 -> vaxis M != 0.
Proof.
move=> MSO a0.
case/boolP : (Aa.angle M == pi) => [/eqP api|api].
  by rewrite /vaxis api eqxx vaxis_euler_neq0.
case/boolP : (axial M == 0) => M0.
  rewrite -axial_sym in M0.
  case: (Aa.sym_angle MSO M0) => /eqP.
    by rewrite (negbTE a0).
  by rewrite (negbTE api).
rewrite /vaxis (negbTE api) scaler_eq0 negb_or M0 andbT.
by rewrite invr_eq0 mulrn_eq0 /= sin_eq0 negb_or a0 api.
Qed.

Lemma vaxis_eskew a (w : vector) :
  sin a != 0 -> a \in Opi_closed T -> norm w = 1 ->
  vaxis `e^(a, w) = w.
Proof.
move=> sphi Ha w1.
rewrite /vaxis angle_eskew //.
move: (sphi).
rewrite sin_eq0 negb_or => /andP[_]/negbTE ->.
by rewrite naxial_eskew.
Qed.

Lemma vaxis_ortho_of_iso (M : 'M[T]_3) (MSO : M \is 'SO[T]_3) :
  vaxis M *m M = vaxis M.
Proof.
rewrite /vaxis.
case: ifPn => [_|pi]; first by apply/eqP; rewrite vaxis_eulerP.
move/axial_vec_eigenspace : MSO => /eigenspaceP.
rewrite -scalemxAl => ->; by rewrite scale1r.
Qed.

Lemma isRot_axis (M : 'M[T]_3) u a : u != 0 -> sin a != 0 ->
  isRot a u (mx_lin1 M) ->
  normalize u = naxial a M.
Proof.
move=> u0 sina0 H.
suff -> : M = `e^(a, normalize u) by rewrite naxial_eskew.
apply: (@same_isRot _ _ _ _ _ 1 u0 _ a) => //.
by rewrite scale1r.
exact: (isRot_eskew_normalize _ u0).
Qed.

End axis_of_angle_axis_representation.
End Aa.

Section angle_axis_of_rot.

Variable T : rcfType.
Let vector := 'rV[T]_3.

Definition log_rot (M : 'M[T]_3) : angle T * 'rV[T]_3 :=
  (Aa.angle M, Aa.vaxis M).

Lemma log_exp_eskew (a : angle T) (w : 'rV[T]_3) :
  sin a != 0 -> a \in Opi_closed T -> norm w = 1 ->
  log_rot `e^(a, w) = (a, w).
Proof.
move=> ? ? ?; congr pair; by [rewrite Aa.angle_eskew | rewrite Aa.vaxis_eskew].
Qed.

Lemma angle_vaxis_eskew M : M \is 'SO[T]_3 ->
  M = `e^(Aa.angle M, normalize (Aa.vaxis M)).
Proof.
move=> MSO; case/boolP : (axial M == 0) => [|M0].
  rewrite -axial_sym => M0'.
  case/(Aa.sym_angle MSO) : (M0') => [a0|api].
    rewrite a0 emx30M.
    move/(Aa.angle0_tr MSO): a0.
    move/O_tr_idmx => M1; by rewrite {1}M1 ?rotation_sub.
  move/(Aa.SO_pi_reflection MSO) : (api) => api'.
  by rewrite /Aa.vaxis api eqxx eskew_pi // norm_normalize // vaxis_euler_neq0.
case/boolP : (Aa.angle M == 0) => [/eqP H|a0].
  rewrite H.
  move/(Aa.angle0_tr MSO) : H.
  move/O_tr_idmx => ->; by rewrite ?rotation_sub // emx30M.
case/boolP : (Aa.angle M == pi) => [/eqP H|api].
  rewrite H eskew_pi ?norm_normalize // /Aa.vaxis H eqxx ?vaxis_euler_neq0 //.
  exact: Aa.SO_pi_reflection.
have sina0 : sin (Aa.angle M) != 0.
  apply: contra a0 => /eqP/sin0_inv [->//|/eqP]; by rewrite (negbTE api).
set w : 'rV_3 := normalize _.
have [a Rota] := SO_isRot MSO.
have {}Rota : isRot a (normalize (vaxis_euler M)) (mx_lin1 M).
  by rewrite (isRotZ a _ (vaxis_euler_neq0 MSO)) // invr_gt0 norm_gt0 vaxis_euler_neq0.
have w0 : normalize (vaxis_euler M) != 0 by rewrite normalize_eq0 vaxis_euler_neq0.
have w1 : norm w = 1 by rewrite norm_normalize // Aa.vaxis_neq0.
case: (angle_in a) => Ha.
- move: (Aa.isRot_angle w0 Ha Rota) => a_angle_of_rot.
  rewrite a_angle_of_rot in Rota.
  move: (Aa.isRot_axis w0 sina0 Rota) => w'axial.
  rewrite /Aa.naxial in w'axial.
  set k := (_^-1) in w'axial.
  have k0 : 0 < k.
    rewrite /k invr_gt0 pmulrn_lgt0 // lt_neqAle eq_sym sina0 /=.
    by rewrite inE a_angle_of_rot in Ha.
  apply: (@same_isRot _ _ _ _ (norm (Aa.vaxis M) *: w) ((sin (Aa.angle M) *+ 2) * k) w0 _ (Aa.angle M) _ Rota).
  - by rewrite pmulr_rgt0 // pmulrn_lgt0 // lt_neqAle eq_sym sina0 -a_angle_of_rot.
  - rewrite -(norm_scale_normalize (normalize (vaxis_euler M))).
    rewrite norm_normalize ?vaxis_euler_neq0 // w'axial.
    rewrite scale1r {2}/k divrr ?unitfE ?mulrn_eq0 //= scale1r.
    by rewrite /w norm_scale_normalize /Aa.vaxis (negbTE api).
  - rewrite isRot_eskew // normalizeZ ?normalizeI // -?norm_eq0 ?w1 ?oner_neq0 //.
    by rewrite norm_gt0 ?Aa.vaxis_neq0.
- move: (Aa.isRot_angleN w0 Ha Rota) => a_angle_of_rot.
  have : M \in unitmx by rewrite orthogonal_unit // rotation_sub // -rotationV.
  move/(@isRot_tr _ _ (Aa.angle M^T) w0 M).
  rewrite {1}Aa.tr_angle -a_angle_of_rot => /(_ Rota).
  rewrite (rotation_inv MSO) Aa.tr_angle.
  move/(Aa.isRot_axis w0 sina0) => w'axial.
  rewrite /Aa.naxial in w'axial.
  set k := (_ ^-1 ) in w'axial.
  have k0 : 0 < k.
    rewrite /k invr_gt0 pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  apply: (@same_isRot _ _ _ _ (- norm (Aa.vaxis M) *: w) ((sin (Aa.angle M) *+ 2) * k) w0 _ (- Aa.angle M)).
  - rewrite pmulr_rgt0 // pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  - rewrite -(norm_scale_normalize (normalize (vaxis_euler M))).
    rewrite norm_normalize ?vaxis_euler_neq0 // w'axial.
    rewrite scale1r {2}/k divrr ?unitfE ?mulrn_eq0 //= scale1r.
    rewrite /w scaleNr norm_scale_normalize /Aa.vaxis (negbTE api).
    by rewrite tr_axial scalerN.
  - by rewrite -a_angle_of_rot.
  - rewrite isRotZN.
    by rewrite opprK isRot_eskew // normalizeI.
    by rewrite -norm_eq0 w1 oner_neq0.
    by rewrite oppr_lt0 norm_gt0 // Aa.vaxis_neq0.
Qed.

Lemma angle_axis_isRot (Q : 'M[T]_3) : axial Q != 0 ->
  Q \is 'SO[T]_3 ->
  isRot (Aa.angle Q) (normalize (Aa.vaxis Q)) (mx_lin1 Q).
Proof.
move=> Q0 QSO.
move/angle_vaxis_eskew : (QSO) => H.
case/boolP : (Aa.angle Q == 0) => [|a0].
  move/eqP/(Aa.angle0_tr QSO).
  move/(O_tr_idmx (rotation_sub QSO)) => Q1; subst Q.
  rewrite Aa.angle1; by apply isRot1.
case/boolP : (Aa.angle Q == pi) => [api|api].
  move/eqP/(Aa.SO_pi_reflection QSO) : (api) => HQ.
  rewrite /Aa.vaxis api (eqP api) {2}HQ.
  apply isRotpi; by rewrite norm_normalize // vaxis_euler_neq0.
move=> [:vaxis0].
rewrite {3}H isRotZ; last 2 first.
  abstract: vaxis0.
  rewrite /Aa.vaxis (negbTE api) scaler_eq0 negb_or Q0 andbT.
  by rewrite invr_eq0 mulrn_eq0 /= sin_eq0 negb_or a0 api.
  by rewrite invr_gt0 norm_gt0.
exact: isRot_eskew_normalize.
Qed.

End angle_axis_of_rot.

Section angle_axis_representation.

Variable T : rcfType.
Let vector := 'rV[T]_3.

Record angle_axis := AngleAxis {
  angle_axis_val : angle T * vector ;
  _ : norm (angle_axis_val.2) == 1 }.

Canonical angle_axis_subType := [subType for angle_axis_val].

Definition aangle (a : angle_axis) := (val a).1.
Definition aaxis (a : angle_axis) := (val a).2.

Lemma norm_axis a : norm (aaxis a) = 1.
Proof. by case: a => *; apply/eqP. Qed.

Fact norm_e1_subproof : norm (@delta_mx T _ 3 0 0) == 1.
Proof. by rewrite norm_delta_mx. Qed.

Definition angle_axis_of (a : angle T) (v : vector) :=
  insubd (@AngleAxis (a,_) norm_e1_subproof) (a, normalize v).

Lemma aaxis_of (a : angle T) (v : vector) : v != 0 ->
  aaxis (angle_axis_of a v) = normalize v.
Proof.
move=> v_neq0 /=; rewrite /angle_axis_of /aaxis val_insubd /=.
by rewrite normZ normfV normr_norm mulVf ?norm_eq0 // eqxx.
Qed.

Lemma aangle_of (a : angle T) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

(*Coercion exp_skew_of_angle_axis r :=
  let (a, w) := (aangle r, aaxis r) in `e^(a, w).*)

Definition angle_axis_of_rot M := angle_axis_of (Aa.angle M) (Aa.vaxis M).

Lemma angle_axis_eskew_old M : M \is 'SO[T]_3 ->
  Aa.vaxis M != 0 ->
  let a := aangle (angle_axis_of_rot M) in
  let w := aaxis (angle_axis_of_rot M) in
  M = `e^(a, w).
Proof.
move=> MSO M0 a w.
rewrite (angle_vaxis_eskew MSO) /a aangle_of; congr (`e^(_, _)).
by rewrite /w /angle_axis_of_rot /= aaxis_of.
Qed.

End angle_axis_representation.

(* NB: work in progress *)
Section properties_of_orthogonal_matrices.

Variables (T : rcfType) (M : 'M[T]_3).
Hypothesis MO : M \is 'O[T]_3.

Lemma sqr_Mi0E i : M i 1 ^+ 2 + M i 2%:R ^+ 2 = 1 - M i 0 ^+ 2.
Proof.
move/norm_row_of_O : MO => /(_ i)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite -addrA addrC eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_Mi1E i : M i 0 ^+ 2 + M i 2%:R ^+ 2 = 1 - M i 1 ^+ 2.
Proof.
move/norm_row_of_O : MO => /(_ i)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite addrAC eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_Mi2E i : M i 0 ^+ 2 + M i 1 ^+ 2 = 1 - M i 2%:R ^+ 2.
Proof.
move/norm_row_of_O : MO => /(_ i)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_M2jE j : M 0 j ^+ 2 + M 1 j ^+ 2 = 1 - M 2%:R j ^+ 2.
Proof.
move/norm_col_of_O : MO => /(_ j)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite eq_sym -subr_eq => /eqP <-.
Qed.

Lemma sqr_M0jE j : M 1 j ^+ 2 + M 2%:R j ^+ 2 = 1 - M 0 j ^+ 2.
Proof.
move/norm_col_of_O : MO => /(_ j)/(congr1 (fun x => x ^+ 2)).
rewrite -dotmulvv dotmulE sum3E !mxE -!expr2 expr1n => /eqP.
by rewrite -addrA addrC eq_sym -subr_eq => /eqP <-.
Qed.

Lemma Mi2_1 i : (`| M i 2%:R | == 1) = (M i 0 == 0) && (M i 1 == 0).
Proof.
move/eqP: (sqr_Mi2E i) => MO'.
apply/idP/idP => [Mi2|/andP[/eqP Mi0 /eqP Mi1]]; last first.
  move: MO'; by rewrite Mi0 Mi1 expr2 mulr0 addr0 eq_sym subr_eq add0r eq_sym sqr_norm_eq1.
move: MO'; rewrite -(sqr_normr (M i 2%:R)) (eqP Mi2) expr1n subrr.
by rewrite paddr_eq0 ?sqr_ge0 // => /andP[]; rewrite 2!sqrf_eq0 => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Lemma M0j_1 j : (`| M 0 j | == 1) = (M 1 j == 0) && (M 2%:R j == 0).
Proof.
move/eqP: (sqr_M2jE j) => MO'.
apply/idP/idP => [M0j|/andP[/eqP Mi0 /eqP Mi1]]; last first.
  by move: MO'; rewrite Mi0 Mi1 expr0n addr0 subr0 sqr_norm_eq1.
move: MO'; rewrite -(sqr_normr (M 0 j)) (eqP M0j) expr1n.
rewrite -subr_eq opprK -addrA addrC eq_sym -subr_eq subrr eq_sym.
by rewrite paddr_eq0 ?sqr_ge0 // 2!sqrf_eq0.
Qed.

Lemma M1j_1 j : (`| M 1 j | == 1) = (M 0 j == 0) && (M 2%:R j == 0).
Proof.
move/eqP: (sqr_M2jE j) => MO'.
apply/idP/idP => [M0j|/andP[/eqP Mi0 /eqP Mi1]]; last first.
  by move: MO'; rewrite Mi0 Mi1 expr0n add0r subr0 sqr_norm_eq1.
move: MO'; rewrite -(sqr_normr (M 1 j)) (eqP M0j) expr1n.
rewrite eq_sym -subr_eq addrAC subrr add0r eq_sym -subr_eq0 opprK.
by rewrite paddr_eq0 ?sqr_ge0 // 2!sqrf_eq0.
Qed.

Lemma M2j_1 j :(`| M 2%:R j | == 1) = (M 0 j == 0) && (M 1 j == 0).
Proof.
move/eqP: (sqr_M2jE j) => MO'.
apply/idP/idP => [Mi2|/andP[/eqP Mi0 /eqP Mi1]]; last first.
  move: MO'; by rewrite Mi0 Mi1 expr2 mulr0 addr0 eq_sym subr_eq add0r eq_sym sqr_norm_eq1.
move: MO'; rewrite -(sqr_normr (M 2%:R j)) (eqP Mi2) expr1n subrr.
by rewrite paddr_eq0 ?sqr_ge0 // => /andP[]; rewrite 2!sqrf_eq0 => /eqP -> /eqP ->; rewrite eqxx.
Qed.

End properties_of_orthogonal_matrices.

(* wip *)
Section euler_angles.

Variables (T : rcfType).

Implicit Types R : 'M[T]_3.

Local Open Scope frame_scope.

(* two orthogonal vectors belonging to the plan (y,z) projected on y and z *)
Lemma exists_rotation_angle (F : frame T) (u v : 'rV[T]_3) :
  norm u = 1 -> norm v = 1 -> u *d v = 0 -> u *v v = F|,0 ->
  { w : angle T | u = cos w *: (F|,1) + sin w *: (F|,2%:R) /\
                  v = - sin w *: (F|,1) + cos w *: (F|,2%:R) }.
Proof.
move=> normu normv u_perp_v uva0.
have u0 : u *d F|,0 = 0 by rewrite -uva0 dot_crossmulC crossmulvv dotmul0v.
have v0 : v *d F|,0 = 0 by rewrite -uva0 dot_crossmulCA crossmulvv dotmulv0.
case/boolP : (u *d F|,2%:R == 0) => [/eqP|] u2.
  suff [?|?] : {u = F|,1 /\ v = F|,2%:R} + {u = - F|,1 /\ v = - F|,2%:R}.
  - exists 0; by rewrite sin0 cos0 !(scale1r,oppr0,scale0r,addr0,add0r).
  - exists pi; by rewrite sinpi cospi !(scaleN1r,scale0r,oppr0,add0r,addr0).
  have v1 : v *d F|,1 = 0.
    move/eqP: (frame_icrossk F); rewrite -eqr_oppLR => /eqP <-.
    rewrite dotmulvN -uva0 crossmulC dotmulvN opprK double_crossmul.
    rewrite dotmulDr dotmulvN (dotmulC _ u) u2 scale0r dotmulv0 subr0.
    by rewrite dotmulvZ (dotmulC v) u_perp_v mulr0.
  rewrite (orthogonal_expansion F u) (orthogonal_expansion F v).
  rewrite u2 u0 v0 v1 !(scale0r,addr0,add0r).
  have [/eqP u1 | /eqP u1] : {u *d F |, 1 == 1} + {u *d F|,1 == -1}.
    move: normu => /(congr1 (fun x => x ^+ 2)); rewrite (sqr_norm_frame F u).
    rewrite sum3E u0 u2 expr0n add0r addr0 expr1n => /eqP.
    by rewrite sqrf_eq1 => /Bool.orb_true_elim.
  - have v2 : v *d F|,2%:R = 1.
      move: uva0.
      rewrite {1}(orthogonal_expansion F u) u0 u1 u2 !(scale0r,add0r,scale1r,addr0).
      rewrite {1}(orthogonal_expansion F v) v0 v1 !(scale0r,add0r) crossmulvZ.
      rewrite (frame_jcrossk F) => /scaler_eq1; apply.
      by rewrite -norm_eq0 noframe_norm oner_eq0.
    rewrite v2 u1 !scale1r; by left.
  - have v2 : v *d F|,2%:R = -1.
      move: uva0.
      rewrite {1}(orthogonal_expansion F u) u0 u1 u2 !(scale0r,add0r,scale1r,addr0,scaleN1r).
      rewrite {1}(orthogonal_expansion F v) v0 v1 !(scale0r,add0r,scale1r,addr0,scaleN1r).
      rewrite crossmulNv crossmulvZ (frame_jcrossk F) -scaleNr => /scaler_eqN1; apply.
      by rewrite -norm_eq0 noframe_norm oner_eq0.
    rewrite v2 u1 !scaleN1r; by right.
case/boolP : (u *d F|,1 == 0) => [/eqP|] u1.
  have {u2}[/eqP u2|/eqP u2] : {u *d F|,2%:R == 1} + {u *d F|,2%:R == -1}.
    move: normu => /(congr1 (fun x => x ^+ 2)).
    rewrite (sqr_norm_frame F u) sum3E u0 u1 expr0n !add0r expr1n => /eqP.
    by rewrite sqrf_eq1 => /Bool.orb_true_elim.
  + have v1 : v *d F|,1%:R = -1.
      move: uva0.
      rewrite {1}(orthogonal_expansion F u) u0 u1 u2 !(scale0r,add0r,scale1r,scaleN1r).
      rewrite {1}(orthogonal_expansion F v) v0 !(scale0r,add0r,scale1r,addr0).
      rewrite crossmulDr crossmulvZ crossmulC (frame_jcrossk F).
      rewrite crossmulvZ crossmulvv scaler0 addr0 scalerN -scaleNr => /scaler_eqN1; apply.
      by rewrite -norm_eq0 noframe_norm oner_eq0.
    have v2 : v *d F|,2%:R = 0.
      move: normv => /(congr1 (fun x => x ^+ 2)).
      rewrite expr1n (sqr_norm_frame F) sum3E v1 v0 expr0n add0r sqrrN expr1n => /eqP.
      by rewrite eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
    exists (pihalf T).
    rewrite cos_pihalf sin_pihalf !(scale0r,add0r,scale1r,scaleN1r,addr0).
    rewrite (orthogonal_expansion F u) (orthogonal_expansion F v).
    by rewrite u1 u0 u2 v1 v0 v2 !(scale0r,addr0,add0r,scale1r,scaleN1r).
  + have v1 : v *d F|,1 = 1.
      move: uva0.
      rewrite {1}(orthogonal_expansion F u) u0 u1 u2 !(scale0r,add0r,scaleN1r).
      rewrite {1}(orthogonal_expansion F v) v0 !(scale0r,add0r,scaleN1r).
      rewrite crossmulDr !crossmulNv !crossmulvZ crossmulvv scaler0 subr0.
      rewrite -scalerN crossmulC opprK (frame_jcrossk F) => /scaler_eq1; apply.
      by rewrite -norm_eq0 noframe_norm oner_eq0.
    have v2 : v *d F|,2%:R = 0.
      move: normv => /(congr1 (fun x => x ^+ 2)).
      rewrite expr1n (sqr_norm_frame F) sum3E v1 v0 expr0n add0r expr1n => /eqP.
      by rewrite eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
    exists (- pihalf T).
    rewrite cosN sinN cos_pihalf sin_pihalf ?(scale0r,add0r,scale1r,scaleN1r,addr0,opprK).
    rewrite (orthogonal_expansion F u) (orthogonal_expansion F v).
    by rewrite u1 u0 u2 v1 v0 v2 !(scale0r,addr0,add0r,scale1r,scaleN1r).
move: (orthogonal_expansion F u).
rewrite -{1}uva0 dot_crossmulC crossmulvv dotmul0v scale0r add0r => Hr2.
move: (orthogonal_expansion F v).
rewrite -{1}uva0 crossmulC dotmulvN dot_crossmulC crossmulvv dotmul0v oppr0 scale0r add0r => Hr3.
have [w [Hw1 Hw2]] : {w : angle T | u *d F|,1 = cos w /\ (u *d F|,2%:R) = sin w}.
  apply sqrD1_cossin.
  move/(congr1 (fun x => norm x)) : Hr2.
  rewrite normu.
  move/(congr1 (fun x => x ^+ 2)).
  rewrite expr1n normD !normZ ?noframe_norm !mulr1.
  rewrite (_ : cos _ = 0); last first.
    case: (lerP 0 (u *d F|,2%:R)).
      rewrite le_eqVlt eq_sym (negbTE u2) /= => {}u2.
      case: (lerP 0 (u *d F|,1)).
        rewrite le_eqVlt eq_sym (negbTE u1) /= => {}u1.
        rewrite vec_anglevZ; last by [].
        rewrite vec_angleZv; last by [].
        by rewrite /cos /vec_angle noframe_jdotk frame_jcrossk noframe_norm expii.
      move=> {}u1.
        rewrite vec_angleZNv; last by [].
        rewrite vec_anglevZ; last by [].
        rewrite cos_vec_angleNv; last 2 first.
          by rewrite -norm_eq0 noframe_norm oner_neq0.
          by rewrite -norm_eq0 noframe_norm oner_neq0.
        by rewrite /cos /vec_angle noframe_jdotk frame_jcrossk noframe_norm expii oppr0.
      move=> {}u2.
      case: (lerP 0 (u *d F|,1)).
        rewrite le_eqVlt eq_sym (negbTE u1) /= => {}u1.
        rewrite vec_angleZv; last by [].
        rewrite vec_anglevZN; last by [].
        by rewrite /cos /vec_angle dotmulvN noframe_jdotk oppr0 crossmulvN normN frame_jcrossk noframe_norm expii.
      move=> {}u1.
      rewrite vec_anglevZN; last by [].
      rewrite vec_angleZNv; last by [].
        rewrite cos_vec_angleNv; last 2 first.
          by rewrite -norm_eq0 noframe_norm oner_neq0.
          by rewrite oppr_eq0 -norm_eq0 noframe_norm oner_neq0.
        rewrite cos_vec_anglevN; last 2 first.
          by rewrite -norm_eq0 noframe_norm oner_neq0.
          by rewrite -norm_eq0 noframe_norm oner_neq0.
        by rewrite opprK /cos /vec_angle noframe_jdotk frame_jcrossk noframe_norm expii.
  by rewrite mulr0 mul0rn addr0 !sqr_normr.
have uRv : u *m `e^(pihalf T, F|,0) = v.
  rewrite -rodriguesP /rodrigues noframe_norm ?expr1n scale1r cos_pihalf subr0.
  rewrite scale1r mul1r sin_pihalf scale1r subrr add0r -uva0 dot_crossmulC.
  rewrite crossmulvv dotmul0v scale0r add0r crossmulC double_crossmul dotmulvv.
  by rewrite normu expr1n scale1r opprB u_perp_v scale0r subr0.
have RO : `e^(pihalf T, F|,0) \in 'O[T]_3 by apply eskew_is_O; rewrite noframe_norm.
have H' : vec_angle u F|,2%:R = vec_angle v (- F|,1).
  move/orth_preserves_vec_angle : RO => /(_ u F|,2%:R) <-.
  rewrite uRv; congr (vec_angle v _).
  rewrite -rodriguesP /rodrigues noframe_norm ?expr1n scale1r cos_pihalf subr0.
  rewrite scale1r mul1r sin_pihalf scale1r subrr add0r.
  by rewrite dotmulC noframe_idotk scale0r add0r frame_icrossk.
have H : vec_angle u (F |, 1) = vec_angle v (F|,2%:R).
  move/orth_preserves_vec_angle : RO => /(_ u F|,1) <-.
  rewrite uRv; congr (vec_angle v _).
  rewrite -rodriguesP /rodrigues noframe_norm ?expr1n scale1r cos_pihalf subr0.
  rewrite scale1r mul1r sin_pihalf scale1r subrr add0r.
  by rewrite dotmulC noframe_idotj scale0r add0r frame_icrossj.
exists w; rewrite -{1}Hw1 -{1}Hw2.
split; first by [].
have <- : v *d F|,1 = - sin w.
  rewrite -Hw2 2!dotmul_cos normu 2!noframe_norm mul1r normv mulr1.
  rewrite [in LHS]mul1r [in RHS]mul1r ?opprK H'.
  rewrite [in RHS]cos_vec_anglevN ?opprK; [by [] | | ].
  by rewrite -norm_eq0 normv oner_neq0.
  by rewrite -norm_eq0 noframe_norm oner_neq0.
have <- : v *d F|,2%:R = cos w.
  by rewrite -Hw1 2!dotmul_cos normu 2!noframe_norm mul1r normv mulr1 H.
by [].
Qed.

Lemma euler_angles_zyx_RO (a1 a2 u v : 'rV[T]_3) w1 k k' :
  norm u = 1 -> norm v = 1 -> u *d v = 0 ->
  norm a1 = 1 -> norm a2 = 1 -> a1 *d a2 = 0 ->
  u = k *: a1 + k' *: a2 ->
  v = - k' *: a1 + k *: a2 ->
  cos w1 = a1 *d u ->
  sin w1 = - a2 *d u ->
  row_mx u^T v^T = row_mx a1^T a2^T *m RO w1.
Proof.
move=> u1 v1 uv a1_1 a2_1 a1a2 Hu Hv Hcos Hsin.
move: uv.
rewrite {1}Hu {1}Hv.
rewrite dotmulDr 2!dotmulDl !(dotmulZv,dotmulvZ) (dotmulC a2 a1) a1a2.
rewrite !(mulr0,addr0,add0r) 2!dotmulvv a1_1 a2_1 expr1n 2!mulr1.
move=> kk'.
move: Hsin; rewrite {1}Hu dotmulDr !(dotmulZv,dotmulvZ) !dotmulNv dotmulC a1a2.
rewrite oppr0 mulr0 add0r mulrN dotmulvv a2_1 expr1n mulr1 => Hsin.
move: Hcos; rewrite {1}Hu dotmulDr !(dotmulZv,dotmulvZ) dotmulvv.
rewrite a1_1 expr1n mulr1 a1a2 mulr0 addr0 => Hcos.
move/eqP : Hsin; rewrite -eqr_oppLR => /eqP Hsin.
subst k k'.
move: u1 => /(congr1 (fun x => x^+2)).
rewrite {1}Hu.
rewrite -dotmulvv dotmulDr 2!dotmulDl !dotmulZv!dotmulvZ !dotmulvv a1_1 a2_1 !expr1n mulr1.
rewrite a1a2 !mulr0 add0r mulr1 dotmulC a1a2 !mulr0 addr0 => u_1.
move: v1 => /(congr1 (fun x => x^+2)).
rewrite {1}Hv.
rewrite -dotmulvv dotmulDr 2!dotmulDl !dotmulZv!dotmulvZ !dotmulvv a1_1 a2_1 !expr1n mulr1.
rewrite a1a2 !mulr0 add0r mulr1 dotmulC a1a2 !mulr0 addr0 => v_1.
rewrite -2!expr2 in v_1.
case/sqrD1_cossin : v_1 => w1' [Hcos Hsin].
rewrite opprK in Hcos.
move: kk'.
rewrite opprK mulNr => _.
by rewrite Hu Hv mul_col_mx2 !mxE /= !linearD /= !linearZ /= !mul_mx_scalar opprK.
Qed.

Lemma euler_zyx_angles R : R \is 'SO[T]_3 ->
  let w2 := asin (R 2%:R 0) in
  0 < cos w2 ->
  forall w3 w1,
    cos w3 = R 0 0 * (cos w2)^-1 ->
    sin w3 = - R 1%:R 0 * (cos w2)^-1 ->
    cos w1 = (col 1 (Rzy w3 w2))^T *d (col 1 R)^T ->
    sin w1 = - (col 2%:R (Rzy w3 w2))^T *d (col 1 R)^T ->
    R = Rz w3 * Ry w2 * Rx w1.
Proof.
move=> RSO w2 cos_w2_ge0 w3 w1 Hw3 Kw3 Hw1 Kw1.
rewrite RzyE.
set A := Rzy _ _.
set a1 := col 0 A. set a2 := col 1 A. set a3 := col 2%:R A.
have Ha1 : a1 = col 0 R.
  apply/matrixP => a b.
  rewrite !mxE /=.
  case: ifPn => [/eqP ->{a}|A0].
    by rewrite !mxE /= Hw3 -mulrA mulVr ?mulr1 // unitfE gt_eqF.
  case: ifPn => [/eqP ->|A1].
    by rewrite !mxE /= Kw3 !mulNr opprK -mulrA mulVr ?mulr1 // unitfE gt_eqF.
  rewrite -(negbK (a == 2%:R)) ifnot2 negb_or A0 A1 /= !mxE /= /w2 asinK.
  suff /eqP -> : a == 2%:R by [].
  by apply/negPn; rewrite ifnot2 negb_or A0.
  by rewrite -ler_norml Oij_ub // rotation_sub.
have Hw2 : sin w2 = R 2%:R 0.
  move/(congr1 (fun v : 'cV_3 => v 2%:R 0)) : Ha1; by rewrite !mxE.
rewrite -(row_mx_colE R).
transitivity (row_mx (col 0 R) (row_mx a2 a3) *m Rx w1).
  rewrite Rx_RO.
  rewrite (mul_row_block _ _ 1) mulmx0 add0r mulmx1 mulmx0 addr0.
  congr (row_mx (col 0 R)).
  rewrite (_ : col 1 R = (row 1 R^T)^T); last by rewrite ?tr_row ?trmxK.
  rewrite (_ : col 2%:R R = (row 2%:R R^T)^T); last by rewrite ?tr_row ?trmxK.
  rewrite -(trmxK a2).
  rewrite -(trmxK a3).
  have [k [k' [Hr2 Hr3]]] : exists k k',
    col 1 R = k *: a2 + k' *: a3 /\ col 2%:R R = - k' *: a2 + k *: a3.
    set r2 := col 1 R.
    set r3 := col 2%:R R.
    have ATSO : A^T \is 'SO[T]_3 by rewrite rotationV Rzy_is_SO.
    set a := frame_of_SO ATSO.
    have a1E : a |, 1 = a2^T by rewrite frame_of_SO_j /a2 tr_col.
    have a2E : a |, 2%:R = a3^T by rewrite frame_of_SO_k /a3 tr_col.
    have : { w : angle T | r2^T = cos w *: (a |, 1) + sin w *: (a |, 2%:R) /\
                           r3^T = - sin w *: (a |, 1) + cos w *: (a |, 2%:R) }.
      apply exists_rotation_angle.
      by rewrite tr_col norm_row_of_O // rotation_sub // rotationV.
      by rewrite tr_col norm_row_of_O // rotation_sub // rotationV.
      rewrite 2!tr_col.
      by move: RSO; rewrite -rotationV => /rotation_sub/orthogonalP ->.
      rewrite frame_of_SO_i -tr_col -/a1 Ha1 !tr_col.
      move: RSO; rewrite -rotationV => RSO.
      set r := frame_of_SO RSO.
      rewrite -(frame_of_SO_i RSO) -(frame_of_SO_j RSO) -(frame_of_SO_k RSO).
      by rewrite frame_jcrossk.
    case => w [Lw1 Lw2].
    exists (cos w), (sin w).
    split.
      apply trmx_inj.
      by rewrite !linearD !linearZ /= Lw1 a1E a2E.
    apply trmx_inj.
    by rewrite !linearD !linearZ /= -a2E -a1E.
  move/(congr1 trmx) : Hr2.
  rewrite tr_col linearD /= 2!linearZ /= => Hr2.
  move/(congr1 trmx) : Hr3.
  rewrite tr_col linearD /= 2!linearZ /= => Hr3.
  apply: (euler_angles_zyx_RO _ _ _ _ _ _ Hr2 Hr3).
  by move: RSO; rewrite -rotationV => /rotation_sub/orthogonal3P/and6P[_ /eqP].
  by move: RSO; rewrite -rotationV => /rotation_sub/orthogonal3P/and6P[_ _ /eqP].
  move: RSO; by rewrite -rotationV => /rotation_sub/orthogonal3P/and6P[_ _ _ _ _ /eqP].
  by rewrite tr_col norm_row_of_O // rotation_sub // rotationV Rzy_is_SO.
  by rewrite tr_col norm_row_of_O // rotation_sub // rotationV Rzy_is_SO.
  move: (Rzy_is_SO w3 w2).
  rewrite -rotationV => /rotation_sub/orthogonal3P/and6P[_ _ _ _ _ /eqP].
  by rewrite !tr_col.
  move: Hw1; by rewrite 2!tr_col.
  move: Kw1; by rewrite 2!tr_col.
by rewrite -Ha1 row_mx_colE.
Qed.

Lemma Rz_rotation_exists (u : 'rV[T]_3) : norm u = 1 ->
  u != 'e_2%:R -> u != - 'e_2%:R ->
  let n : 'rV_3 := normalize ('e_2%:R *v u) in
  {phi | isRot phi 'e_2%:R (mx_lin1 (Rz phi)) & 'e_0 *m Rz phi = n}.
Proof.
move=> u1 H1 H2 n.
exists (if 0 <= u``_0 then vec_angle n 'e_0 else - vec_angle n 'e_0).
  by rewrite Rz_eskew isRot_eskew // ?normalizeI // ?norm_delta_mx.
rewrite {1}e0row /Rz mulmx_row3_col3 ?(scale0r,scale1r,addr0).
rewrite [in RHS]/n crossmulE.
rewrite (_ : 'e_2%:R 0 1 = 0) ?(mul0r,add0r); last by rewrite mxE.
rewrite (_ : 'e_2%:R 0 0 = 0) ?(mul0r,subrr,subr0); last by rewrite mxE.
rewrite (_ : 'e_2%:R 0 2%:R = 1) ?mul1r; last by rewrite mxE.
have ? : 'e_2%:R *v u != 0.
  apply/colinearP; case.
    by rewrite -norm_eq0 u1 // oner_eq0.
  case=> _ [k Hk]; have k1 : `|k| = 1.
    move: Hk => /(congr1 (@norm _ _)); rewrite normZ u1 mulr1 norm_delta_mx.
    by move->.
  case: (lerP k 0) => k0; move: k1 Hk.
    rewrite ler0_norm // -{2}(opprK k) => ->; rewrite scaleN1r.
    by move/(congr1 (fun x => - x)); rewrite opprK => /esym; apply/eqP.
  by rewrite gtr0_norm // => ->; rewrite scale1r => /esym; apply/eqP.
rewrite /normalize row3Z mulr0; congr row3.
- transitivity (n *d 'e_0).
    rewrite dotmul_cos norm_normalize ?mul1r ?norm_delta_mx ?mul1r //.
    case: ifP => //; by rewrite cosN.
  by rewrite -coorE /n crossmulE /normalize row3Z !mxE /= ?(mulr0,mul0r,add0r,mul1r,subr0,oppr0).
- transitivity (if 0 <= u``_0 then norm (n *v 'e_0) else - norm (n *v 'e_0)).
    rewrite norm_crossmul norm_normalize ?mul1r // norm_delta_mx mul1r.
    rewrite ger0_norm // ?sin_vec_angle_ge0 // -?norm_eq0 ?norm_normalize ?oner_neq0 //
      ?norm_delta_mx ?oner_neq0 //.
    case: ifPn => //; by rewrite sinN.
  rewrite /n /normalize crossmulE.
  rewrite (_ : 'e_0%:R 0 2%:R = 0) ?(mulr0,subr0,add0r); last by rewrite mxE.
  rewrite (_ : 'e_0%:R 0 1 = 0) ?(mulr0,oppr0,add0r); last by rewrite mxE.
  rewrite (_ : 'e_0%:R 0 0 = 1) ?(mulr1); last by rewrite mxE.
  rewrite crossmulE.
  rewrite (_ : 'e_2%:R 0 1 = 0) ?(mul0r,add0r); last by rewrite mxE.
  rewrite (_ : 'e_2%:R 0 0 = 0) ?(mul0r,subrr,subr0); last by rewrite mxE.
  rewrite (_ : 'e_2%:R 0 2%:R = 1) ?(mul1r); last by rewrite mxE.
  rewrite !mxE mulr0 /=.
  rewrite -{2 3 5 6}(oppr0) -row3N normN.
  rewrite [in LHS]mulrC -{2 3 5 6}(mulr0 (u``_0)) -row3Z.
  rewrite normZ mulrC norm_row3z ger0_norm ?invr_ge0 ?norm_ge0 //.
  case: ifPn => R20.
  - by rewrite ger0_norm.
  - by rewrite ltr0_norm ?ltNge // mulrN opprK.
Qed.

End euler_angles.

Section properties_of_atan2. (* not sure they are interesting yet *)

Variables (T : rcfType).

Lemma sqrtr_sqrN2 (x : T) : x != 0 -> Num.sqrt (x ^- 2) = `|x|^-1.
Proof.
move=> x0.
apply (@mulrI _ `|x|); first by rewrite unitfE normr_eq0.
rewrite -{1}(sqrtr_sqr x) -sqrtrM ?sqr_ge0 // divrr; last by rewrite unitfE normr_eq0.
by rewrite divrr ?sqrtr1 // unitfE sqrf_eq0.
Qed.

Lemma N1x2_gt0 (x : T) : `| x | < 1 -> 0 < 1 - x ^+ 2.
Proof. move=> x1; by rewrite subr_gt0 -sqr_normr expr_lt1. Qed.

Definition yarc (x : T) := Num.sqrt (1 - x ^+ 2).

Lemma yarc0 : yarc 0 = 1.
Proof. by rewrite /yarc expr0n subr0 sqrtr1. Qed.

Lemma yarc1 x : `| x | = 1 -> yarc x = 0.
Proof. by move/eqP; rewrite -sqr_norm_eq1 /yarc => /eqP ->; rewrite subrr sqrtr0. Qed.

Lemma yarc_neq0 (x : T) : `| x | < 1 -> yarc x != 0.
Proof. by move=> x1; rewrite sqrtr_eq0 -ltNge N1x2_gt0. Qed.

Lemma yarc_gt0 (x : T) : `| x | < 1 -> 0 < yarc x.
Proof. by move=> x1; rewrite lt_neqAle sqrtr_ge0 andbT eq_sym yarc_neq0. Qed.

Lemma sqr_yarc (x : T) : `| x | < 1 -> (yarc x) ^+ 2 = 1 - x ^+ 2.
Proof. move=> x1; by rewrite /yarc sqr_sqrtr // ltW // N1x2_gt0. Qed.

Lemma yarc_sin (x : angle T) : yarc (sin x) = `| cos x |.
Proof. by rewrite /yarc -cos2sin2 sqrtr_sqr. Qed.

Lemma inv_yarc (x : T) : `| x | < 1 -> (yarc x)^-1 = Num.sqrt (1 - x ^+ 2)^-1.
Proof.
move=> x1.
apply (@mulrI _ (yarc x)); first by rewrite unitfE yarc_neq0.
rewrite divrr; last by rewrite unitfE yarc_neq0.
rewrite -sqrtrM; last by rewrite ltW // N1x2_gt0.
by rewrite divrr ?sqrtr1 // unitfE gt_eqF // N1x2_gt0.
Qed.

Lemma inv_yarc_gt0 (x : T) : `| x | < 1 -> 0 < (yarc x)^-1.
Proof. move=> x1; by rewrite inv_yarc // sqrtr_gt0 invr_gt0 N1x2_gt0. Qed.

Lemma atan2_x_gt0E (x y : T) : y > 0 -> atan2 x y = atan (x / y).
Proof. move=> y0; by rewrite /atan2 y0. Qed.

Lemma atan2_ge0_lt0E (x y : T) : x >= 0 -> y < 0 -> atan2 x y = atan (x / y) + pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltNge ltW. Qed.

Lemma atan2_lt0_lt0E (x y : T) : x < 0 -> y < 0 -> atan2 x y = atan (x / y) - pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltNge ltW //= leNgt x0. Qed.

Lemma atan2_gt0_0E (x y : T) : x > 0 -> atan2 x 0 = pihalf _.
Proof. by move=> x0; rewrite /atan2 x0 ltxx. Qed.

Lemma atan2_lt0_0E (x y : T) : x < 0 -> atan2 x 0 = - pihalf _.
Proof. move=> x0; by rewrite /atan2 ltxx ltNge ltW //= x0. Qed.

Lemma cos_atan2 (x y : T) : y != 0 -> cos (atan2 x y) = y / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neq_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // cosDpi ?eqxx // cos_atan mul1r expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 lt_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?lt_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_even_gt0 // orbC lt_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 lt_eqF.
    by rewrite !invrN invrK mulNr opprK.
  rewrite atan2_lt0_lt0E // -piNpi cosDpi ?eqxx ?orbT // cos_atan mul1r expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // cos_atan mul1r.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gt_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gt_eqF // gtr0_norm // invrM ?invrK //.
by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_gt0.
by rewrite unitfE invr_neq0 // gt_eqF.
Qed.

Lemma cos_atan2_yarc (x : T) : `| x | < 1 -> cos (atan2 (- x) (yarc x)) = yarc x.
Proof.
move=> x1; by rewrite cos_atan2 ?yarc_neq0 // sqr_yarc // sqrrN subrK sqrtr1 divr1.
Qed.

Lemma sin_atan2 (x y : T) : y != 0 -> sin (atan2 x y) = x / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neq_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // sinDpi ?eqxx // sin_atan expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 lt_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?lt_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_even_gt0 // orbC lt_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 lt_eqF.
    rewrite !invrN invrK mulNr mulrN opprK -mulrA (mulrA _^-1) mulVr ?mul1r //.
    by rewrite unitfE lt_eqF.
  rewrite atan2_lt0_lt0E // -piNpi sinDpi ?eqxx ?orbT // sin_atan expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // sin_atan.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gt_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gt_eqF // gtr0_norm // invrM; last 2 first.
  by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_gt0.
  by rewrite unitfE invr_neq0 // gt_eqF.
rewrite invrK -(mulrA x) (mulrA _^-1) mulVr ?mul1r //.
by rewrite unitfE gt_eqF.
Qed.

Lemma sin_atan2_yarc (x : T) : `| x | < 1 -> sin (atan2 x (yarc x)) = x.
Proof.
move=> x1; by rewrite sin_atan2 ?yarc_neq0 // sqr_yarc // subrK sqrtr1 divr1.
Qed.

Lemma cos_atan2_0 (x : T) : cos (atan2 x 0) = (x == 0)%:R.
Proof.
rewrite /atan2 ltxx; case: ifPn => [x0|]; first by rewrite cos_pihalf gt_eqF.
rewrite -leNgt le_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltxx cos0 eqxx.
by rewrite x0 cosN cos_pihalf lt_eqF.
Qed.

Lemma sin_atan2_0 (x : T) : sin (atan2 x 0) = Num.sg x.
Proof.
rewrite /atan2 ltxx; case: ifPn => [x0|]; first by rewrite sin_pihalf gtr0_sg.
rewrite -leNgt le_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltxx sin0 sgr0.
by rewrite x0 sinN sin_pihalf ltr0_sg.
Qed.

End properties_of_atan2.

Section euler_angles_old. (* does not look like the right approach *)

Variables (T : rcfType).

Definition Rxyz (a b c : angle T) :=
  let ca := cos a in let cb := cos b in let cc := cos c in
  let sa := sin a in let sb := sin b in let sc := sin c in
  col_mx3
  (row3 (ca * cb) (sa * cb) (- sb))
  (row3 (ca * sb * sc - sa * cc) (sa * sb * sc + ca * cc) (cb * sc))
  (row3 (ca * sb * cc + sa * sc) (sa * sb * cc - ca * sc) (cb * cc)).

Lemma RxyzE a b c : Rx a * Ry b * Rz c = Rxyz c b a.
Proof.
apply/matrix3P/and9P; split; rewrite !mxE /= sum3E !mxE /= !sum3E !mxE /=; Simp.r => //.
by rewrite mulrC.
by rewrite mulrC.
by rewrite mulrAC -mulrA mulrC (mulrC (cos a)).
by rewrite mulrC (mulrC (sin a)) mulrA (mulrC (cos a)).
by rewrite mulrC.
by rewrite mulrC (mulrC (cos a)) mulrA (mulrC (sin a)).
by rewrite mulrC (mulrC (cos a)) mulrA (mulrC (sin a)).
by rewrite mulrC.
Qed.

Definition rpy_a (M : 'M[T]_3) : angle T :=
  atan2 (M 0 1) (M 0 0).

Definition rpy_b (M : 'M[T]_3) : angle T :=
  atan2 (- M 0 2%:R) (Num.sqrt (M 1 2%:R ^+ 2 + M 2%:R 2%:R ^+ 2)).

Definition rpy_c (M : 'M[T]_3) : angle T :=
  atan2 (M 1 2%:R) (M 2%:R 2%:R).

Lemma rpy_solution M : M \is 'SO[T]_3 ->
  0 < cos (rpy_b M) -> (* pi/2 < b < pi/2 *)
  M = Rx (rpy_c M) * Ry (rpy_b M) * Rz (rpy_a M).
Proof.
move=> MSO Hb.
rewrite RxyzE.
have M02 : `|M 0 2%:R| < 1.
  rewrite lt_neqAle Oij_ub ?rotation_sub // andbT.
  apply/negP => abs.
  move: Hb; rewrite ltNge => /negP; apply.
  move: (abs); rewrite M0j_1 ?rotation_sub // => /andP[/eqP M12 /eqP M22].
  rewrite /rpy_b M12 M22 expr0n add0r sqrtr0 cos_atan2_0 oppr_eq0.
  by rewrite -normr_eq0 (eqP abs) oner_eq0.
apply/matrix3P/and9P; split; apply/eqP; rewrite !mxE /=.
- move: Hb; rewrite /rpy_a /rpy_b sqr_M0jE ?rotation_sub // -/(yarc _) => Hb.
  move: Hb; rewrite cos_atan2_yarc // => _.
  have [/eqP M00|M00] := boolP (M 0 0 == 0).
    rewrite M00 cos_atan2_0.
    have M01 : M 0 1 != 0.
      apply/negPn => /eqP M01.
      move: (Mi2_1 (rotation_sub MSO) 0).
      by rewrite M00 M01 !eqxx /= lt_eqF.
    by rewrite (negbTE M01) mul0r.
  rewrite cos_atan2 // sqr_Mi2E ?rotation_sub // -/(yarc _) -mulrA.
  by rewrite mulVr ?mulr1 // unitfE yarc_neq0.
- move: Hb; rewrite /rpy_a /rpy_b sqr_M0jE ?rotation_sub // -/(yarc _) => Hb.
  move: Hb; rewrite cos_atan2_yarc // => _.
  have [/eqP M00|M00] := boolP (M 0 0 == 0).
    rewrite M00 sin_atan2_0.
    rewrite /yarc -sqr_Mi2E ?rotation_sub // M00 expr0n add0r sqrtr_sqr.
    by rewrite mulr_sg_norm.
  rewrite sin_atan2 // sqr_Mi2E ?rotation_sub // -/(yarc _).
  by rewrite -mulrA mulVr ?mulr1 // unitfE yarc_neq0.
- rewrite /rpy_b.
  rewrite sqr_M0jE ?rotation_sub // -/(yarc _) -sinN atan2N opprK.
  by rewrite sin_atan2_yarc.
- move: Hb; rewrite /rpy_a /rpy_b /rpy_c sqr_M0jE ?rotation_sub // -/(yarc _) => Hb.
  rewrite sin_atan2 ?yarc_neq0 //.
  rewrite sqrrN sqr_yarc // subrK sqrtr1 divr1.
  case/boolP : (M 0 0 == 0) => [/eqP M00|M00] .
    rewrite M00 cos_atan2_0 sin_atan2_0.
    have M01 : M 0 1 != 0.
      admit.
    rewrite (negbTE M01) !mul0r add0r.
    case/boolP : (M 2%:R 2%:R == 0) => [/eqP|] M22.
      rewrite M22 cos_atan2_0.
      have M12 : M 1 2%:R != 0.
        admit.
      rewrite (negbTE M12) mulr0 oppr0.
      admit. (* orth of cols 1 and 3 *)
    rewrite cos_atan2 //.
    rewrite addrC sqr_M0jE ?rotation_sub //.
Abort.

Definition euler_b (M : 'M[T]_3) : angle T := (* theta *)
  if `| M 0 2%:R | != 1 then
    - asin (M 0 2%:R)
  else if M 0 2%:R == 1 then
    - pihalf T
  else (* M 0 2%:R == - 1*) pihalf T.

Definition euler_c (M : 'M[T]_3) : angle T := (* psi *)
  if `| M 0 2%:R | != 1 then
    atan2 (M 1 2%:R / cos (euler_b M)) (M 2%:R 2%:R / cos (euler_b M))
  else if M 0 2%:R == 1 then
    atan2 (- M 1 0) (- M 2%:R 0)
  else
    atan2 (M 1 0) (M 2%:R 1).

Definition euler_a (M : 'M[T]_3) : angle T := (* phi *)
  if `| M 0 2%:R | != 1 then
    atan2 (M 0 1 / cos (euler_b M)) (M 0 0 / cos (euler_b M))
  else
    0.

Lemma rot_euler_anglesE M : M \is 'SO[T]_3 ->
  M = Rx (euler_c M) * Ry (euler_b M) * Rz (euler_a M).
Proof.
move=> MSO.
rewrite RxyzE.
have [/eqP M02|M02] := boolP (`|M 0 2%:R| == 1); last first.
  have {}M02 : `|M 0 2%:R| < 1.
    by rewrite lt_neqAle M02 andTb Oij_ub // rotation_sub.
  apply/matrix3P/and9P; split; apply/eqP; rewrite !mxE /=.
  - rewrite /euler_a /euler_b lt_eqF //= cosN cos_asin //.
    have [/eqP M00|M00] := boolP (M 0 0 == 0).
      rewrite M00 mul0r cos_atan2_0.
      have M01 : M 0 1 != 0.
        apply/negPn => /eqP M01.
        move: (Mi2_1 (rotation_sub MSO) 0).
        by rewrite M00 M01 !eqxx /= lt_eqF.
      rewrite mulf_eq0 (negbTE M01) orFb invr_eq0.
      move H : (_ == 0) => h; case: h H => H.
      by rewrite mul1r (eqP H).
      by rewrite mul0r.
    rewrite cos_atan2; last first.
      by rewrite mulf_neq0 // invr_eq0 -/(yarc _) yarc_neq0.
    rewrite -/(yarc _).
    rewrite mulrAC -(mulrA (M 0 0)) mulVr ?unitfE ?yarc_neq0 // mulr1.
    rewrite 2!expr_div_n -mulrDl sqr_Mi2E ?rotation_sub // sqr_yarc //.
    by rewrite divrr ?sqrtr1 ?divr1 // unitfE subr_eq0 eq_sym sqr_norm_eq1 lt_eqF.
  - rewrite /euler_a /euler_b lt_eqF //= cosN cos_asin //.
    have [/eqP M00|M00] := boolP (M 0 0 == 0).
      rewrite M00 mul0r sin_atan2_0 sgrM sgrV -mulrA -normrEsg.
      by rewrite -sqr_Mi2E ?rotation_sub // M00 expr0n add0r sqrtr_sqr normr_id mulr_sg_norm.
    rewrite sin_atan2; last first.
      by rewrite mulf_neq0 // -/(yarc _) invr_eq0 yarc_neq0.
    rewrite -/(yarc _).
    (* NB: same as above *)
    rewrite mulrAC -(mulrA (M 0 1)) mulVr ?unitfE ?yarc_neq0 // mulr1.
    rewrite 2!expr_div_n -mulrDl sqr_Mi2E ?rotation_sub // sqr_yarc //.
    by rewrite divrr ?sqrtr1 ?divr1 // unitfE subr_eq0 eq_sym sqr_norm_eq1 lt_eqF.
  - by rewrite /euler_b lt_eqF //= sinN opprK asinK // -ler_norml ltW.
  - rewrite /euler_a /euler_c /euler_b lt_eqF //= cosN sinN.
    rewrite cos_asin // -/(yarc _) asinK -?ler_norml; last by rewrite ltW.
    have [/eqP M00|] := boolP (M 0 0 == 0).
      rewrite M00 mul0r cos_atan2_0 sin_atan2_0 mulf_eq0 invr_eq0.
      rewrite (negbTE (yarc_neq0 _)) // orbF.
      have M01 : M 0 1 != 0.
        move: M02.
        rewrite ltNge; apply: contra => M01.
        move: (Mi2_1 (rotation_sub MSO) 0).
        by rewrite M00 M01 eqxx /= => /eqP ->.
      rewrite (negbTE M01) 2!mul0r add0r.
      have [/eqP M22|] := boolP (M 2%:R 2%:R == 0).
        rewrite M22 mul0r cos_atan2_0 mulf_eq0 invr_eq0.
        rewrite (negbTE (yarc_neq0 _)) // orbF.
      have M12 : M 1 2%:R != 0.
        move: M02.
        rewrite ltNge; apply: contra => M12.
        move: (M0j_1 (rotation_sub MSO) 2%:R).
        by rewrite M12 M22 eqxx /= => /eqP ->.
      rewrite (negbTE M12) mulr0 oppr0.
      admit.
    admit.
    admit.
  - rewrite /euler_a /euler_c /euler_b lt_eqF //= cosN sinN.
    rewrite cos_asin // -/(yarc _) asinK -?ler_norml; last by rewrite ltW.
    admit.
  - rewrite /euler_c /euler_b lt_eqF //= cosN cos_asin // -/(yarc _).
    admit.
  - rewrite /euler_a /euler_c /euler_b lt_eqF //= cosN sinN.
    rewrite cos_asin // -/(yarc _) asinK -?ler_norml; last by rewrite ltW.
    admit.
  - rewrite /euler_a /euler_c /euler_b lt_eqF //= cosN sinN.
    rewrite cos_asin // -/(yarc _) asinK -?ler_norml; last by rewrite ltW.
    admit.
  - rewrite /euler_c /euler_b lt_eqF //= cosN cos_asin // -/(yarc _).
    admit.
have [M00 M01] : M 0 0 = 0 /\ M 0 1 = 0.
  by move/eqP : M02; rewrite Mi2_1 ?rotation_sub // => /andP[/eqP ? /eqP].
rewrite /euler_a /euler_b /euler_c M02 eqxx /= /Rxyz.
rewrite cos0 sin0 ?(mul0r,mul1r,add0r,subr0,addr0).
move/eqP : M02; rewrite eqr_norml ler01 andbT => /orP[|] /eqP M02.
- rewrite M02 eqxx cosN sinN opprK.
  apply/matrix3P/and9P; split; apply/eqP; rewrite !mxE //= ?cos_pihalf ?sin_pihalf //.
  rewrite mulN1r.
  admit.
  admit.
  rewrite mul0r.
  move: (M0j_1 (rotation_sub MSO) 2%:R).
  by rewrite M02 normr1 eqxx => /esym /andP[/eqP].
  rewrite mulN1r.
  admit.
  admit.
  rewrite mul0r.
  move: (M0j_1 (rotation_sub MSO) 2%:R).
  by rewrite M02 normr1 eqxx => /esym => /andP[_ /eqP].
- rewrite M02 Neqxx oner_eq0.
  apply/matrix3P/and9P; split; apply/eqP; rewrite !mxE //= ?cos_pihalf // ?sin_pihalf //.
  rewrite mul1r.
  admit.
  admit.
  rewrite mul0r.
  move: (M0j_1 (rotation_sub MSO) 2%:R).
  by rewrite M02 normrN1 eqxx => /esym => /andP[/eqP].
  rewrite mul1r.
  admit.
  admit.
  rewrite mul0r.
  move: (M0j_1 (rotation_sub MSO)  2%:R).
  by rewrite M02 normrN1 eqxx => /esym => /andP[_ /eqP].
Abort.

End euler_angles_old.
