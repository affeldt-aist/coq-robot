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
  2. section is_around_axis_definition.
     definition of rotations w.r.t. axis
     definition of the Rx,Ry,Rz rotations
     properties of rotations
     sample lemmas:
       all rotations around an axis of angle a have trace "1 + 2 * cos a"
       equivalence SO[R]_3 <-> is_around_axis
  2. section axial_vector
     definition of the axial vector 
     proof that this vector is stable by rotation (like the axis)
  3. section exponential_map_rot
     specialized exponential map
     sample lemmas: 
       inverse of the exponential map,
       exponential map of a skew matrix is a rotation
     Rodrigues formula: 
       u * e^(phi,w) can be expressed using a lin. comb. of vectors u, (u *d w)w, u *v w)
  4. section angle_of_rotation
  5. section axis_of_rotation
  6. section angle_axis_of_rot
     sample lemmas:
       a rotation matrix has angle_of_rot M and normnalize (axis_of_rot M) for exp. coor.
  7. section angle_axis_representation
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
case: (sqr_normr_cossin (norm_row_of_O MO 0)); rewrite !mxE => a [a1 a2].
case: (sqr_normr_cossin (norm_row_of_O MO 1)); rewrite !mxE => b [b1 b2].
move/orthogonalP : (MO) => /(_ 0 1) /=.
rewrite dotmulE sum2E !mxE a1 a2 b1 b2 -cosB.
case/cos0_inv => [abpi|].
  exfalso.
  move/rotation_det : MSO.
  rewrite det_mx22 a1 a2 b1 b2 mulrC -(mulrC (cos b)) -sinB => /esym/eqP.
  rewrite -eqr_opp -sinN opprB abpi sin_pihalf -subr_eq0.
  by rewrite -opprD eqr_oppLR oppr0 -(natrD _ 1 1) pnatr_eq0.
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
case: (sqr_normr_cossin (norm_row_of_O MO 0)); rewrite !mxE => a [a1 a2].
case: (sqr_normr_cossin (norm_row_of_O MO 1)); rewrite !mxE => b [b1 b2].
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

Section is_around_axis_definition.

Variable R : rcfType.
Implicit Types a : angle R.

Definition Rx a := col_mx3
  'e_0
  (row3 0 (cos a) (sin a))
  (row3 0 (- sin a) (cos a)).

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

Lemma tr_Rx a : \tr (Rx a) = 1 + cos a *+ 2.
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

(* TODO *)
Definition Ry a := col_mx3
  (row3 (cos a) 0 (- sin a))
  'e_1
  (row3 (sin a) 0 (cos a)).

(* TODO *)
Definition Rz a := col_mx3
  (row3 (cos a) (sin a) 0)
  (row3 (- sin a) (cos a) 0)
  'e_2%:R.

CoInductive is_around_axis (u : 'rV[R]_3)
  (a : angle R)
  (f : {linear 'rV_3 -> 'rV_3}) : Prop :=
  mkIsAroundAxis of
  f u = u &
  let: j := Base.j u in let: k := Base.k u in
  f j = cos a *: j + sin a *: k &
  let: j := Base.j u in let: k := Base.k u in
  f k = - sin a *: j + cos a *: k.

Section properties_of_is_around_axis.

Variable u : 'rV[R]_3.

Lemma is_around_axis_axis a (Q : 'M[R]_3) :
  is_around_axis u a (mx_lin1 Q) -> u *m Q = u.
Proof. by case. Qed.

Lemma is_around_axis1 : is_around_axis u 0 (mx_lin1 1).
Proof.
split => /=; first by rewrite mulmx1.
by rewrite cos0 sin0 mulmx1 scale0r addr0 scale1r.
by rewrite mulmx1 sin0 cos0 scaleNr scale0r oppr0 add0r scale1r.
Qed.

Lemma is_around_axisD (a b : angle R) (f g : 'M[R]_3) :
  is_around_axis u a (mx_lin1 f) ->
  is_around_axis u b (mx_lin1 g) ->
  is_around_axis u (a + b) (mx_lin1 (f * g)).
Proof.
move=> [/= H1 H2 H3] [/= K1 K2 K3]; split => /=.
- by rewrite mulmxA H1 K1.
- rewrite mulmxA H2 mulmxDl cosD sinD -2!scalemxAl K2 K3 2!scalerDr addrACA.
  by rewrite !scalerA mulrN -2!scalerDl (addrC (cos a * sin b)).
- rewrite mulmxA H3 mulmxDl -2!scalemxAl K2 K3 2!scalerDr !scalerA sinD cosD.
  rewrite addrACA mulrN -2!scalerDl -opprB mulNr opprK (addrC (- _ * _)) mulNr.
  by rewrite (addrC (cos a * sin b)).
Qed.

Lemma is_around_axisN a (M : 'M[R]_3) :
  norm u = 1 -> is_around_axis u (- a) (mx_lin1 M) ->
  is_around_axis (- u) a (mx_lin1 M).
Proof.
move=> u1 [/= H1 H2 H3]; split.
by rewrite /= mulNmx H1.
by rewrite /= Base.jN H2 cosN sinN Base.kN scalerN scaleNr.
by rewrite /= Base.kN Base.jN mulNmx H3 sinN opprK cosN scalerN opprD scaleNr.
Qed.

Hypotheses u0 : u != 0.

Lemma is_around_axisZ a f k (k0 : 0 < k):
  is_around_axis (k *: u) a f <-> is_around_axis u a f.
Proof.
split; case; rewrite ?(Base.jZ u0 k0) ?(Base.kZ u0 k0) => H1 H2 H3; split;
  rewrite ?(Base.jZ u0 k0) ?(Base.kZ u0 k0) //.
- move: H1.
  rewrite linearZ /= => /scalerI -> //; by rewrite gtr_eqF.
- by rewrite linearZ H1.
Qed.

Lemma is_around_axisZN a f k (k0 : k < 0):
  is_around_axis (k *: u) a (mx_lin1 f) <-> is_around_axis u (- a) (mx_lin1 f).
Proof.
rewrite -oppr_gt0 in k0. move: u0 => u0'; rewrite -oppr0 -eqr_oppLR in u0'.
split; case => H1 H2 H3; split.
- move: H1 => /=.
  rewrite -scalemxAl => /scalerI; apply; by rewrite -oppr_eq0 gtr_eqF.
- move: H2; rewrite -(opprK k) scaleNr -scalerN (Base.jZ u0' k0) (Base.kZ u0' k0).
  by rewrite cosN sinN Base.jN Base.kN scalerN scaleNr.
- move/eqP: H3; rewrite -(opprK k) scaleNr -scalerN (Base.jZ u0' k0) (Base.kZ u0' k0).
  by rewrite cosN sinN Base.jN Base.kN linearN scalerN -opprB scaleNr 2!opprK addrC eqr_opp => /eqP.
- move: H1; by rewrite /= -scalemxAl => ->.
- rewrite -(opprK k) scaleNr -scalerN (Base.jZ u0' k0) (Base.kZ u0' k0).
  by move: H2; rewrite cosN sinN Base.jN Base.kN scalerN scaleNr.
- rewrite -(opprK k) scaleNr -scalerN (Base.jZ u0' k0) (Base.kZ u0' k0) Base.jN Base.kN.
  by move: H3; rewrite cosN sinN opprK scalerN linearN -opprB scaleNr opprK addrC => ->.
Qed.

Lemma tr_around_axis a M :
  is_around_axis u a (mx_lin1 M) -> \tr M = 1 + cos a *+ 2.
Proof.
case=> /= Hu [Hj Hk].
move: (@basis_change _ M (Base.frame u0) (Rx a)).
rewrite !mxE /= !scale1r !scale0r !add0r !addr0.
rewrite {1 2}/Base.i {1 2}/normalize -scalemxAl Hu => /(_ erefl Hj Hk) ->.
rewrite mxtrace_mulC mulmxA mulmxV ?mul1mx ?tr_Rx //.
rewrite unitmxE unitfE rotation_det ?oner_neq0 //.
exact: (frame_is_rot (Base.frame u0)).
Qed.

Lemma same_rot (M P : 'M[R]_3) v k (k0 : 0 < k) a :
  u = k *: v ->
  is_around_axis u a (mx_lin1 M) ->
  is_around_axis v a (mx_lin1 P) ->
  M = P.
Proof.
move=> mkp [/= HMi HMj HMk] [/= HPi HPj HPk].
apply/eqP/mulmxP => w.
rewrite (orthogonal_expansion (Base.frame u0) w) !mulmxDl -!scalemxAl !scalerA.
have v0 : v != 0 by apply: contra u0; rewrite mkp => /eqP ->; rewrite scaler0.
congr (_ *: _ + _ *: _ + _ *: _).
- by rewrite HMi mkp -scalemxAl HPi.
- by rewrite HMj /= mkp (Base.jZ v0 k0) (Base.kZ v0 k0) -HPj -/(Base.j _) Base.jZ.
- by rewrite HMk /= mkp (Base.jZ v0 k0) (Base.kZ v0 k0) -HPk -/(Base.k _) Base.kZ.
Qed.

Lemma is_around_axis_trmx a M : M \in unitmx ->
  is_around_axis u (- a) (mx_lin1 M) ->
  is_around_axis u a (mx_lin1 M^-1).
Proof.
move=> Hf H.
case: H => [/= H1 H2 H3].
have K1 : normalize u *m M = normalize u by rewrite /normalize -scalemxAl H1.
move: (@basis_change _ M (Base.frame u0) (Rx (- a))).
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
split => /=.
- by rewrite -{1}H1 -mulmxA mulmxV // mulmx1.
- rewrite HfRx !mulmxA.
  rewrite (_ : Base.j u *m _ = 'e_1); last first.
    rewrite col_mx3_mul dotmulC /normalize dotmulZv (Base.udotj u0) mulr0 dotmulvv.
    by rewrite (NOFrame.normj (Base.frame u0)) // expr1n (NOFrame.jdotk (Base.frame u0)) e1row.
  rewrite (_ : 'e_1 *m _ = row3 0 (cos (- a)) (sin a)); last first.
    rewrite (rotation_inv (Rx_is_SO (- a))) /Rx col_mx3_mul.
    rewrite dote2 /= 2!dotmulE 2!sum3E !mxE /= cosN sinN opprK. by Simp.r.
  by rewrite mulmx_row3_col3 scale0r add0r cosN.
- rewrite HfRx !mulmxA.
  rewrite (_ : Base.k u *m _ = 'e_2%:R); last first.
    rewrite col_mx3_mul dotmulC /normalize dotmulZv (Base.udotk u0) mulr0 dotmulC.
    by rewrite (NOFrame.jdotk (Base.frame u0)) dotmulvv (NOFrame.normk (Base.frame u0)) // expr1n e2row.
  rewrite (_ : 'e_2%:R *m _ = row3 0 (- sin a) (cos a)); last first.
    rewrite (rotation_inv (Rx_is_SO (- a))) /Rx col_mx3_mul.
    rewrite dote2 /= 2!dotmulE 2!sum3E !mxE /= cosN sinN opprK. by Simp.r.
  by rewrite mulmx_row3_col3 scale0r add0r.
Qed.

Lemma is_around_axis_SO a f : is_around_axis u a f -> lin1_mx f \is 'SO[R]_3.
Proof.
case=> Hu Hj Hk.
move: (@basis_change _ (lin1_mx f) (Base.frame u0) (Rx a)).
rewrite !mxE /= !(scale1r,scale0r,add0r,addr0) 3!mul_rV_lin1.
rewrite linearZ Hu => /(_ erefl).
rewrite -/(Base.j _) -/(Base.k _) => /(_ Hj Hk) ->.
move=> [:abs].
rewrite rpredM //; last first.
  abstract: abs.
  exact: (frame_is_rot (Base.frame u0)).
by rewrite rpredM // ?Rx_is_SO // rotation_inv // rotationV.
Qed.

End properties_of_is_around_axis.

Definition exp_skew' (a : angle R) (e : 'rV[R]_3) :=
  e^T *m e + (cos a) *: (1 - e^T *m e) + sin a *: \S( e ).

(* [angeles] p.42, eqn 2.49 *)
Lemma is_around_axis_exp_skew'_new phi Q u : norm u = 1 ->
  is_around_axis u phi (mx_lin1 Q) ->
  Q = exp_skew' phi u.
Proof.
move=> e1 Maxis.
apply/eqP/mulmxP => p.
have QO : Q \is 'O[R]_3.
  have : u != 0 by rewrite -norm_eq0 e1 oner_eq0.
  by move/is_around_axis_SO => /(_ _ _ Maxis); rewrite mx_lin1K rotationE => /andP[].
rewrite (decomp (p *m Q) u).
have -> : axialcomp (p *m Q) u = axialcomp p u.
  rewrite axialcompE.
  case: (Maxis) => /= H2 _ _.
  rewrite -{1}H2 trmx_mul mulmxA -(mulmxA p).
  move: QO; rewrite orthogonalE mulmxE => /eqP ->.
  by rewrite mulmx1 axialcompE.
rewrite /exp_skew'.
rewrite -[in RHS]addrA mulmxDr axialcompE mulmxA; congr (_ + _).
have H1 : normalcomp (p *m Q) u = cos phi *: normalcomp p u - sin phi *: (p *v u).
  transitivity (normalcomp p u *m Q).
    (* lemma? *)
    rewrite /normalcomp mulmxBl; congr (_ - _).
    case: Maxis => /= H1 _ _.
    rewrite -scalemxAl H1 -{1}H1; congr (_ *: _).
    by rewrite (proj2 (orth_preserves_dotmul Q) QO u).
  case: Maxis => /= H1 H2 H3.
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
  rewrite -{1}(opprK (sin phi)) 3!scaleNr -opprB opprK -scalerBr; congr (- (_ *: _)).
  rewrite -double_crossmul.
  (* TODO: shouldn't be using Base1... *)
  move: (Frame.jcrossk (Base.frame (norm1_neq0 e1))).
  rewrite -Base.jE -Base.kE -Base.iE => ->.
  rewrite {2}(decomp p u) [in RHS]crossmulC linearD /=.
  rewrite crossmul_axialcomp add0r -[in RHS]crossmulC.
  by rewrite /Base.i normalizeI.
rewrite {}H1 /normalcomp scalerBr mulmxDr -scalemxAr mulmxBr mulmx1.
rewrite scalerBr -2!addrA; congr (_ + _).
rewrite -scalemxAr -(scalerN (sin phi)) crossmulC opprK -(skew_mxE p u).
congr (- (_ *: _) + _).
by rewrite dotmulC mulmxA (mx11_scalar (p *m _)) mul_scalar_mx.
Qed.

Lemma Rx0 : Rx 0 = 1.
Proof. by rewrite /Rx cos0 sin0 oppr0; apply/matrix3P; rewrite !mxE. Qed.

Lemma Rxpi : Rx pi = diag_mx (row3 1 (-1) (-1)).
Proof. 
rewrite /Rx cospi sinpi oppr0; apply/matrix3P; by rewrite !mxE /= -?mulNrn ?mulr1n ?mulr0n.
Qed.
(* TODO: move Rxpi, Rx0 *)

(* xxx *)
Lemma SO_is_around_axis M : M \is 'SO[R]_3 ->
  {u | exists a, norm u = 1 /\ is_around_axis u a (mx_lin1 M) }.
Proof.
move=> MSO.
case/boolP : (M == 1) => [/eqP ->|M1].
  exists 'e_0, 0; split.
    by rewrite norm_delta_mx.
  exact: is_around_axis1.
case: (euler MSO) => v /andP[v0 /eqP vMv].
set f := Base.frame v0. set i := Base.i v. set j := Base.j v. set k := Base.k v.
have iMi : i *m M = i by rewrite /i /normalize -scalemxAl vMv.
have iMj : i *d (j *m M) = 0.
  by rewrite -iMi (proj2 (orth_preserves_dotmul M) (rotation_sub MSO) i j) (NOFrame.idotj f).
have iMk : i *d (k *m M) = 0.
  by rewrite -iMi (proj2 (orth_preserves_dotmul M) (rotation_sub MSO) i k) (NOFrame.idotk f).
set a := (j *m M) *d j.
set b := (j *m M) *d k.
have ab : j *m M = a *: j + b *: k.
  by rewrite {1}(orthogonal_expansion f (j *m M)) -/j -/k dotmulC iMj scale0r add0r.
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
  exists i, phi; split.
    by rewrite norm_normalize.
  apply: (proj1 (@is_around_axisZ _ _ phi (mx_lin1 M) (norm v) _)).
  by rewrite /i normalize_eq0.
  by rewrite ltr_neqAle ?norm_ge0 andbT eq_sym norm_eq0.
  rewrite /i norm_scale_normalize; split => //=.
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
  move: (Frame.P f); rewrite /frame_sgn -/j -/k => -> /eqP.
  by rewrite invr1 mulr1 mul1r -subr_eq0 -opprD eqr_oppLR oppr0 -(natrD _ 1 1) pnatr_eq0.
Qed.

Definition axis_of_rot_gen M :=
  match eqVneq (M \is 'SO[R]_3) true with
  | left HM => sval (SO_is_around_axis HM)
  | right _ => 0
  end.

(*Definition axis_of_rot_gen M (HM : M \is 'SO[R]_3) :=
  sval (SO_is_around_axis HM).*)

Lemma norm_axis_of_rot_gen M (HM : M \is 'SO[R]_3) : norm (axis_of_rot_gen M) = 1.
Proof.
rewrite /axis_of_rot_gen.
case: eqVneq => H.
  rewrite (_ : H = HM) //; last by apply eq_irrelevance.
  by case: (SO_is_around_axis HM) => /= x; case=> a [].
by rewrite HM in H.
Qed.

Lemma axis_of_rot_genE M (HM : M \is 'SO[R]_3) : 
  exists a, is_around_axis (axis_of_rot_gen M) a (mx_lin1 M).
Proof.
rewrite /axis_of_rot_gen.
case: eqVneq => H.
  rewrite (_ : H = HM) //; last by apply eq_irrelevance.
  case: (SO_is_around_axis HM) => /= x [a [? H']].
  by exists a.
by rewrite HM in H.
Qed.

End is_around_axis_definition.

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
Lemma is_around_axis_axial_vec M : M \is 'SO[R]_3 ->
  forall u a, is_around_axis u a (mx_lin1 M) -> colinear u (axial_vec M).
Proof.
move=> MSO u a [/= H1 ? ?]; apply is_eigenvector1_colinear => //.
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

Lemma inv_emx3 a M : M ^+ 4 = - M ^+ 2 -> `e(a, M) * `e(a, -M) = 1.
Proof.
move=> aM.
case/boolP : (cos a == 1) => [/eqP cphi|cphi]; rewrite /emx3.
  by rewrite cphi subrr 2!scale0r !addr0 scalerN (cos1sin0 cphi) scale0r addr0 subr0 mulr1.
rewrite !mulrDr !mulrDl !mulr1 !mul1r -[RHS]addr0 -!addrA; congr (_ + _).
rewrite !addrA (_ : (- M) ^+ 2 = M ^+ 2); last by rewrite expr2 mulNr mulrN opprK -expr2.
rewrite -!addrA (addrCA (_ *: M ^+ 2)) !addrA scalerN subrr add0r.
rewrite (_ : (1 - _) *: _ * _ = - (sin a *: M * ((1 - cos a) *: M ^+ 2))); last first.
  rewrite mulrN; congr (- _).
  rewrite -2!scalerAr -!scalerAl -exprS -exprSr 2!scalerA; congr (_ *: _).
  by rewrite mulrC.
rewrite -!addrA (addrCA (- (sin a *: _ * _))) !addrA subrK.
rewrite mulrN -scalerAr -scalerAl -expr2 scalerA -expr2.
rewrite -[in X in _ - _ + _ + X = _]scalerAr -scalerAl -exprD scalerA -expr2.
rewrite -scalerBl -scalerDl sin2cos2.
rewrite -{2}(expr1n _ 2) subr_sqr -{1 3}(mulr1 (1 - cos a)) -mulrBr -mulrDr.
rewrite opprD addrA subrr add0r -(addrC 1) -expr2 -scalerDr.
apply/eqP; rewrite scaler_eq0 sqrf_eq0 subr_eq0 eq_sym (negbTE cphi) /=.
by rewrite aM subrr.
Qed.

Local Notation "'`e^(' a ',' w ')'" := (emx3 a \S( w )) (format "'`e^(' a ','  w ')'").

Lemma unskew_eskew a w : unskew `e^(a, w) = (sin a) *: w.
Proof.
rewrite /emx3 !(unskewD,unskewZ,skew_mx2,unskewN,skew_mxK,unskew_cst,scaler0,add0r,subr0).
by rewrite unskew_sym ?scaler0 ?addr0 // mul_tr_vec_sym.
Qed.

Lemma tr_eskew a w : `e^(a, w)^T = `e^(a, - w).
Proof. by rewrite tr_emx3 tr_skew /emx3 skew_mxN. Qed.

Lemma trace_eskew a u : norm u = 1 -> \tr `e^(a, u) = 1 + 2%:R * cos a.
Proof.
move=> w1.
rewrite 2!mxtraceD !mxtraceZ /= mxtrace1.
rewrite (trace_anti (anti_skew _)) mulr0 addr0 mxtrace_skew_mx2 w1.
rewrite (_ : - _ = - 2%:R); last by rewrite expr1n mulr1.
by rewrite mulrDl addrA mul1r -natrB // mulrC mulrN -mulNr opprK.
Qed.

(* see table 1.1 of handbook of robotics *)
Lemma eskewE a u : norm u = 1 ->
  let va := 1 - cos a in let ca := cos a in let sa := sin a in
  `e^(a, u) = col_mx3
  (row3 (u``_0 ^+2 * va + ca)
        (u``_0 * u``_1 * va + u``_2%:R * sa)
        (u``_0 * u``_2%:R * va - u``_1 * sa))
  (row3 (u``_0 * u``_1 * va - u``_2%:R * sa)
        (u``_1 ^+2 * va + ca)
        (u``_1 * u``_2%:R * va + u``_0 * sa))
  (row3 (u``_0 * u``_2%:R * va + u``_1 * sa)
        (u``_1 * u``_2%:R * va - u``_0 * sa)
        (u``_2%:R ^+2 * va + ca)).
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

(*Lemma trace_sqr_exp_rot_skew_mx (phi : angle R) w : norm w = 1 ->
  \tr `e^(phi, (skew_mx w) ^+ 2) = - (1 + 2%:R * cos phi) ^+ 2(*?*).
Proof.
move=> w1.
Abort.*)

Lemma Rz_eskew a : Rz a = `e^(a, 'e_2%:R).
Proof.
rewrite /Rz eskewE ?norm_delta_mx //.
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

Definition rodrigues_gen (v : vector) a w :=
  v - (1 - cos a) *: (norm w ^+ 2 *: v) + (1 - cos a) * (v *d w) *: w + sin a *: (w *v v).

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

Definition rodrigues (v : vector) a w :=
  cos a *: v + (1 - cos a) * (v *d w) *: w + sin a *: (w *v v).

Lemma rodriguesP u a w : norm w = 1 -> rodrigues u a w = u *m `e^(a, w).
Proof.
move=> w1; rewrite -(rodrigues_genP u a w).
rewrite /rodrigues_gen /rodrigues w1 expr1n scale1r; congr (_ + _ + _).
by rewrite scalerBl opprB scale1r addrCA addrA addrK.
Qed.

End rodrigues_formula.

Lemma is_around_axis_eskew a w : w != 0 ->
  is_around_axis w a (mx_lin1 `e^(a, normalize w)).
Proof.
move=> w1.
pose f := Base.frame w1.
split => /=.
- rewrite -rodrigues_genP // /rodrigues_gen (norm_normalize w1) expr1n scale1r.
  rewrite dotmul_normalize_norm scalerA -mulrA divrr ?mulr1 ?unitfE ?norm_eq0 //.
  by rewrite subrK crossmulZv crossmulvv 2!scaler0 addr0.
- rewrite -rodrigues_genP // /rodrigues_gen dotmulC.
  rewrite (_ : normalize w *d Base.j w = 0) ?mulr0 ?scale0r ?addr0; last first.
    by move: (NOFrame.idotj f).
  rewrite (Base.icrossj w1) norm_normalize // expr1n scale1r scalerBl scale1r.
  by rewrite opprB addrCA subrr addr0.
- rewrite -rodrigues_genP // /rodrigues_gen dotmulC.
  rewrite (_ : normalize w *d Base.k w = 0) ?mulr0 ?scale0r ?addr0; last first.
    by move: (NOFrame.idotk f).
  rewrite (norm_normalize w1) expr1n scale1r scalerBl scale1r opprB addrCA subrr.
  rewrite addr0 addrC; congr (_ + _).
  rewrite (_ : Base.j w = - Base.i w *v Base.k w); last first.
    by rewrite crossmulNv (Base.icrossk w1) opprK.
  by rewrite crossmulNv scalerN scaleNr opprK.
Qed.

(*Lemma is_around_axis_eskew a w : norm w = 1 ->
  is_around_axis w a (mx_lin1 `e^(a, w)).
Proof.
move=> w1.
pose f := Base.frame (norm1_neq0 w1).
split => /=.
- rewrite -rodriguesP // /rodrigues dotmulvv w1 expr1n mulr1 scalerBl.
  by rewrite scale1r addrCA subrr addr0 crossmulvv scaler0 addr0.
- rewrite -rodriguesP // /rodrigues dotmulC.
  move: (NOFrame.idotj f) => /=.
  rewrite {1 2}/Base.i {1}(normalizeI w1) => ->.
  rewrite mulr0 scale0r addr0 crossmulC.
  rewrite (Base.icrossj (norm1_neq0 w1)).
  by rewrite {1}/Base.i {1}normalizeI // crossmulC opprK.
- rewrite -rodriguesP // /rodrigues dotmulC.
  move: (NOFrame.idotk f) => /=.
  rewrite {1}/Base.i {1}(normalizeI w1) => ->.
  rewrite mulr0 scale0r addr0.
  move: (proj1 (noframe_posP (noframe_pos_crossmul (Frame.P f)))) => /esym.
  rewrite /= -/(Base.k w).
  rewrite {1}/Base.i {1}(normalizeI w1) [in X in _ -> X]crossmulC => ->.
  by rewrite scalerN addrC scaleNr.
Qed.*)

Lemma eskew'E w (a : angle R) : norm w = 1 ->
  exp_skew' a w = `e^(a, w).
Proof.
move=> e1.
rewrite /exp_skew' /emx3 addrAC skew_mx2 e1 expr1n.
rewrite -addrA addrCA -[in RHS]addrA [in RHS]addrCA; congr (_ + _).
rewrite scalerBr scalemx1 scalemx1 scalerBl scale1r.
rewrite -[in RHS](addrA (w^T *m w)) [in RHS](addrCA 1); congr (_ + _).
by rewrite scalerDr addrC addrA subrr add0r opprD scalerN opprK scalemx1.
Qed.

Lemma is_around_axis_exp_skew' e (e0 : e != 0) (a : angle R) :
  is_around_axis e a (mx_lin1 (exp_skew' a (normalize e))).
Proof.
move: (is_around_axis_eskew a e0); by rewrite eskew'E ?norm_normalize.
Qed.

Lemma axial_vec_exp_skew' (e : vector) a : axial_vec (exp_skew' a e) = sin a *: e *+ 2.
Proof.
rewrite /exp_skew' 2!axial_vecD (_ : axial_vec _ = 0) ?add0r; last first.
  apply/eqP; by rewrite -axial_vec_sym mul_tr_vec_sym.
rewrite (_ : axial_vec _ = 0) ?add0r; last first.
  apply/eqP; rewrite -axial_vec_sym sym_scaler_closed (* TODO: delcare the right canonical to be able to use rpredZ *) //.
  by rewrite rpredD // ?sym_cst // rpredN mul_tr_vec_sym.
rewrite axial_vecZ axial_vecE scalerMnr; congr (_ *: _).
by rewrite unskewD skew_mxK unskewN tr_skew unskewN skew_mxK opprK mulr2n.
Qed.

Lemma eskew_is_onto_SO M : M \is 'SO[R]_3 ->
  exists a w, norm w = 1 /\ M = `e^(a, w).
Proof.
case/SO_is_around_axis => u [a [u1 au]].
exists a, (normalize u); split.
  by rewrite norm_normalize // -norm_eq0 u1 oner_eq0.
move: (is_around_axis_eskew a (norm1_neq0 u1)) => au'.
exact: (@same_rot _ u (norm1_neq0 u1) _ _ u 1 ltr01 _ (esym (scale1r _)) au au').
Qed.

End exponential_map_rot.

Notation "'`e(' a ',' M ')'" := (emx3 a M) (format "'`e(' a ','  M ')'").
Notation "'`e^(' a ',' w ')'" := (emx3 a \S( w )) (format "'`e^(' a ','  w ')'").

Section angle_of_rotation.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition angle_of_rot (M : 'M[R]_3) := acos ((\tr M - 1) / 2%:R).

Lemma tr_angle_of_rot M : angle_of_rot M^T = angle_of_rot M.
Proof. by rewrite /angle_of_rot mxtrace_tr. Qed.

Lemma is_around_axis_angle_of_rot M u a : 
  u != 0 -> a \in Opi_closed R ->
  is_around_axis u a (mx_lin1 M) -> a = angle_of_rot M.
Proof.
move=> u0 Ha.
move/(tr_around_axis u0); rewrite /angle_of_rot => ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr.
  by rewrite mulr1 cosK.
by rewrite unitfE pnatr_eq0.
Qed.

Lemma is_around_axis_angle_of_rotN M u a :
  u != 0 -> a \in piO_closed R ->
  is_around_axis u a (mx_lin1 M) -> a = - angle_of_rot M.
Proof.
move=> u0 Ha.
move/(tr_around_axis u0); rewrite /angle_of_rot => ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr.
  by rewrite mulr1 cosKN // opprK.
by rewrite unitfE pnatr_eq0.
Qed.

(* NB: useful? *)
Lemma angle_of_rot_Rx a :
  (a \in Opi_closed R -> angle_of_rot (Rx a) = a) /\
  (a \in piO_closed R -> angle_of_rot (Rx a) = - a).
Proof.
split => Ha; rewrite /angle_of_rot tr_Rx addrAC subrr add0r
  -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1;
  by [rewrite cosK | rewrite cosKN].
Qed.

Lemma angle_of_rot_RO M a : M = block_mx (1 : 'M_1) 0 0 (RO a) ->
  (a \in Opi_closed R -> angle_of_rot M = a) /\
  (a \in piO_closed R -> angle_of_rot M = - a).
Proof.
move=> Ma.
rewrite /angle_of_rot Ma (mxtrace_block (1 : 'M_1)) tr_RO mxtrace1 addrAC.
rewrite subrr add0r -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1.
split => Ha; by [rewrite cosK | rewrite cosKN].
Qed.

Lemma angle_of_rot_exp_skew a u : norm u = 1 ->
  a \in Opi_closed R ->
  angle_of_rot `e^(a, u) = a.
Proof.
move=> u1 Ha.
rewrite /angle_of_rot trace_eskew // addrAC subrr add0r.
by rewrite mulrAC divrr ?mul1r ?unitfE // ?pnatr_eq0 // cosK.
Qed.

Lemma angle_of_rot0_tr (M : 'M[R]_3) : M \is 'SO[R]_3 -> angle_of_rot M = 0 -> \tr M = 3%:R.
Proof.
move=> MSO /(congr1 (fun x => cos x)).
rewrite cos0 /angle_of_rot acosK; last first.
  case: (SO_is_around_axis MSO) => u [a [u1 HM]].
  case: (angle_in a).
    move/(is_around_axis_angle_of_rot (norm1_neq0 u1))/(_ HM) => ?; subst a.
    move/(tr_around_axis (norm1_neq0 u1)) : HM => ->.
    rewrite addrAC subrr add0r.
    rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
    by rewrite -ler_norml cos_max.
  move/(is_around_axis_angle_of_rotN (norm1_neq0 u1))/(_ HM) => ?; subst a.
  move/(tr_around_axis (norm1_neq0 u1)) : HM => ->.
  rewrite addrAC subrr add0r.
  rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
  by rewrite -ler_norml cos_max.
move/(congr1 (fun x => x * 2%:R)).
rewrite -mulrA mulVr ?unitfE ?pnatr_eq0 // mulr1 mul1r.
move/(congr1 (fun x => x + 1)).
rewrite subrK => ->.
by rewrite (natrD _ 2 1).
Qed.

Lemma angle_of_rotpi_tr (M : 'M[R]_3) : M \is 'SO[R]_3 -> angle_of_rot M = pi -> \tr M = - 1.
Proof.
move=> MSO /(congr1 (fun x => cos x)).
rewrite cospi /angle_of_rot acosK; last first.
  (* TODO: factorize with angle_of_rot0_tr *)
  case: (SO_is_around_axis MSO) => u [a [u1 HM]].
  case: (angle_in a).
    move/(is_around_axis_angle_of_rot (norm1_neq0 u1))/(_ HM) => ?; subst a.
    move/(tr_around_axis (norm1_neq0 u1)) : HM => ->.
    rewrite addrAC subrr add0r.
    rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
    by rewrite -ler_norml cos_max.
  move/(is_around_axis_angle_of_rotN (norm1_neq0 u1))/(_ HM) => ?; subst a.
  move/(tr_around_axis (norm1_neq0 u1)) : HM => ->.
  rewrite addrAC subrr add0r.
  rewrite -(mulr_natl (cos _) 2) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
  by rewrite -ler_norml cos_max.
move/(congr1 (fun x => x * 2%:R)).
rewrite -mulrA mulVr ?unitfE ?pnatr_eq0 // mulr1.
move/(congr1 (fun x => x + 1)).
by rewrite subrK mulN1r mulr2n opprD subrK.
Qed.

End angle_of_rotation.

Section axis_of_rotation.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition axis_of_rot (M : 'M[R]_3) : 'rV[R]_3 :=
  let a := angle_of_rot M in 
  if a == pi then 
    axis_of_rot_gen M
  else
    1 / ((sin a) *+ 2) *: axial_vec M.

(* TODO: duplicate lemmas:
mul_tr_vecij
   forall (R : rcfType) (u : 'rV_3) (i j : 'I_3),
   (u^T *m u) i j = u``_i * u``_j
mulmx_trE
   forall (R : rcfType) (n : nat) (v : 'rV_n) (i j : 'I_n),
   (v^T *m v) i j = v``_i * v``_j
*)

(* TODO: move *)
Lemma is_around_axis_pi_inv (M : 'M[R]_3) u : 
  u != 0 -> 
  is_around_axis u pi (mx_lin1 M) ->
  M = (normalize u)^T *m normalize u *+ 2 - 1.
Proof.
move=> u0 H.
have {H}H : is_around_axis (normalize u) pi (mx_lin1 M).
  apply is_around_axisZ => //.
  by rewrite invr_gt0 ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
move/is_around_axis_exp_skew'_new : H.
rewrite norm_normalize // => /(_ erefl) ->.
by rewrite /exp_skew' cospi sinpi scale0r addr0 scaleN1r opprB addrA -mulr2n.
Qed.

(* TODO: move *)
Lemma is_around_axis_0_inv (M : 'M[R]_3) u : 
  u != 0 -> 
  is_around_axis u 0 (mx_lin1 M) -> M = 1.
Proof.
move=> u0 H.
move: (is_around_axis1 u) => H'.
apply: (same_rot u0 ltr01 _ H H').
by rewrite scale1r.
Qed.

Lemma is_around_axis_axis_of_rot (M : 'M[R]_3) u a : 
  u != 0 -> sin a != 0 ->
  is_around_axis u a (mx_lin1 M) ->
  normalize u = (1 / (sin a *+ 2)) *: axial_vec M.
Proof.
move=> u0 sina0 H.
have -> : M = `e^(a, normalize u).
  apply: (@same_rot _ u _ _ _ u 1 _ a) => //.
  by rewrite scale1r.
  exact: (is_around_axis_eskew _ u0).
rewrite axial_vec_eskew scalerA div1r.
by rewrite mulVr ?scale1r // unitfE mulrn_eq0 negb_or.
Qed.

End axis_of_rotation.

Section angle_axis_of_rot.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition log_rot (M : 'M[R]_3) : angle R * 'rV[R]_3 :=
  (angle_of_rot M, axis_of_rot M).

(* TODO: move *)
Lemma sin_eq0 (a : angle R) : (sin a == 0) = (a == 0) || (a == pi).
Proof.
apply/idP/idP => [/eqP|].
  by case/sin0_inv => ->; rewrite !eqxx // orbC.
by case/orP => /eqP ->; rewrite ?sin0 // sinpi.  
Qed.

Lemma log_exp_eskew (a : angle R) (w : 'rV[R]_3) :
  sin a != 0 -> a \in Opi_closed R -> norm w = 1 ->
  log_rot `e^(a, w) = (a, w).
Proof.
move=> sphi Ha w1 [:Hphi].
congr pair.
  abstract: Hphi.
  rewrite /angle_of_rot trace_eskew // addrAC subrr add0r.
  by rewrite mulrC mulrA mulVr ?mul1r ?(cosK Ha) // unitfE pnatr_eq0.
apply/rowP => i.

rewrite /axis_of_rot Hphi.
move: (sphi).
rewrite sin_eq0 negb_or => /andP[_]/negbTE ->.

rewrite 2!mxE /= (*Hphi*) => [:twosphi].
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

Lemma rotation_is_Rx (M : 'M[R]_3) k (k0 : 0 < k) : M \is 'SO[R]_3 ->
  axial_vec M = k *: 'e_0 ->
  angle_of_rot M \in Opi_closed R /\
  (M = Rx (- angle_of_rot M) \/ M = Rx (angle_of_rot M)).
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
have PSO : P \is 'SO[R]_2 by rewrite -(SO3_SO2 MP).
move=> [: Hangle].
split.
  abstract: Hangle.
  rewrite inE /angle_of_rot MP (mxtrace_block (1 : 'M_1)) mxtrace1 addrAC.
  rewrite subrr add0r sin_acos.
    by rewrite sqrtr_ge0.
  rewrite normrM normrV ?unitfE ?pnatr_eq0 // normr_nat ler_pdivr_mulr // mul1r.
  exact: tr_SO2.
case/rot2d : PSO => a PRO; rewrite {}PRO in MP.
case: (angle_in a) => Ha.
- move: (proj1 (angle_of_rot_RO MP) Ha) => MHa.
  right; by rewrite MHa MP Rx_RO.
- move: (proj2 (angle_of_rot_RO MP) Ha) => MHa.
  left; by rewrite MHa opprK MP Rx_RO.
Qed.

(* TODO: move *)
Lemma expiNpi : expi (- pi) = - 1 :> R[i].
Proof.
rewrite expi_cos_sin cosN sinN cospi sinpi.
by apply/eqP; rewrite eq_complex /= !eqxx.
Qed.

Lemma piNpi : pi = - pi :> angle R.
Proof. by apply expi_inj; rewrite expiNpi expipi. Qed.

Lemma SO_pi_inv M : M \is 'SO[R]_3 ->
  angle_of_rot M = pi -> 
  let u := axis_of_rot_gen M in
  M = (normalize u)^T *m normalize u *+ 2 - 1.
Proof.
move=> MSO Mpi u.
have [a H] : exists a, is_around_axis u a (mx_lin1 M) by apply axis_of_rot_genE.
have u1 : norm u = 1 by rewrite norm_axis_of_rot_gen.
have ? : a = pi.
  case: (angle_in a) => Ha.
    by move/is_around_axis_angle_of_rot : H => /(_ (norm1_neq0 u1)) -> //.
  by move/is_around_axis_angle_of_rotN : H => /(_ (norm1_neq0 u1)) -> //; rewrite piNpi Mpi.
subst a.
by move/is_around_axis_pi_inv : H => /(_ (norm1_neq0 u1)) HM.
Qed.

Lemma angle_axis_eskew_gen M : M \is 'SO[R]_3 ->
  axial_vec M != 0 ->
(*  angle_of_rot M != pi ->*)
  M = exp_skew' (angle_of_rot M) (normalize (axis_of_rot M)).
Proof.
move=> HM M0 (*api*).
case/boolP : (angle_of_rot M == 0) => [/eqP H|a0].
  rewrite H /exp_skew' cos0 scale1r sin0 scale0r addr0 addrCA subrr addr0.
  apply O_tr_idmx; by [apply/rotation_sub | apply angle_of_rot0_tr].
case/boolP : (angle_of_rot M == pi) => [/eqP H|api].
  rewrite H /exp_skew' cospi scaleN1r sinpi scale0r addr0 opprB addrA -mulr2n.
  rewrite /axis_of_rot H eqxx.
  by apply SO_pi_inv.
have sina0 : sin (angle_of_rot M) != 0.
  apply: contra a0 => /eqP/sin0_inv [->//|/eqP]; by rewrite (negbTE api).
set w := normalize _.
case: (SO_is_around_axis HM) => w' [a [w'1 w'a]].
have w'0 : w' != 0 by rewrite -norm_eq0 w'1 oner_neq0.
have Htmp0 : axis_of_rot M != 0.

  rewrite /axis_of_rot.
  move: (sina0).
  rewrite sin_eq0 negb_or => /andP[_ /negbTE] ->.

  by rewrite scaler_eq0 negb_or div1r invr_eq0 mulrn_eq0 /= M0 andbT.
rewrite eskew'E ?norm_normalize //.
have w1 : norm w = 1 by rewrite norm_normalize.
case: (angle_in a) => Ha.
- move: (is_around_axis_angle_of_rot w'0 Ha w'a) => ?; subst a.
  move: (is_around_axis_axis_of_rot w'0 sina0 w'a) => w'axial.
  set k := (1 / _) in w'axial.
  have k0 : 0 < k.
    rewrite /k div1r invr_gt0 pmulrn_lgt0 // ltr_neqAle eq_sym sina0 /=.
    by rewrite inE in Ha.
  apply: (@same_rot _ _ w'0 _ _ (norm (axis_of_rot M) *: w) ((sin (angle_of_rot M) *+ 2) * k) _ (angle_of_rot M)).
  - by rewrite pmulr_rgt0 // pmulrn_lgt0 // ltr_neqAle eq_sym sina0.
  - rewrite -(norm_scale_normalize w') w'axial scalerA mulrC -scalerA.
    rewrite mulrC -[in RHS]scalerA; congr (_ *: _).
    rewrite /w norm_scale_normalize.

    rewrite /axis_of_rot.
    move: (sina0).
    rewrite sin_eq0 negb_or => /andP[_ /negbTE] ->.
    
    rewrite scalerA div1r divrr ?scale1r ?w'1 ?scale1r //.
    by rewrite unitfE mulrn_eq0 negb_or.
  - rewrite -{2}(trmxK M).
    move/rotation_inv : (HM) => <-.
    by rewrite orthogonal_inv ?rotation_sub // trmxK.
  - move: (is_around_axis_eskew (angle_of_rot M) (norm1_neq0 w1)) => H.
    rewrite (normalizeI w1) in H.
    apply: (proj2 (is_around_axisZ (norm1_neq0 w1) _ _ _)) => //.
    by rewrite ltr_neqAle norm_ge0 eq_sym norm_eq0 Htmp0.
- move: (is_around_axis_angle_of_rotN w'0 Ha w'a) => a_angle_of_rot.
  have : M \in unitmx by rewrite orthogonal_unit // rotation_sub // -rotationV.
  move/(@is_around_axis_trmx _ _ w'0 (angle_of_rot M^T) M).
  rewrite {1}tr_angle_of_rot -a_angle_of_rot => /(_ w'a).
  rewrite (rotation_inv HM) tr_angle_of_rot.
  move/(is_around_axis_axis_of_rot w'0 sina0) => w'axial.
  set k := (1 / _) in w'axial.
  have k0 : 0 < k.
    rewrite /k div1r invr_gt0 pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  apply: (@same_rot _ _ w'0 _ _ (- norm (axis_of_rot M) *: w) ((sin (angle_of_rot M) *+ 2) * k) _ (- angle_of_rot M)).
  - rewrite pmulr_rgt0 // pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  - rewrite -(norm_scale_normalize w') w'axial scalerA mulrC -scalerA.
    rewrite [in RHS]mulrC -[in RHS]scalerA; congr (_ *: _).
    rewrite /w.
    rewrite 2!scalerA -mulrA mulNr divrr ?mulr1; last first.
      by rewrite unitfE norm_eq0.
    rewrite w'1 scale1r tr_axial_vec mulrN1. 

    rewrite /axis_of_rot.
    move: (sina0).
    rewrite sin_eq0 negb_or => /andP[_ /negbTE] ->.

    rewrite scalerA div1r.
    rewrite mulr2n mulNr divrr ?scaleN1r //.
    by rewrite unitfE -mulr2n mulrn_eq0 negb_or.
  - by rewrite -a_angle_of_rot.
  - move: (is_around_axis_eskew (angle_of_rot M) (norm1_neq0 w1)) => H.
    rewrite (normalizeI w1) in H.
    have w0' : 0 < (norm (axis_of_rot M))^-1.
      by rewrite invr_gt0 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
    apply: (proj1 (is_around_axisZ _ _ _ w0')).
      rewrite scaler_eq0 negb_or eqr_oppLR oppr0 norm_eq0 Htmp0 /= /w scaler_eq0.
      by rewrite negb_or invr_eq0 norm_eq0 andbb.
    rewrite scaleNr scalerN scalerA mulVr; last by rewrite unitfE norm_eq0.
    rewrite scale1r.
    apply is_around_axisN => //.
    by rewrite opprK.
Qed.

(*Lemma angle_axis_eskew_gen M : M \is 'SO[R]_3 ->
  axial_vec M != 0 ->
  angle_of_rot M != pi ->
  M = `e^(angle_of_rot M, normalize (axis_of_rot M)).
Proof.
move=> HM M0 api.
case/boolP : (angle_of_rot M == 0) => [/eqP H|a0].
  rewrite H emx30M.
  apply SO_tr3_idmx => //; by apply angle_of_rot0_tr.
(*case/boolP : (angle_of_rot M == pi) => [/eqP H|].
  case: (SO_pi_inv HM H) => u Mu.
  rewrite -eskew'E ?norm_normalize.
  
  rewrite H /emx3 sinpi scale0r addr0 cospi opprK (_ : 1 + 1 = 2%:R) // scaler_nat.
  rewrite /axis_of_rot.
*)
have sina0 : sin (angle_of_rot M) != 0.
  apply: contra a0 => /eqP/sin0_inv [->//|/eqP]; by rewrite (negbTE api).
set w := normalize _.
case: (SO_is_around_axis HM) => w' [a [w'1 w'a]].
have w'0 : w' != 0 by rewrite -norm_eq0 w'1 oner_neq0.
have Htmp0 : axis_of_rot M != 0.
  by rewrite scaler_eq0 negb_or div1r invr_eq0 mulrn_eq0 /= M0 andbT.
have w1 : norm w = 1 by rewrite norm_normalize.
case: (angle_in a) => Ha.
- move: (is_around_axis_angle_of_rot w'0 Ha w'a) => ?; subst a.
  move: (is_around_axis_axis_of_rot w'0 sina0 w'a) => w'axial.
  set k := (1 / _) in w'axial.
  have k0 : 0 < k.
    rewrite /k div1r invr_gt0 pmulrn_lgt0 // ltr_neqAle eq_sym sina0 /=.
    by rewrite inE in Ha.
  apply: (@same_rot _ _ w'0 _ _ (norm (axis_of_rot M) *: w) ((sin (angle_of_rot M) *+ 2) * k) _ (angle_of_rot M)).
  - by rewrite pmulr_rgt0 // pmulrn_lgt0 // ltr_neqAle eq_sym sina0.
  - rewrite -(norm_scale_normalize w') w'axial scalerA mulrC -scalerA.
    rewrite mulrC -[in RHS]scalerA; congr (_ *: _).
    rewrite /w norm_scale_normalize.
    rewrite /axis_of_rot scalerA div1r divrr ?scale1r ?w'1 ?scale1r //.
    by rewrite unitfE mulrn_eq0 negb_or.
  - rewrite -{2}(trmxK M).
    move/rotation_inv : (HM) => <-.
    by rewrite orthogonal_inv ?rotation_sub // trmxK.
  - move: (is_around_axis_eskew (angle_of_rot M) (norm1_neq0 w1)) => H.
    rewrite (normalizeI w1) in H.
    apply: (proj2 (is_around_axisZ (norm1_neq0 w1) _ _ _)) => //.
    by rewrite ltr_neqAle norm_ge0 eq_sym norm_eq0 Htmp0.
- move: (is_around_axis_angle_of_rotN w'0 Ha w'a) => a_angle_of_rot.
  have : M \in unitmx by rewrite orthogonal_unit // rotation_sub // -rotationV.
  move/(@is_around_axis_trmx _ _ w'0 (angle_of_rot M^T) M).
  rewrite {1}tr_angle_of_rot -a_angle_of_rot => /(_ w'a).
  rewrite (rotation_inv HM) tr_angle_of_rot.
  move/(is_around_axis_axis_of_rot w'0 sina0) => w'axial.
  set k := (1 / _) in w'axial.
  have k0 : 0 < k.
    rewrite /k div1r invr_gt0 pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  apply: (@same_rot _ _ w'0 _ _ (- norm (axis_of_rot M) *: w) ((sin (angle_of_rot M) *+ 2) * k) _ (- angle_of_rot M)).
  - rewrite pmulr_rgt0 // pmulrn_lgt0 //.
    by rewrite inE a_angle_of_rot sinN oppr_lt0 in Ha.
  - rewrite -(norm_scale_normalize w') w'axial scalerA mulrC -scalerA.
    rewrite [in RHS]mulrC -[in RHS]scalerA; congr (_ *: _).
    rewrite /w.
    rewrite 2!scalerA -mulrA mulNr divrr ?mulr1; last first.
      by rewrite unitfE norm_eq0.
    rewrite w'1 scale1r tr_axial_vec mulrN1 scalerA div1r.
    rewrite mulr2n mulNr divrr ?scaleN1r //.
    by rewrite unitfE -mulr2n mulrn_eq0 negb_or.
  - by rewrite -a_angle_of_rot.
  - move: (is_around_axis_eskew (angle_of_rot M) (norm1_neq0 w1)) => H.
    rewrite (normalizeI w1) in H.
    have w0' : 0 < (norm (axis_of_rot M))^-1.
      by rewrite invr_gt0 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
    apply: (proj1 (is_around_axisZ _ _ _ w0')).
      rewrite scaler_eq0 negb_or eqr_oppLR oppr0 norm_eq0 Htmp0 /= /w scaler_eq0.
      by rewrite negb_or invr_eq0 norm_eq0 andbb.
    rewrite scaleNr scalerN scalerA mulVr; last by rewrite unitfE norm_eq0.
    rewrite scale1r.
    apply is_around_axisN => //.
    by rewrite opprK.
Qed.
*)

Lemma angle_axis_is_around_axis (Q : 'M[R]_3) :
  Q \is 'SO[R]_3 ->
  axial_vec Q != 0 ->
  angle_of_rot Q != pi ->
  is_around_axis (normalize (axis_of_rot Q)) (angle_of_rot Q) (mx_lin1 Q).
Proof.
move=> QSO w0 a0.
case/boolP : (angle_of_rot Q == 0) => aQ0.
  have Q1 : Q = 1.
    apply O_tr_idmx; by [apply rotation_sub | 
      apply angle_of_rot0_tr => //; apply/eqP].
  rewrite (eqP aQ0) Q1.
  by apply is_around_axis1.
have Htmp0 : axis_of_rot Q != 0.

  rewrite /axis_of_rot.
  rewrite (negbTE a0).

  rewrite scaler_eq0 negb_or div1r invr_eq0 mulrn_eq0 /= w0 andbT.
  apply: contra aQ0 => /eqP/sin0_inv[/eqP //|/eqP]; by rewrite (negbTE a0).
have HQ : Q = `e^(angle_of_rot Q, normalize (axis_of_rot Q)).
  
  rewrite -eskew'E ?norm_normalize //.
  by apply: angle_axis_eskew_gen.
rewrite {3}HQ.
rewrite is_around_axisZ //.
by apply is_around_axis_eskew => //.
by rewrite invr_gt0 ltr_neqAle norm_ge0 eq_sym norm_eq0 andbT.
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
  insubd (@AngleAxis (a,_) norm_e1_subproof) (a, (norm v)^-1 *: v).

Lemma aaxis_of (a : angle R) (v : vector) : v != 0 ->
  aaxis (angle_axis_of a v) = (norm v)^-1 *: v.
Proof.
move=> v_neq0 /=; rewrite /angle_axis_of /aaxis val_insubd /=.
by rewrite normZ normfV normr_norm mulVf ?norm_eq0 // eqxx.
Qed.

(* NB: not used *)
(*Lemma aaxis_of1 (a : angle R) (v : vector) : norm v = 1 ->
  aaxis (angle_axis_of a v) = v.
Proof.
move=> v1; rewrite aaxis_of; last by rewrite -norm_eq0 v1 oner_neq0.
by rewrite v1 invr1 scale1r.
Qed.*)

Lemma aangle_of (a : angle R) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

Coercion exp_skew_of_angle_axis r :=
  let (a, w) := (aangle r, aaxis r) in `e^(a, w).

(* NB: does not seem useful *)
(*Lemma trace_rodrigues r : \tr (exp_rot_of_angle_axis r) = 1 + 2%:R * cos (aangle r).
Proof. by rewrite trace_exp_rot_skew_mx // norm_axis. Qed.
Lemma rodrigues_mx_is_O r : norm (aaxis r) = 1 -> exp_rot_of_angle_axis r \in 'O[R]_3.
Proof.
move=> axis1.
rewrite /exp_rot_of_angle_axis orthogonalE tr_exp_rot {2}(eqP (anti_skew _)) linearN /= trmxK.
by rewrite inv_exp_rot // skew_mx4.
Qed.
Lemma det_rodrigues_mx r : norm (aaxis r) = 1 -> \det (exp_rot_of_angle_axis r) = 1.
Proof. move=> ?; by rewrite /exp_rot_of_angle_axis det_exp_rot. Qed.
*)

Definition angle_axis_of_rot M :=
  angle_axis_of (angle_of_rot M) (axis_of_rot M).

Lemma angle_axis_eskew M : M \is 'SO[R]_3 ->
  axial_vec M != 0 ->
  angle_of_rot M != pi ->
  let a := aangle (angle_axis_of_rot M) in
  let w := aaxis (angle_axis_of_rot M) in
  M = `e^(a, w).
Proof.
move=> HM M0 sin0 a w.
case/boolP : (angle_of_rot M == 0) => a0.
  rewrite /a aangle_of (eqP a0) emx30M.
  apply O_tr_idmx; [by apply rotation_sub|].
  apply angle_of_rot0_tr => //; by apply/eqP.
rewrite -eskew'E ?norm_axis //.
rewrite (angle_axis_eskew_gen HM M0) /a /w aangle_of aaxis_of //.

rewrite /axis_of_rot.
rewrite (negbTE sin0).

rewrite scaler_eq0 negb_or M0 andbT div1r invr_eq0 mulrn_eq0 /=.
apply: contra a0 => /eqP/sin0_inv[/eqP //|/eqP].
by rewrite (negbTE sin0). 
Qed.

End angle_axis_representation.
