Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp
Require Import complex.
From mathcomp.fingroup
Require Import fingroup perm.

(*
 OUTLINE:
 1. section extra
 2. section dot_product
 3. sections O[R]_3 and SO[R]_3
    (sample lemma: Euler's theorem)
 4. section triple_prod_mat/crossmul (definition of "normal" also) 
    (sample lemma: double_crossmul)
 5. section norm 
    (sample lemma: multiplication by a O[R]_3 matrix preserves norm)
    (NB: some specialized lemmas for dimension 3)
 6. section colinear 
    (simple definition using crossmul, but seemed clearer to me to have a dedicated definition)
 7. section angle 
    (addition, scalar multiplication, half-angle)
    (definitions of cos, sin, acos, etc. also various properties) 
    (NB: vec_angles seem to be restricted to [0,pi])
    (sample lemma: multiplication by a O[R]_3 matrix preserves vec_angle)
 8. section normalize_orthogonalize 
    (easy definitions to construct a frame out of three non-colinear points)
 9. section triad 
    (construction d'une base orthonormee a partir de trois points non-colineaires)
 10. section transformation_given_three_points 
    (construction d'une transformation (rotation + translation) etant donnes 
    trois points de depart et leurs positions d'arrivee)
 11. section canonical frame (the frame (1,0,0),(0,1,0),(0,0,1) and its properties)
 12. definition of rotations w.r.t. an axis
 13. module Frame: 
     frame definition and of mapping from one frame to another (NB: in progress)
 14. section homogeneous_transformation
 15. section isometry_def
 16. section orthognal_frame
 17. sectoon tangent vectors
 18. section central isometrie
 19. section derivative maps
     (sample lemma: preservation of the cross-product by derivative maps)
 20. section rigid_transformation_is_homogenous_transformation
     (a direct isometry (i.e., cross-product preserving) can be expressed in homogeneous coordinates)
     (NB: converse in progress)
 21: section kinematics chains
 22. section symmetric/antisymmetry/skew (properties of skew matrices)
     (sample lemma: eigenvalues of skew matrices)
 14. section exponential_map (properties of exponential map)
     (sample lemma: inverse of the exponential map,
     exponential map of a skew matrix is a rotation)
 15. section rodrigues
     (sample lemmas: equivalence exponential map <-> Rodrigues' formula)
     (TODO: prove that rotations can always be epressed as exponential map)
 16. section quaternion
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Ltac simp_ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=].
Ltac simpr := rewrite ?(mulr0,mul0r,mul1r,mulr1,addr0,add0r).

Section extra.

Lemma opp_self {R : rcfType} (u : 'rV[R]_3) : u = - u -> u = 0.
Proof.
move/eqP.
by rewrite -subr_eq0 opprK -mulr2n -scaler_nat scaler_eq0 pnatr_eq0 /= => /eqP.
Qed.

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat)
 (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (M : zmodType) (m1 m2 n : nat)
 (A1 : 'M[M]_(m1, n)) (A2 : 'M_(m2, n)):
 (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
by rewrite -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx0 tr_col_mx row_mx_eq0.
Qed.

Lemma rew_condAr (a b c : bool) : a = b && c -> (b -> c = a).
Proof. by case: b. Qed.

Lemma thirdI3 (i j : 'I_3) : i != j -> exists k, (k != i) && (k != j).
Proof.
case: i j => -[i0|[i1|[i2|//]]].
- case=> -[//|[j1 _|[j2 _|//]]]; by [exists 2%:R | exists 1].
- case=> -[j0 _|[//|[j2 _|//]]]; by [exists 2%:R | exists 0].
- case=> -[j0 _|[j1 _|[//|//]]]; by [exists 1 | exists 0].
Qed.

Lemma ifnot0 (i : 'I_3) : (i != 0) = (i == 1) || (i == 2%:R).
Proof. by case: i => -[i0 //| [i1 //| [i2 // | //]]]. Qed.

Lemma ifnot1 (i : 'I_3) : (i != 1) = (i == 0) || (i == 2%:R).
Proof. by case: i => -[i0 //| [i1 //| [i2 // | //]]]. Qed.

Lemma ifnot2 (i : 'I_3) : (i != 2%:R) = (i == 0) || (i == 1).
Proof. by case: i => -[i0 //| [i1 //| [i2 // | //]]]. Qed.

Lemma sum1E {T : ringType} (f : 'I_1 -> T) : \sum_(i < 1) f i = f 0.
Proof. rewrite (bigD1 ord0) //= big_pred0 ?addr0 //; by case => -[]. Qed.

Lemma sum2E {T : ringType} (f : 'I_2 -> T) : \sum_(i < 2) f i = f 0 + f 1.
Proof. rewrite big_ord_recr /= sum1E; congr (f _ + f _); by apply val_inj. Qed.

Lemma sum3E {T : ringType} (f : 'I_3 -> T) : \sum_(i < 3) f i = f 0 + f 1 + f 2%:R.
Proof. rewrite big_ord_recr //= sum2E; congr (f _ + f _ + f _); by apply val_inj. Qed.

Lemma sum4E {T : ringType} (f : 'I_4 -> T) : \sum_(i < 4) f i = f 0 + f 1 + f 2%:R + f 3%:R.
Proof. rewrite big_ord_recr //= sum3E; congr (f _ + f _ + f _ + f _); by apply val_inj. Qed.

Lemma det_mx11 {T : comRingType }(A : 'M[T]_1) : \det A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar det_scalar. Qed.

Lemma cofactor_mx22 {T : comRingType} (A : 'M[T]_2) i j :
  cofactor A i j = (-1) ^+ (i + j) * A (i + 1) (j + 1).
Proof.
rewrite /cofactor det_mx11 !mxE; congr (_ * A _ _);
by apply/val_inj; move: i j => [[|[|?]]?] [[|[|?]]?].
Qed.

Lemma liftE0 m (i : 'I_m.+2) : fintype.lift i ord0 = (i == 0)%:R.
Proof. 
apply/val_inj => /=; rewrite /bump leqn0 addn0.
by case: i => // -[].
Qed.

Lemma liftE1 {m} (i : 'I_m.+3) : fintype.lift i 1 = (i <= 1).+1%:R.
Proof.
apply val_inj => /=.
case: i => -[/= _|]; first by rewrite /bump modn_small.
by case.
Qed.

Lemma det_mx22 {T : comRingType} (A : 'M[T]_2) : \det A = A 0 0 * A 1 1 -  A 0 1 * A 1 0.
Proof.
rewrite (expand_det_row _ ord0) !(mxE, big_ord_recl, big_ord0).
rewrite !(mul0r, mul1r, addr0) !cofactor_mx22 !(mul1r, mulNr, mulrN).
by rewrite !(lift0E, add0r) /= addrr_char2.
Qed.

Lemma cofactor_mx33 {T : comRingType} (A : 'M[T]_3) i j :
  cofactor A i j = (-1) ^+ (i + j) * 
                   (A (i == 0)%:R (j == 0)%:R * A ((i <= 1).+1%:R) ((j <= 1).+1%:R) -
                    A (i == 0)%:R ((j <= 1).+1%:R) * A ((i <= 1).+1%:R) (j == 0)%:R).
Proof.
rewrite /cofactor det_mx22 !mxE; congr (_ * (A _ _ * A _ _ - A _ _ * A _ _));
  by rewrite (liftE0, liftE1).
Qed.

Lemma det_mx33 {T : comRingType } (M : 'M[T]_3) :
  \det M = M 0 0 * (M 1 1 * M 2%:R 2%:R - M 2%:R 1 * M 1 2%:R) +
           M 0 1 * (M 2%:R 0 * M 1 2%:R - M 1 0 * M 2%:R 2%:R) +
           M 0 2%:R * (M 1 0 * M 2%:R 1 - M 2%:R 0 * M 1 1).
Proof.
rewrite (expand_det_row M 0) sum3E -2!addrA; congr (_ * _ + (_ * _ + _ * _)).
  by rewrite cofactor_mx33 /= expr0 mul1r [in X in _ - X]mulrC.
by rewrite cofactor_mx33 /= expr1 mulN1r opprB mulrC.
by rewrite cofactor_mx33 expr2 mulN1r opprK mul1r /= [in X in _ - X]mulrC.
Qed.

Lemma opp_conjc {R : rcfType} (a b : R) : - (a -i* b) = - a +i* b.
Proof. by apply/eqP; rewrite eq_complex /= opprK !eqxx. Qed.

Lemma Re_scale {R : rcfType} (x : R[i]) (k : R) : k != 0 -> Re (x / k%:C) = (Re x) / k.
Proof. 
move=> k0; case: x => a b /=.
rewrite expr0n /= addr0 mul0r -mulrN opprK mulr0 addr0.
by rewrite expr2 invrM // ?unitfE // (mulrA k) divff // mul1r.
Qed.

Lemma complexZ1 {R : rcfType} (a b k : R) : (k * a) +i* (k * b) = k%:C * (a +i* b).
Proof. by simpc. Qed.

Lemma complexZ2 {R : rcfType} (a b k : R) : (k * a) -i* (k * b) = k%:C * (a -i* b).
Proof. by simpc. Qed.

Definition complexZ {R : rcfType} := (@complexZ1 R, @complexZ2 R).

End extra.

Section dot_product.

Variables (R : rcfType) (n : nat).

Definition dotmul (u v : 'rV[R]_n) : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE u v : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma dotmulC u v : u *d v = v *d u.
Proof. by rewrite /dotmul -[_ *m _]trmxK trmx_mul !trmxK mxE. Qed.

Lemma dotmul0v v : 0 *d v = 0.
Proof. by rewrite [LHS]mxE big1 // => i; rewrite mxE mul0r. Qed.

Lemma dotmulv0 v : v *d 0 = 0.
Proof. by rewrite dotmulC dotmul0v. Qed.

Lemma dotmulDr a b c : a *d (b + c) = a *d b + a *d c.
Proof. by rewrite {1}/dotmul linearD /= linearD /= mxE. Qed.

Lemma dotmulDl a b c : (b + c) *d a = b *d a + c *d a.
Proof. by rewrite dotmulC dotmulDr dotmulC (dotmulC c). Qed.

Lemma dotmulD u v : (u + v) *d (u + v) = u *d u + (u *d v) *+ 2 + v *d v.
Proof. rewrite dotmulDr 2!dotmulDl -!addrA; congr (_ + _); by rewrite dotmulC. Qed.

Lemma dotmulvN u v : u *d -v = - (u *d v).
Proof. by rewrite /dotmul linearN /= mulmxN mxE. Qed.

Lemma dotmulNv u v : - u *d v = - (u *d v).
Proof. by rewrite dotmulC dotmulvN dotmulC. Qed.

Lemma dotmulvZ u k v : u *d (k *: v) = k * (u *d v).
Proof. by rewrite /dotmul linearZ /= -scalemxAr mxE. Qed.

Lemma dotmulZv u k v : (k *: u) *d v = k * (u *d v).
Proof. by rewrite dotmulC dotmulvZ dotmulC. Qed.

Lemma le0dotmul u : 0 <= u *d u.
Proof. rewrite dotmulE sumr_ge0 // => i _; by rewrite -expr2 sqr_ge0. Qed.

Lemma dotmulvv0 u : (u *d u == 0) = (u == 0).
Proof.
apply/idP/idP; last by move/eqP ->; rewrite dotmul0v.
rewrite dotmulE psumr_eq0; last by move=> i _; rewrite -expr2 sqr_ge0.
move/allP => H; apply/eqP/rowP => i.
apply/eqP; by rewrite mxE -sqrf_eq0 expr2 -(implyTb ( _ == _)) H.
Qed.

Lemma dotmul_delta_mx u i : u *d delta_mx 0 i = u 0 i.
Proof.
rewrite dotmulE (bigD1 i) //= mxE !eqxx /= mulr1 (eq_bigr (fun=> 0)).
rewrite big_const; elim: #| _ | => /= [|*]; by rewrite ?(addr0,add0r).
by move=> j ji; rewrite !mxE eqxx (negbTE ji) /= mulr0.
Qed.

Lemma dotmul_eq u v : (forall x, u *d x = v *d x) -> u = v.
Proof.
move=> uv.
rewrite (row_sum_delta u) (row_sum_delta v); apply eq_bigr => i _.
move: (uv (delta_mx 0 i)); by rewrite 2!dotmul_delta_mx => ->.
Qed.

Lemma dotmul_trmx u M v : u *d (v *m M) = (u *m M^T) *d v.
Proof. by rewrite /dotmul trmx_mul mulmxA. Qed.

End dot_product.

Notation "*d%R" := (@dotmul _ _) : ring_scope.
Notation "u *d w" := (dotmul u w) (at level 40) : ring_scope.

Section orthogonal_rotation_def.

Variables (n : nat) (R : rcfType).

Definition orthogonal := [qualify M : 'M[R]_n | M *m M^T == 1%:M].
Fact orthogonal_key : pred_key orthogonal. Proof. by []. Qed.
Canonical orthogonal_keyed := KeyedQualifier orthogonal_key.

Definition rotation := [qualify M : 'M[R]_n | (M \is orthogonal) && (\det M == 1)].
Fact rotation_key : pred_key rotation. Proof. by []. Qed.
Canonical rotation_keyed := KeyedQualifier rotation_key.

End orthogonal_rotation_def.

Local Notation "''O_' n [ R ]" := (orthogonal n R)
  (at level 8, n at level 2, format "''O_' n [ R ]").

Local Notation "''SO_' n [ R ]" := (rotation n R)
  (at level 8, n at level 2, format "''SO_' n [ R ]").

Section orthogonal.

Variables (n' : nat) (R : rcfType).
Let n := n'.+1.

Lemma orthogonalE M : (M \is 'O_n[R]) = (M * M^T == 1). Proof. by []. Qed.

Lemma orthogonal1 : 1 \is 'O_n[R].
Proof. by rewrite orthogonalE trmx1 mulr1. Qed.

Lemma orthogonalEinv M : (M \is 'O_n[R]) = (M \is a GRing.unit) && (M^-1 == M^T).
Proof.
rewrite orthogonalE; have [Mu | notMu] /= := boolP (M \in unitmx); last first.
  by apply: contraNF notMu => /eqP /mulmx1_unit [].
by rewrite -(inj_eq (@mulrI _ M^-1 _)) ?unitrV // mulr1 mulKr.
Qed.

Lemma orthogonal_unit M : (M \is 'O_n[R]) -> (M \is a GRing.unit).
Proof. by rewrite orthogonalEinv => /andP []. Qed.

Lemma orthogonalV M : (M^T \is 'O_n[R]) = (M \is 'O_n[R]).
Proof.
by rewrite !orthogonalEinv unitmx_tr -trmxV (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma orthogonal_inv M : M \is 'O_n[R] -> M^-1 = M^T.
Proof. by rewrite orthogonalEinv => /andP [_ /eqP]. Qed.

Lemma orthogonalEC M : (M \is 'O_n[R]) = (M^T * M == 1).
Proof. by rewrite -orthogonalV orthogonalE trmxK. Qed.

Lemma orthogonal_det M : M \is 'O_n[R] -> `|\det M| = 1.
Proof.
move=> /eqP /(congr1 determinant); rewrite detM det_tr det1 => /eqP.
by rewrite sqr_norm_eq1 => /eqP.
Qed.

Lemma orthogonal_oppr_closed : oppr_closed 'O_n[R].
Proof. by move=> x; rewrite !orthogonalE linearN /= mulNr mulrN opprK. Qed.
Canonical orthogonal_is_oppr_closed := OpprPred orthogonal_oppr_closed.

Lemma orthogonal_divr_closed : divr_closed 'O_n[R].
Proof.
split => [| P Q HP HQ]; first exact: orthogonal1.
rewrite orthogonalE orthogonal_inv // trmx_mul trmxK -mulrA.
by rewrite -orthogonal_inv // mulKr // orthogonal_unit.
Qed.
Canonical orthogonal_is_mulr_closed := MulrPred orthogonal_divr_closed.
Canonical orthogonal_is_divr_closed := DivrPred orthogonal_divr_closed.
Canonical orthogonal_is_smulr_closed := SmulrPred orthogonal_divr_closed.
Canonical orthogonal_is_sdivr_closed := SdivrPred orthogonal_divr_closed.

Lemma rotationE M : (M \is 'SO_n[R]) = (M \is 'O_n[R]) && (\det M == 1). Proof. by []. Qed.

Lemma rotationV M : (M^T \is 'SO_n[R]) = (M \is 'SO_n[R]).
Proof. by rewrite rotationE orthogonalV det_tr -rotationE. Qed.

Lemma rotation1 : 1 \is 'SO_n[R].
Proof. apply/andP; by rewrite orthogonal1 det1. Qed.

Lemma rotation_det M : M \is 'SO_n[R] -> \det M = 1.
Proof. by move=> /andP[_ /eqP]. Qed.

Lemma rotation_sub : {subset 'SO_n[R] <= 'O_n[R]}.
Proof. by move=> M /andP []. Qed.

Lemma rotation_divr_closed : divr_closed 'SO_n[R].
Proof.
split => [|P Q Prot Qrot]; first exact: rotation1.
rewrite rotationE rpred_div ?rotation_sub //=.
by rewrite det_mulmx det_inv !rotation_det // divr1.
Qed.

Canonical rotation_is_mulr_closed := MulrPred rotation_divr_closed.
Canonical rotation_is_divr_closed := DivrPred rotation_divr_closed.

End orthogonal.

Lemma orthogonalP {n} R M : 
  reflect (forall i j, row i M *d row j M = (i == j)%:R) (M \is 'O_n.+1[R]).
Proof.
apply: (iffP idP) => [|H] /=.
  rewrite orthogonalE => /eqP H i j.
  move/matrixP/(_ i j) : H; rewrite /dotmul !mxE => <-.
  apply eq_bigr => k _; by rewrite !mxE.
rewrite orthogonalE.
apply/eqP/matrixP => i j; rewrite !mxE.
rewrite -H /dotmul !mxE.
apply eq_bigr => k _; by rewrite !mxE.
Qed.

Lemma euler {R : rcfType} (M : 'M[R]_3) : M \is 'SO_3[R] -> exists n : 'rV[R]_3, n *m M = n. 
Proof.
move=> MSO.
suff : \det (M - 1) = 0.
  case/eqP/det0P => n _; rewrite mulmxBr mulmx1 => /eqP.
  rewrite subr_eq0 => /eqP nM; by exists n.
suff /eqP : \det (M - 1) = - \det (M - 1).
  by rewrite -subr_eq0 opprK -mulr2n -mulr_natr mulf_eq0 pnatr_eq0 orbF => /eqP.
rewrite -{1}det_tr.
move/eqP : MSO; rewrite rotationE => /eqP/andP[].
rewrite orthogonalEC => /eqP MMT /eqP detM.
rewrite -{1}MMT -{1}(mul1r M) -mulrBl trmx_mul.
rewrite linearD /= trmx1 linearN /= trmxK -opprB.
rewrite mulmxN -scaleN1r detZ -signr_odd expr1 mulN1r.
by rewrite det_mulmx det_tr detM mul1r.
Qed.

Section triple_prod_mat.

Variable (T : ringType).

(* find a better name *)
Definition triple_prod_mat (u v w : 'rV[T]_3) :=
  \matrix_(i < 3) [eta \0 with 0 |-> u, 1 |-> v, 2%:R |-> w] i.
(*Definition triple_product_mat (u v w : vector) :=
  \matrix_(i < 3) [eta \0 with 0 |-> u, 1 |-> v, 2%:R |-> w] i.*)

Lemma triple_prod_matE a b c : 
  triple_prod_mat a b c = col_mx a (col_mx b c).
Proof.
apply/matrixP => i j; rewrite !mxE /SimplFunDelta /=.
case: ifPn => [i0|].
  case: splitP => [j0|k ik]; first by rewrite (ord1 j0).
  exfalso. move/negP: i0; apply; apply/negP; by rewrite -val_eqE /= ik.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case: splitP => [j0|]; first by rewrite (ord1 j0).
  case => -[|k Hk] //= zerotwo _; rewrite mxE.
  case: splitP => k; by rewrite (ord1 k).
case: splitP => [j0|]; first by rewrite (ord1 j0).
case => -[|[|k Hk]] //= onetwo _; rewrite mxE.
case: splitP => k; by rewrite (ord1 k).
Qed.

Lemma row'_triple_prod_mat (i : 'I_3) (u v w : 'rV[T]_3) :
  row' i (triple_prod_mat u v w) = [eta \0 with
  0 |-> \matrix_(k < 2) [eta \0 with 0 |-> v, 1 |-> w] k,
  1 |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> w] k,
  2%:R |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> v] k] i.
Proof.
case: i => [[|[|[|?]]]] ?; apply/matrixP=> [] [[|[|[|?]]]] ? j;
by rewrite !mxE.
Qed.

Lemma triple_prod_mat_perm_12 (a b c : 'rV[T]_3) :
  xrow 1 2%:R (triple_prod_mat a b c) = triple_prod_mat a c b.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma triple_prod_mat_perm_01 a b c :
  xrow 0 1 (triple_prod_mat a b c) = triple_prod_mat b a c.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma triple_prod_mat_perm_02 a b c :
 xrow 0 2%:R (triple_prod_mat a b c) = triple_prod_mat c b a.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma mulmx_triple_prod_mat M a b c : 
  triple_prod_mat a b c *m M = triple_prod_mat (a *m M) (b *m M) (c *m M).
Proof.
apply/matrixP => i j.
move: i => -[[|[|[] // ]] ?]; rewrite !mxE; apply eq_bigr => /= ? _; by rewrite mxE.
Qed.

End triple_prod_mat.

Section crossmul.

Variable R : rcfType.
Let vector := 'rV[R]_3.

(* by definition, zi = axis of joint i *)

Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS (at level 69).

Lemma normal_sym k m (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) :
  A _|_ B = B _|_ A.
Proof.
rewrite !(sameP sub_kermxP eqP) -{1}[A]trmxK -trmx_mul.
by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma normalNm k m (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) : (- A) _|_ B = A _|_ B.
Proof. by rewrite eqmx_opp. Qed.

Lemma normalmN k m (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) : A _|_ (- B) = A _|_ B.
Proof. by rewrite ![A _|_ _]normal_sym normalNm. Qed.

Lemma normalDm k m p (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) (C : 'M[R]_(p,3)) :
  (A + B _|_ C) = (A _|_ C) && (B _|_ C).
Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed.

Lemma normalmD  k m p (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) (C : 'M[R]_(p,3)) :
  (A _|_ B + C) = (A _|_ B) && (A _|_ C).
Proof. by rewrite ![A _|_ _]normal_sym normalDm. Qed.

Lemma normalvv (u v : 'rV[R]_3) : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

Lemma triple_prod_mat_mulmx (v : vector) a b c : 
  v *m (triple_prod_mat a b c)^T = 
  row_mx (v *d a)%:M (row_mx (v *d b)%:M (v *d c)%:M).
Proof.
rewrite triple_prod_matE (tr_col_mx a) (tr_col_mx b) (mul_mx_row v a^T). 
by rewrite (mul_mx_row v b^T) /dotmul -!mx11_scalar.
Qed.

(* Definition mixed_product_mat n (u : 'I_n -> 'rV[R]_n) :=  *)
(*   \matrix_(i < n, j < n) u i ord0 j. *)

(* Definition crossmul (u : 'rV[R]_n.+1) (v : 'I_n -> 'rV[R]_n.+1) : 'rV[R]_n.+1 := *)
(*   \row_(k < n) \det (mixed_product_mat (delta_mx 0 k)). *)

Definition crossmul (u v : vector) : vector :=
  \row_(k < 3) \det (triple_prod_mat (delta_mx 0 k) u v).

Local Notation "*v%R" := (@crossmul _).
Local Notation "u *v w" := (crossmul u w) (at level 40).

(*Definition crossmul (u v : vector) : vector :=
  \row_(i < 3) \det (col_mx (delta_mx (ord0 : 'I_1) i) (col_mx u v)).*)

Lemma crossmulC u v : u *v v = - (v *v u).
Proof.
rewrite /crossmul; apply/rowP => k; rewrite !mxE.
set M := (X in - \det X).
transitivity (\det (row_perm (tperm (1 : 'I__) 2%:R) M)); last first.
  by rewrite row_permE detM det_perm odd_tperm /= expr1 mulN1r.
congr (\det _); apply/matrixP => i j; rewrite !mxE permE /=.
by case: i => [[|[|[]]]] ?.
Qed.

Lemma crossmul0v u : 0 *v u = 0.
Proof.
apply/rowP=> k; rewrite !mxE; apply/eqP/det0P.
exists (delta_mx 0 1).
  apply/negP=> /eqP /(congr1 (fun f : 'M__ => f 0 1)) /eqP.
  by rewrite !mxE /= oner_eq0.
by rewrite -rowE; apply/rowP=> j; rewrite !mxE.
Qed.

Lemma crossmulv0 u : u *v 0 = 0.
Proof. by rewrite crossmulC crossmul0v oppr0. Qed.

Lemma crossmul_triple (u v w : 'rV[R]_3) :
  u *d (v *v w) = \det (triple_prod_mat u v w).
Proof.
pose M (k : 'I_3) : 'M_3 := triple_prod_mat (delta_mx 0 k) v w.
pose Mu12 := triple_prod_mat (u 0 1 *: delta_mx 0 1 + u 0 2%:R *: delta_mx 0 2%:R) v w.
rewrite (@determinant_multilinear _ _ _ (M 0) Mu12 0 (u 0 0) 1) ?mul1r
        ?row'_triple_prod_mat //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx /tnth /=.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
rewrite [\det Mu12](@determinant_multilinear _ _ _
  (M 1) (M 2%:R) 0 (u 0 1) (u 0 2%:R)) ?row'_triple_prod_mat //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
by rewrite dotmulE !big_ord_recl big_ord0 addr0 /= !mxE; simp_ord.
Qed.

Lemma crossmul_normal (u v : 'rV[R]_3) : u _|_ (u *v v).
Proof.
rewrite normalvv crossmul_triple.
rewrite (determinant_alternate (oner_neq0 _)) => [|i] //.
by rewrite !mxE.
Qed.

Lemma common_normal_crossmul u v : (u *v v) _|_ u + v.
Proof.
rewrite normalmD ![(_ *v _) _|_ _]normal_sym crossmul_normal.
by rewrite crossmulC normalmN crossmul_normal.
Qed.

(* u /\ (v + w) = u /\ v + u /\ w *)
Lemma crossmul_linear u : linear (crossmul u).
Proof.
move=> a v w; apply/rowP => k; rewrite !mxE.
pose M w := triple_prod_mat (delta_mx 0 k) u w.
rewrite (@determinant_multilinear _ _ (M _) (M v) (M w) 2%:R a 1);
  rewrite ?row'_triple_prod_mat ?mul1r ?scale1r ?mxE //=.
by apply/rowP => j; rewrite !mxE.
Qed.

Canonical crossmul_is_additive u := Additive (crossmul_linear u).
Canonical crossmul_is_linear u := AddLinear (crossmul_linear u).

Definition crossmulr u := crossmul^~ u.

Lemma crossmulr_linear u : linear (crossmulr u).
Proof.
move=> a v w; rewrite /crossmulr crossmulC linearD linearZ /=.
by rewrite opprD -scalerN -!crossmulC.
Qed.

Canonical crossmulr_is_additive u := Additive (crossmulr_linear u).
Canonical crossmulr_is_linear u := AddLinear (crossmulr_linear u).

Lemma crossmulE u v : (u *v v) = \row_j [eta \0 with
  0 |-> u 0 1 * v 0 2%:R - u 0 2%:R * v 0 1,
  1 |-> u 0 2%:R * v 0 0 - u 0 0 * v 0 2%:R,
  2%:R |-> u 0 0 * v 0 1 - u 0 1 * v 0 0] j.
Proof.
apply/rowP => i; rewrite !mxE (expand_det_row _ ord0).
rewrite !(mxE, big_ord_recl, big_ord0) !(mul0r, mul1r, addr0).
rewrite /cofactor !det_mx22 !mxE /= mul1r mulN1r opprB -signr_odd mul1r.
by simp_ord; case: i => [[|[|[]]]] //= ?; rewrite ?(mul1r,mul0r,add0r,addr0).
Qed.

Lemma crossmulNv (u v : vector) : - u *v v = - (u *v v).
Proof. by rewrite crossmulC linearN /= opprK crossmulC. Qed.

Lemma crossmulvN (a b : vector) : a *v (- b) = - (a *v b).
Proof. by rewrite crossmulC crossmulNv opprK crossmulC. Qed.

Lemma crossmulZ (a b : vector) k : ((k *: a) *v b) = k *: (a *v b).
Proof. by rewrite crossmulC linearZ /= crossmulC scalerN opprK. Qed.

Lemma crossmul0E (u v : vector) : 
  (u *v v == 0) = [forall i, [forall j, (i != j) ==> (v 0 i * u 0 j == u 0 i * v 0 j)]].
Proof.
apply/idP/idP => [/eqP|].
  rewrite crossmulE => uv0.
  apply/forallP => /= i. apply/forallP => /= j. apply/implyP => ij.
  case: (thirdI3 ij) => k Hk.
  move/rowP : uv0 => /(_ k).
  rewrite /SimplFunDelta /= !mxE => /eqP.
  case: ifPn => [/eqP k0|k0].
    rewrite subr_eq0; move: Hk ij; rewrite k0 eq_sym ifnot0 (eq_sym _ j) ifnot0.
    case/andP => /orP[] /eqP -> /orP [] /eqP -> // _ /eqP;
      [move=> ->; by rewrite mulrC | move=> <-; by rewrite mulrC].
  case: ifPn => [/eqP k1|k1].
    rewrite subr_eq0; move: Hk ij; rewrite k1 eq_sym ifnot1 (eq_sym _ j) ifnot1.
    case/andP => /orP[] /eqP -> /orP [] /eqP -> // _ /eqP;
      [move=> <-; by rewrite mulrC | move=> ->; by rewrite mulrC].
  case: ifPn => [/eqP k2|k2 _].
    rewrite subr_eq0; move: Hk ij; rewrite k2 eq_sym ifnot2 (eq_sym _ j) ifnot2.
    case/andP => /orP[] /eqP -> /orP [] /eqP -> // _ /eqP;
      [move=> ->; by rewrite mulrC | move=> <-; by rewrite mulrC].
  move: (ifnot0 k); by rewrite k0 (negbTE k1) (negbTE k2).  
move/forallP => /= H; apply/eqP/rowP => i.
rewrite crossmulE /SimplFunDelta /= !mxE; apply/eqP.
case: ifPn => [_|].
  move: (H 1) => /forallP/(_ 2%:R) /= /eqP <-; by rewrite subr_eq0 mulrC.
rewrite ifnot0 => /orP [] /eqP -> /=.
- move: (H 0) => /forallP/(_ 2%:R) /= /eqP <-; by rewrite subr_eq0 mulrC.
- move: (H 0) => /forallP/(_ 1) /= /eqP <-; by rewrite subr_eq0 mulrC.
Qed.

(* rewrite linear_sum. *)

Lemma crossmulvv (u : vector) : u *v u = 0.
Proof.
rewrite crossmulE; apply/rowP => i; rewrite !mxE; do 3 rewrite mulrC subrr.
rewrite /SimplFunDelta /=; case: ifP => [//|_]; case: ifP => [//|_]; by case: ifP.
Qed.

Lemma mulmxl_crossmulr M u v : M *m (u *v v) = u *v (M *m v).
Proof. by rewrite -(mul_rV_lin1 [linear of crossmul u]) mulmxA mul_rV_lin1. Qed.

Lemma mulmxl_crossmull M u v : M *m (u *v v) = ((M *m u) *v v).
Proof. by rewrite crossmulC mulmxN mulmxl_crossmulr -crossmulC. Qed.

(* Lemma mulmxr_crossmulr o u v : o \in so -> *)
(*   (u *v v) *m o = ((u *m o) *v (v *m o)). *)
(* Proof. *)
(* rewrite -[M]trmxK [M^T]matrix_sum_delta. *)
(* rewrite !linear_sum /=; apply: eq_bigr=> i _. *)
(* rewrite !linear_sum /=; apply: eq_bigr=> j _. *)
(* rewrite !mxE !linearZ /= trmx_delta. *)
(* rewr *)
(* rewrite -[in RHS]/(crossmulr _ _). *)
(* rewrite linear_sum /= /crossmu. *)
(* rewrite *)

(* apply/rowP => k; rewrite !mxE. *)
(* rewrite -![_ *v _](mul_rV_lin1 [linear of crossmulr _]). *)
(* rewrite -!mulmxA. *)
(* rewrite mul_rV_lin. *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr (v * M)]). *)

(* rewrite -/(mulmxr _ _) -!(mul_rV_lin1 [linear of mulmxr M]). *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr v]). *)

(* rewrite -!/(crossmulr _ _). *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr v]). *)
(* Abort. *)

(*
/mulmxr. mul_rV_lin1.
Qed.
*)

Lemma dotmul_crossmul_shift a b c : a *d (b *v c) = c *d (a *v b).
Proof. 
rewrite crossmul_triple.
rewrite -triple_prod_mat_perm_12 xrowE det_mulmx det_perm /= odd_tperm /=.
rewrite -triple_prod_mat_perm_01 xrowE det_mulmx det_perm /= odd_tperm /=.
by rewrite expr1 mulrA mulrNN 2!mul1r -crossmul_triple.
Qed.

Lemma dotmul_crossmulA u v x : u *d (v *v x) = (u *v v) *d x.
Proof. by rewrite dotmul_crossmul_shift dotmulC. Qed.

Lemma dotmul_crossmulCA a b c : a *d (b *v c) = - b *d (a *v c).
Proof. 
do 2  rewrite dotmul_crossmulA. 
by rewrite crossmulNv crossmulC.
Qed.

Lemma det_triple_prod_mat u v (x : vector) : 
  \det (triple_prod_mat u v x) = (u *v v) *d x.
Proof. by rewrite -crossmul_triple dotmul_crossmulA. Qed.

Lemma det_crossmul_dotmul M a b (x : vector) : 
  (\det M *: (a *v b)) *d x = (((a *m M) *v (b *m M)) *m M^T) *d x.
Proof.
transitivity (\det M * \det (triple_prod_mat a b x)).
  by rewrite dotmulZv -crossmul_triple dotmul_crossmulA.
transitivity (\det (triple_prod_mat (a *m M) (b *m M) (x *m M))).
  by rewrite mulrC -det_mulmx mulmx_triple_prod_mat.
transitivity (((a *m M) *v (b *m M)) *d (x *m M)).
  by rewrite det_triple_prod_mat.
by rewrite dotmul_trmx.
Qed.

Lemma mulmx_crossmul' M (a b : vector) :
  \det M *: (a *v b) = ((a *m M) *v (b *m M)) *m M^T.
Proof. apply dotmul_eq => x; exact: det_crossmul_dotmul. Qed.

Lemma mulmx_crossmul M (a b : vector) : M \is a GRing.unit ->
  (a *v b) *m (\det M *: M^-1^T) = (a *m M) *v (b *m M).
Proof.
move=> invM.
move: (mulmx_crossmul' M a b) => /(congr1 (fun x => x *m M^T^-1)).
rewrite -mulmxA mulmxV ?unitmx_tr // mulmx1 => <-.  
by rewrite -scalemxAr trmx_inv scalemxAl.
Qed.

(* "From the geometrical definition, the cross product is invariant under 
   proper rotations about the axis defined by a × b"
   https://en.wikipedia.org/wiki/Cross_product *)
Lemma mulmxr_crossmulr r u v : r \is 'O_3[R] -> 
  (u *v v) *m r = \det r *: ((u *m r) *v (v *m r)).
Proof. 
move=> rO; move: (rO).
rewrite orthogonalEinv => /andP[r1 /eqP rT].
rewrite -mulmx_crossmul //.
move/eqP: (orthogonal_det rO).
rewrite eqr_norml // => /andP[ /orP[/eqP-> |/eqP->] _];
  rewrite ?scale1r rT trmxK //.
by rewrite -scalemxAr scalerA mulrNN !mul1r scale1r.
Qed.

Lemma mulmxr_crossmulr_SO r u v : r \is 'SO_3[R] ->
  (u *v v) *m r = (u *m r) *v (v *m r).
Proof. 
rewrite rotationE => /andP[rO detr1].
by rewrite mulmxr_crossmulr // (eqP detr1) scale1r.
Qed.

Lemma double_crossmul (u v w : 'rV[R]_3) :
 u *v (v *v w) = (u *d w) *: v - (u *d v) *: w.
Proof.
(*
have [->|u_neq0] := eqVneq u 0.
  by rewrite crossmul0v !dotmul0v !scale0r subr0.
have : exists M : 'M_3, u *m M = delta_mx 0 0.

rewrite !crossmulE; apply/rowP => i.
rewrite !dotmulE !(big_ord_recl, big_ord0, addr0) !mxE /=.
simpr; rewrite oppr0 opprB addr0.
by case: i => [[|[|[|?]]]] ? //=; simp_ord => //=; rewrite mulrC ?subrr.
Qed.

rewrite !mulrDl !mulrBr !mulrA ?opprB.
*)
apply/rowP => i.
have : i \in [:: ord0 ; 1 ; 2%:R].
  have : i \in enum 'I_3 by rewrite mem_enum.
  rewrite 3!enum_ordS (_ : enum 'I_0 = nil) // -enum0.
  apply eq_enum => i'; by move: (ltn_ord i').
rewrite inE; case/orP => [/eqP ->|].
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  rewrite /tnth /=.
  move : (_ * (_ * _)) => a. move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c. move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB -addrA (addrC (- b)) 2!addrA -addrA -opprB opprK.
  move: (a + d) => f. move: (b + c) => g.
  by rewrite [in RHS](addrC e) opprD addrA addrK.
rewrite inE; case/orP => [/eqP ->|].
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite /tnth /=.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  move : (_ * (_ * _)) => a. move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c. move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB -addrA (addrC (- b)) 2!addrA -addrA -opprB opprK.
  rewrite [in RHS](addrC e) [in RHS]addrA.
  rewrite (addrC d).
  move: (a + d) => f.
  rewrite [in RHS](addrC e) [in RHS]addrA (addrC c).
  move: (b + c) => g.
  by rewrite (addrC g) opprD addrA addrK.
rewrite inE => /eqP ->.
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite /tnth /= 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  move : (_ * (_ * _)) => a. move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c. move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB -addrA (addrC (- b)) 2!addrA -addrA -opprB opprK [in RHS]addrA.
  move: (a + d) => f.
  rewrite [in RHS]addrA.
  move: (b + c) => g.
  by rewrite (addrC g) opprD addrA addrK.
Qed.

Lemma dotmul_crossmul2 (a b c : vector) : (a *v b) *v (a *v c) = (a *d (b *v c)) *: a.
Proof.
by rewrite double_crossmul (dotmulC _ a) dotmul_crossmulA crossmulvv dotmul0v 
  scale0r subr0 -dotmul_crossmulA.
Qed.

Lemma jacobi u v w : u *v (v *v w) + v *v (w *v u) + w *v (u *v v) = 0.
Proof.
(* consequence of double_crossmul *)
rewrite 3!double_crossmul.
rewrite !addrA -(addrA (_ *: v)) (dotmulC u v) -(addrC (_ *: w)) subrr addr0.
rewrite -!addrA addrC -!addrA (dotmulC w u) -(addrC (_ *: v)) subrr addr0.
by rewrite addrC dotmulC subrr.
Qed.

End crossmul.

Notation "*v%R" := (@crossmul _) : ring_scope.
Notation "u *v w" := (crossmul u w) (at level 40) : ring_scope.

Section norm.

Variables (R : rcfType) (n : nat).
Implicit Types u : 'rV[R]_n.

Definition norm u := Num.sqrt (u *d u).

Lemma normN a : norm (- a) = norm a.
Proof. by rewrite /norm dotmulNv dotmulvN opprK. Qed.

Lemma norm2 (k : R) : `| k | ^+ 2 = k ^+ 2.
Proof.
case: (ltrP 0 k) => [k0|]; first by rewrite gtr0_norm.
rewrite ler_eqVlt; case/orP => [/eqP ->|k0]; first by rewrite normr0.
by rewrite ltr0_norm // sqrrN.
Qed.

Lemma norm0 : norm 0 = 0.
Proof. by rewrite /norm dotmul0v sqrtr0. Qed.

Lemma norm_delta_mx i : norm (delta_mx 0 i) = 1.
Proof.
rewrite /norm dotmulE (bigD1 i) ?mxE //= ?eqxx mul1r big1 ?addr0 ?sqrtr1 //.
by move=> j /negPf eq_ij; rewrite mxE eqxx eq_ij mulr0.
Qed.

Lemma norm_ge0 u : norm u >= 0.
Proof. by apply sqrtr_ge0. Qed.
Hint Resolve norm_ge0.

Lemma normr_norm u : `|norm u| = norm u.
Proof. by rewrite ger0_norm. Qed.

Lemma norm_eq0 u : (norm u == 0) = (u == 0).
Proof. by rewrite -sqrtr0 eqr_sqrt // ?dotmulvv0 // le0dotmul. Qed.

Lemma normZ (k : R) u : norm (k *: u) = `|k| * norm u.
Proof.
by rewrite /norm dotmulvZ dotmulZv mulrA sqrtrM -expr2 ?sqrtr_sqr // sqr_ge0.
Qed.

Lemma dotmulvv u : u *d u = norm u ^+ 2.
Proof.
rewrite /norm [_ ^+ _]sqr_sqrtr // dotmulE sumr_ge0 //.
by move=> i _; rewrite sqr_ge0.
Qed.

End norm.

Lemma orth_preserves_dotmulvv R n v M : M \is 'O_n.+1[R] -> (v *m M) *d (v *m M) = v *d v.
Proof.
move=> HM; rewrite dotmul_trmx -mulmxA (_ : M *m _ = 1%:M) ?mulmx1 //.
by move: HM; rewrite orthogonalE => /eqP.
Qed.

Definition preserves_norm {R : rcfType} n (f : 'rV[R]_n -> 'rV[R]_n) :=
  forall v, norm (f v) = norm v.

Lemma orth_preserves_norm R n M : M \is 'O_n.+1[R] -> preserves_norm (fun x => x *m M).
Proof. move=> HM v; by rewrite /norm orth_preserves_dotmulvv. Qed.

Definition preserves_dot_products {R : rcfType} n (f : 'rV[R]_n -> 'rV[R]_n) :=
  forall a b, f a *d f b = a *d b.

Lemma orth_preserves_dotmul {R : rcfType} n (f : 'M[R]_n.+1) :
  preserves_dot_products (fun x : 'rV[R]_n.+1 => x *m f) <-> f \is 'O_n.+1[R].
Proof.
split => H.
  rewrite /preserves_dot_products in H.
  apply/orthogonalP => i j.
  by rewrite 2!rowE H dotmul_delta_mx mxE eqxx /= eq_sym.
move=> u v.
have := orth_preserves_dotmulvv (u + v) H.
rewrite mulmxDl dotmulD.
rewrite dotmulD.
rewrite orth_preserves_dotmulvv // (orth_preserves_dotmulvv v H) //.
move/(congr1 (fun x => x - v *d v)).
rewrite -!addrA subrr 2!addr0.
move/(congr1 (fun x => - (u *d u) + x)).
rewrite !addrA (addrC (- (u *d u))) subrr 2!add0r.
rewrite -2!mulr2n => /eqP.
by rewrite eqr_pmuln2r // => /eqP.
Qed.

Section norm3.

Variable R : rcfType.
Implicit Types u : 'rV[R]_3.

Lemma sqr_norm u : norm u ^+ 2 = u 0 0 ^+ 2 + u 0 1 ^+ 2 + u 0 2%:R ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum3E !expr2. Qed.

Lemma norm_crossmul' u v : (norm (u *v v)) ^+ 2 = (norm u * norm v) ^+ 2 - (u *d v) ^+ 2 .
Proof.
rewrite sqr_norm crossmulE /SimplFunDelta /= !mxE /=.
transitivity (((u 0 0)^+2 + (u 0 1)^+2 + (u 0 2%:R)^+2)
  * ((v 0 0)^+2 + (v 0 1)^+2 + (v 0 2%:R)^+2)
  - (u 0 0 * v 0 0 + u 0 1 * v 0 1 + u 0 2%:R * v 0 2%:R)^+2).
  set u0 := u 0 0. set v0 := v 0 0.
  set u1 := u 0 1. set v1 := v 0 1.
  set u2 := u 0 2%:R. set v2 := v 0 2%:R.
  rewrite !sqrrB !mulrDr !mulrDl !sqrrD.
  set A := u1 * v2. set A' := u2 * v1.
  set B := u2 * v0. set B' := u0 * v2.
  set C := u0 * v1. set C' := u1 * v0.
  set U0 := u0 ^+ 2. set U1 := u1 ^+ 2. set U2 := u2 ^+ 2.
  set V0 := v0 ^+ 2. set V1 := v1 ^+ 2. set V2 := v2 ^+ 2.
  rewrite (_ : u0 * v0 * (u1 * v1) = C * C'); last first.
    rewrite /C /C' -2!mulrA; congr (_ * _).
    rewrite mulrA mulrC; congr (_ * _); by rewrite mulrC.
  rewrite mulrDl.
  rewrite (_ : u0 * v0 * (u2 * v2) = B * B'); last first.
    rewrite /B /B' [in RHS]mulrC -!mulrA; congr (_ * _).
    rewrite mulrA -(mulrC v2); congr (_ * _); by rewrite mulrC.
  rewrite (_ : u1 * v1 * (u2 * v2) = A * A'); last first.
    rewrite /A /A' -!mulrA; congr (_ * _).
    rewrite mulrA -(mulrC v2); congr (_ * _); by rewrite mulrC.
  rewrite (_ : (u0 * v0) ^+ 2 = U0 * V0); last by rewrite exprMn.
  rewrite (_ : (u1 * v1) ^+ 2 = U1 * V1); last by rewrite exprMn.
  rewrite (_ : (u2 * v2) ^+ 2 = U2 * V2); last by rewrite exprMn.
  rewrite 4![in RHS]opprD.
  (* U0 * V0 *)
  rewrite -3!(addrA (U0 * V0)) -3![in X in _ = _ + X](addrA (- (U0 * V0))).
  rewrite [in RHS](addrAC (U0 * V0)) [in RHS](addrA (U0 * V0)) subrr add0r.
  (* U1 * V1 *)
  rewrite -(addrC (- (U1 * V1))) -(addrC (U1 * V1)) (addrCA (U1 * V0 + _)).
  rewrite -3!(addrA (- (U1 * V1))) -![in X in _ = _ + X](addrA (U1 * V1)) addrCA.
  rewrite [in RHS](addrA (- (U1 * V1))) [in RHS](addrC (- (U1 * V1))) subrr add0r.
  (* U2 * V2 *)
  rewrite -(addrC (- (U2 * V2))) -(addrC (U2 * V2)) -(addrC (U2 * V2 + _)).
  rewrite [in RHS]addrAC 2!(addrA (- (U2 * V2))) -(addrC (U2 * V2)) subrr add0r.
  (* C * C' ^+ 2 *)
  rewrite (addrC (C ^+ 2 - _)) ![in LHS]addrA.
  rewrite (addrC (C * C' *- 2)) ![in RHS]addrA; congr (_ - _).
  rewrite (_ : U0 * V2 = B' ^+ 2); last by rewrite exprMn.
  rewrite (_ : U1 * V2 = A ^+ 2); last by rewrite exprMn.
  rewrite (_ : U0 * V1 = C ^+ 2); last by rewrite exprMn.
  rewrite (_ : U1 * V0 = C' ^+ 2); last by rewrite exprMn.
  rewrite (_ : U2 * V0 = B ^+ 2); last by rewrite exprMn.
  rewrite (_ : U2 * V1 = A' ^+ 2); last by rewrite exprMn.
  (* B' ^+ 2, A ^+ 2 *)
  rewrite -(addrC (B' ^+ 2)) -!addrA; congr (_ + (_ + _)).
  rewrite !addrA.
  (* B ^+ 2 *)
  rewrite -2!(addrC (B ^+ 2)) -!addrA; congr (_ + _).
  rewrite !addrA.
  (* C ^+ 2 *)
  rewrite -(addrC (C ^+ 2)) -!addrA; congr (_ + _).
  rewrite !addrA.
  (* C' ^+ 2 *)
  rewrite -(addrC (C' ^+ 2)) -!addrA; congr (_ + _).
  rewrite !addrA.
  (* A' ^+ 2 *)
  rewrite -(addrC (A' ^+ 2)) -!addrA; congr (_ + _).
  rewrite -!mulNrn !mulr2n !opprD.
  rewrite addrC -!addrA; congr (_ + _).
  rewrite addrA.
  rewrite addrC -!addrA; congr (_ + _).
  by rewrite addrC.
rewrite exprMn -2!sqr_norm; congr (_ - _ ^+ 2).
by rewrite dotmulE sum3E.
Qed.

Lemma orth_preserves_norm_crossmul M u v : M \is 'O_3[R] ->
  norm (u *v v) = norm ((u *m M) *v (v *m M)).
Proof.
move=> MO; rewrite -(orth_preserves_norm MO (u *v v)).
by rewrite (mulmxr_crossmulr u v MO) normZ (orthogonal_det MO) mul1r.
Qed.

Lemma norm_crossmul_normal u v : u *d v = 0 ->
  norm u = 1 -> norm v = 1 -> norm (u *v v) = 1.
Proof.
move=> uv0 u1 v1; apply/eqP.
rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 //.
by rewrite norm_crossmul' u1 v1 uv0 expr0n /= subr0 mulr1 // norm_ge0.
Qed.

End norm3.

Section colinear.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition colinear (u v : vector) := u *v v == 0.

Lemma scale_colinear k v : colinear (k *: v) v.
Proof. by rewrite /colinear crossmulC linearZ /= crossmulvv scaler0 oppr0. Qed.

Lemma colinear_refl : reflexive colinear.
Proof. move=> ?; by rewrite /colinear crossmulvv. Qed.

Lemma colinear0 u : colinear 0 u.
Proof. by rewrite /colinear crossmul0v. Qed.

Lemma colinear_sym : symmetric colinear.
Proof. by move=> u v; rewrite /colinear crossmulC -eqr_opp opprK oppr0. Qed.

Lemma dotmul_eq0_crossmul_neq0 (u v : vector) : u != 0 -> v != 0 -> u *d v == 0 -> u *v v != 0.
Proof.
move=> u0 v0 uv0.
rewrite -norm_eq0 -(@eqr_expn2 _ 2) // ?norm_ge0 // exprnP expr0n -exprnP. 
rewrite norm_crossmul' (eqP uv0) expr0n subr0 -expr0n eqr_expn2 //.
by rewrite mulf_eq0 negb_or 2!norm_eq0 u0.
by rewrite mulr_ge0 // ?norm_ge0.
Qed.

Lemma colinear_trans v u w : u != 0 -> colinear v u -> colinear u w -> colinear v w.
Proof.
move=> u0.
rewrite /colinear => vu0 uw0.
move: (jacobi u v w).
rewrite (crossmulC u v) (eqP vu0) oppr0 crossmulv0 addr0.
rewrite (crossmulC w u) (eqP uw0) oppr0 crossmulv0 addr0.
rewrite double_crossmul => /eqP; rewrite subr_eq0.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite crossmul0v.
case/boolP : (w == 0) => [/eqP ->|w0]; first by rewrite crossmulv0.
have uw0' : u *d w != 0.
  apply: contraL uw0.
  by apply dotmul_eq0_crossmul_neq0.
move/eqP/(congr1 (fun x => (u *d w)^-1 *: x )).
rewrite scalerA mulVr // ?unitfE // scale1r => ->.
by rewrite scalerA crossmulC linearZ /= crossmulvv scaler0 oppr0.
Qed.

Lemma colinearZ1 (u v : vector) k : colinear u v -> colinear (k *: u) v.
Proof.
rewrite /colinear => uv.
by rewrite /colinear crossmulC linearZ /= crossmulC (eqP uv) oppr0 scaler0 oppr0.
Qed.

Lemma colinearZ2 (u v : vector) k : k != 0 -> colinear (k *: u) v -> colinear u v.
Proof.
move=> k0; rewrite /colinear.
by rewrite crossmulC linearZ /= crossmulC scalerN opprK scalemx_eq0 (negbTE k0).
Qed.

Lemma colinear_dotmul (u v : vector) : colinear u v -> (u *d v) ^+ 2 = u *d u * (v *d v).
Proof.
rewrite /colinear crossmul0E => uv0.
rewrite !dotmulE expr2 !big_distrl /=.
apply eq_bigr => i _; rewrite -!mulrA; congr (_ * _).
rewrite 2!big_distrr /=.
apply eq_bigr => j /= _; rewrite !mulrA; congr (_ * _).
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite mulrC.
move/forallP : uv0 => /(_ i)/forallP/(_ j).
by rewrite ij implyTb => /eqP.
Qed.

End colinear.

Lemma pnatr_is_a_unit {R : rcfType} n : n.+1%:R \is a @GRing.unit R.
Proof. by rewrite unitfE pnatr_eq0. Qed.

Section angle.

Variable R : rcfType.
Record angle := Angle {
  expi : R[i]; 
  _ : `| expi | == 1
}.

Lemma ReZ (x : R[i]) (k : R) : Re (k%:C * x) = k * Re x.
Proof. 
case: x => a b /=; by rewrite mul0r subr0.
Qed.

Fact angle0_subproof : `| 1 / `| 1 | | == 1 :> R[i].
Proof. by rewrite normr1 divr1 normr1. Qed.

Definition angle0 := Angle angle0_subproof.

Canonical angle_subType := [subType for expi].

Lemma normr_expi a : `|expi a| = 1.
Proof. by case: a => x /= /eqP. Qed.

Lemma expi_eq0 a : (expi a == 0) = false.
Proof. case: a => /= a /eqP Ha; apply/negbTE; by rewrite -normr_gt0 Ha. Qed.

Definition arg (x : R[i]) : angle := insubd angle0 (x / `| x |). 

Lemma argZ x (k : R) : 0 < k -> arg (k %:C * x) = arg x.
Proof.
move=> k0; rewrite /arg; congr (insubd _ _).
rewrite normrM gtr0_norm; last by rewrite ltcR.
rewrite -mulf_div divff ?mul1r //.
by rewrite lt0r_neq0 // ltcR.
Qed.

Lemma argZ_neg x (k : R) : k < 0 -> arg (k %:C * x) = arg (- x).
Proof.
move=> k0; rewrite /arg; congr (insubd _ _).
rewrite normrM ltr0_norm; last by rewrite ltcR.
rewrite -mulf_div invrN mulrN divff ?mul1r; last by rewrite ltr0_neq0 // ltcR.
by rewrite mulNr mul1r normrN mulNr.
Qed.

Lemma expiK : cancel expi arg.
Proof.
move=> a; apply/val_inj=> /=.
by rewrite insubdK ?normr_expi ?divr1 // -topredE /= normr_expi.
Qed.

Lemma expi_arg x : x != 0 -> expi (arg x) = x / `|x|.
Proof.
move=> Nx_neq0; rewrite insubdK //.
by rewrite -topredE /= normrM normfV normr_id divff // normr_eq0.
Qed.

Lemma expi_conjc (a : R[i]) : a != 0 -> (expi (arg a))^-1 = expi (arg a^*).
Proof.
case: a => a b a0 /=; rewrite expi_arg // expi_arg //; last first.
  apply: contra a0 => a0; by rewrite -conjc_eq0.
rewrite invc_norm (_ : `| _ | = 1); last first.
  by rewrite normrM normrV ?unitfE ?normr_eq0 // normr_id divrr // unitfE normr_eq0.
rewrite exprnN exp1rz mul1r. simpc. by rewrite /= sqrrN.
Qed.

Lemma mul_norm_arg x : x = `|x| * expi (arg x).
Proof. 
have [x0|x_neq0] := boolP (x == 0); first by rewrite (eqP x0) normr0 mul0r.
by rewrite expi_arg // mulrC mulfVK // normr_eq0. 
Qed.

Lemma argK x : `|x| = 1 -> expi (arg x) = x.
Proof. by move=> Nx1; rewrite expi_arg ?Nx1 ?divr1 // -normr_gt0 Nx1. Qed.

Lemma arg_Re k : 0 < k -> arg k%:C = arg 1.
Proof.
move=> k0.
apply val_inj => /=.
rewrite expi_arg; last by rewrite lt0r_neq0 // ltcR.
rewrite ger0_norm; last by rewrite ler0c ler_eqVlt k0 orbC.
rewrite divff //; last by rewrite lt0r_neq0 // ltcR.
by rewrite argK // ger0_norm // ler01.
Qed.

Definition add_angle a b := arg (expi a * expi b).
Definition opp_angle a := arg (expi a)^-1.

Lemma add_angleA : associative add_angle.
Proof.
by move=> ???; rewrite /add_angle argK ?mulrA ?argK // ?normrM 2!normr_expi mulr1.
Qed.

Lemma add_angleC : commutative add_angle.
Proof. move=> a b; by rewrite /add_angle mulrC. Qed.

Lemma add_0angle x : add_angle (arg 1) x = x.
Proof. by rewrite /add_angle argK ?normr1 ?mul1r ?expiK. Qed.

Lemma expi_is_unit x : expi x \is a GRing.unit. 
Proof. by rewrite unitfE -normr_eq0 normr_expi oner_eq0. Qed.

Lemma add_Nangle x : add_angle (opp_angle x) x = arg 1.
Proof. 
rewrite /add_angle /opp_angle argK; first by rewrite mulVr // expi_is_unit.
by rewrite normrV ?expi_is_unit // normr_expi invr1.
Qed.

Definition angle_eqMixin := [eqMixin of angle by <:].
Canonical angle_eqType := EqType angle angle_eqMixin.
Definition angle_choiceMixin := [choiceMixin of angle by <:].
Canonical angle_choiceType := ChoiceType angle angle_choiceMixin.
Definition angle_ZmodMixin := ZmodMixin add_angleA add_angleC add_0angle add_Nangle.
Canonical angle_ZmodType := ZmodType angle angle_ZmodMixin.

Lemma add_angleE (a b : angle) : a + b = add_angle a b.
Proof. done. Qed.

Definition cos a := Re (expi a).
Definition sin a := Im (expi a).
Definition tan a := sin a / cos a.

Lemma cos1sin0 a : cos a = 1 -> sin a = 0.
Proof.
case: a => -[a b] ab1; rewrite /cos /sin /= => a1; move: ab1.
rewrite {}a1 normc_def /= expr1n => /eqP[] /(congr1 (fun x => x ^+ 2)).
rewrite expr1n sqr_sqrtr; last by rewrite addr_ge0 // ?ler01 // sqr_ge0.
by move/eqP; rewrite eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
Qed.

Lemma cos0sin1 a : cos a = 0 -> `| sin a | = 1.
Proof.
case: a => -[a b] ab1; rewrite /cos /sin /= => a1; move: ab1.
rewrite {}a1 normc_def /= expr0n add0r => /eqP[]; by rewrite sqrtr_sqr.
Qed.

Lemma cos_max (a : angle) : `| cos a | <= 1.
Proof. rewrite -lecR (ler_trans (normc_ge_Re _)) //; by case: a => ? /= /eqP ->. Qed. 

Lemma cos2Dsin2 a : (cos a) ^+ 2 + (sin a) ^+ 2 = 1.
Proof.
move: (add_Re2_Im2 (expi a)).
by rewrite normr_expi expr1n => /(congr1 (fun x => Re x)) => /= <-.
Qed.

Lemma abs_sin (a : angle) : `| sin a | = Num.sqrt (1 - cos a ^+ 2).
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) //; last by rewrite sqrtr_ge0.
rewrite -normrX ger0_norm; last by rewrite sqr_ge0.
rewrite sqr_sqrtr; last by rewrite lter_sub_addr add0r -norm2 exprn_ilte1 // cos_max.
by rewrite -subr_eq opprK addrC cos2Dsin2.
Qed.

(*
sin(t) = ( exp(it) - exp(-it) )/2i
cos(t) = ( exp(it) + exp(-it) )/2
*)

Lemma expiD a b : expi (a + b) = expi a * expi b.
Proof.
move: a b => [a a1] [b b1] /=.
by rewrite /add_angle /= argK // normrM  (eqP a1) (eqP b1) mulr1.
Qed.

Lemma expi_cos_sin a : expi a = cos a +i* sin a.
Proof. by case: a => -[a0 a1] Ha; rewrite /cos /sin. Qed.

Lemma sinD a b : sin (a + b) = sin a * cos b + cos a * sin b.
Proof. by rewrite {1}/sin expiD 2!expi_cos_sin /= addrC. Qed.

Lemma cosD a b : cos (a + b) = cos a * cos b - sin a * sin b.
Proof. by rewrite {1}/cos expiD 2!expi_cos_sin /= addrC. Qed.

Definition atan (x : R) : angle := arg (x +i* 1) *~ sgz (x).
Definition asin (x : R) : angle := arg (Num.sqrt (1 - x^2) +i* x).
Definition acos (x : R) : angle := arg (x +i* Num.sqrt (1 - x^2)).

Definition pi := arg (-1).

Definition pihalf := (arg (0 +i* 1) : angle).

Lemma expipi : expi pi = -1. Proof. by rewrite argK ?normrN1. Qed.

Lemma arg1 : arg 1 = 0.
Proof. apply val_inj => /=; by rewrite argK // normr1. Qed.

Lemma cos0 : cos 0 = 1.
Proof. by rewrite /cos -arg1 argK // ger0_norm // ler01. Qed.

Lemma sin0 : sin 0 = 0.
Proof.
move: (cos2Dsin2 0); rewrite cos0 expr2 mulr1 => /eqP.
by rewrite eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
Qed.

Lemma expi0 : expi 0 = 1.
Proof. by rewrite expi_cos_sin cos0 sin0. Qed.

Lemma cos1_angle0 a : cos a = 1 -> a = 0.
Proof.
case: a; rewrite /cos /=; case => x y xy /= x1. 
have /eqP y0 : y == 0.
  move: xy; rewrite x1 normc_def /= expr1n eq_complex /= eqxx andbT.
  rewrite -(@eqr_expn2 _ 2%N) // ?ler01 //; last by rewrite sqrtr_ge0.
  rewrite sqr_sqrtr; last by apply addr_ge0 => //; rewrite ?ler01 // sqr_ge0.
  by rewrite expr1n eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0.
by apply val_inj => /=; rewrite x1 y0 expi0 complexr0.
Qed.

Lemma cosN1_angle0 a : cos a = -1 -> a = pi.
Proof.
case: a => a Ha; rewrite /cos /=; case: a Ha => x y xy /= x1. 
have y0 : y = 0.
  move: xy.
  rewrite x1 normc_def /= sqrrN expr1n eq_complex /= eqxx andbT.
  rewrite -(@eqr_expn2 _ 2%N) // ?ler01 //; last by rewrite sqrtr_ge0.
  rewrite sqr_sqrtr; last by apply addr_ge0 => //; rewrite ?ler01 // sqr_ge0.
  by rewrite expr1n eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
apply val_inj => /=; rewrite x1 y0 expipi complexr0.
by rewrite real_complexE; apply/eqP; rewrite eq_complex /= oppr0 2!eqxx.
Qed.

Lemma sin0cos1 a : sin a = 0 -> `| cos a | = 1.
Proof.
case: a => -[a b] ab1; rewrite /cos /sin /= => a1; move: ab1.
rewrite {}a1 normc_def /= expr0n => /eqP[] /(congr1 (fun x => x ^+ 2)).
rewrite expr1n sqr_sqrtr; last by rewrite addr_ge0 // ?ler01 // sqr_ge0.
by move/eqP; rewrite addr0 -{1}(@expr1n _ 2%N) -norm2 eqr_expn2 // ?ler01 // => /eqP.
Qed.

Lemma arg0_inv (a : R[i]) : `|a| = 1 -> arg a = 0 -> a = 1.
Proof.
case: a => x y a1 H.
by rewrite -expi0 -H expi_arg ?a1 ?divr1 // -normr_eq0 a1 oner_eq0.
Qed.

Lemma argpi_inv (a : R[i]) : `|a| = 1 -> arg a = pi -> a = -1.
Proof.
case: a => x y a1 H.
by rewrite -expipi -H expi_arg ?a1 ?divr1 // -normr_eq0 a1 oner_eq0.
Qed.

Lemma expi2pi : expi (pi + pi) = 1.
Proof. by rewrite /pi expiD argK // ?normrN1 // mulrNN mulr1. Qed.

Lemma expi_inj : injective expi.
Proof. move=> [a a1] [b b1] /= ab; by apply/val_inj. Qed.

Lemma pi2 : pi *+ 2 = 0.
Proof. apply expi_inj => //; by rewrite expi2pi -arg1 argK // normr1. Qed.

(* The following lemmas are true in specific domains only, such as
]-pi/2, pi/2[ = [pred a | cos a > 0] 
]0, pi[ = [pred a | sin a > 0] 
[-pi/2, pi/2[ = [pred a | cos a > 0] 
[0, pi] = [pred a | sin a >= 0] 
[0, pi[ = [pred a | sin a >= 0 && a != pi] 
*)

Definition Opi_closed := [pred a | 0 <= sin a].

(*cancel acos cos*)
Lemma acosK (r : R) : -1 <= r <= 1 -> cos (acos r) = r.
Proof. 
move=> rdom.
rewrite /acos /cos argK // normc_def /= sqr_sqrtr; last first.
  by rewrite subr_ge0 -ler_sqrt // ?ltr01 // sqrtr1 -exprnP sqrtr_sqr ler_norml.
by rewrite addrC subrK sqrtr1.
Qed.

(*cancel cos acos*)
Lemma cosK a : a \in Opi_closed -> acos (cos a) = a.
Proof.
rewrite inE => adom.
rewrite /acos /cos /= expi_cos_sin /= -(cos2Dsin2 a) addrAC subrr add0r.
by rewrite sqrtr_sqr /= ger0_norm // -expi_cos_sin expiK.
Qed.

(*cancel asin sin*)
Lemma asinK r : -1 <= r <= 1 -> sin (asin r) = r.
Proof.
move=> rdom.
rewrite /sin /asin argK // normc_def /= sqr_sqrtr; last first.
  by rewrite subr_ge0 -ler_sqrt // ?ltr01 // sqrtr1 -exprnP sqrtr_sqr ler_norml.
by rewrite subrK sqrtr1.
Qed.

Lemma sin_acos x : `|x| <= 1 -> sin (acos x) = Num.sqrt (1 - x ^ 2).
Proof.
move=> Nx_le1; rewrite /sin /acos argK //; simpc; rewrite sqr_sqrtr.
  by rewrite addrC addrNK sqrtr1 //.
by rewrite subr_ge0 -[_ ^ _]real_normK ?num_real // exprn_ile1.
Qed.

Definition scalea k a : R[i] := (expi a) ^+ k.

Lemma scalea_proof k a : `| scalea k a | == 1.
Proof. by rewrite /scalea normrX normr_expi expr1n. Qed.

Definition scale_angle k a := Angle (scalea_proof k a).

Lemma scale_angleD k1 k2 a : 
  scale_angle (k1 + k2) a = (scale_angle k1 a) + (scale_angle k2 a).
Proof. apply val_inj => /=; by rewrite /add_angle expiD /scalea exprD. Qed.

Lemma scale_angle0a a : scale_angle 0 a = 0.
Proof. apply val_inj => /=; by rewrite /scalea expr0 expi0. Qed.

Lemma scale_angle1a a : scale_angle 1 a = a.
Proof. apply val_inj => /=; by rewrite /scalea expr1. Qed.

Lemma moivre n a :
  (cos a +i* sin a) ^+n = cos (scale_angle n a) +i* sin (scale_angle n a).
Proof.
rewrite -!expi_cos_sin.
elim: n => [|n ih]; first by rewrite scale_angle0a expr0 expi0.
by rewrite exprS ih -addn1 scale_angleD expiD scale_angle1a mulrC.
Qed.


Lemma Re_half_anglec (x : R[i]) : `|x| = 1 -> 0 <= 1 + Re x.
Proof.
move=> x1; rewrite -ler_subl_addr add0r.
suff : `| Re x |%:C <= `|x|; last by rewrite normc_ge_Re.
rewrite x1 -lecR; apply: ler_trans; by rewrite lecR ler_normr lerr orbT.
Qed.

Lemma Im_half_anglec (x : R[i]) : `|x| = 1 -> Re x <= 1.
Proof.
move=> x1; suff : `| Re x |%:C <= `|x|; last by rewrite normc_ge_Re.
rewrite x1 -lecR; apply: ler_trans; by rewrite lecR ler_normr lerr.
Qed.

Lemma eq_angle (a b : angle) : (a == b) = ((cos a == cos b) && (sin a == sin b)).
Proof.
case: a b => [[a b] ab] [[c d] cd].
rewrite /cos /= /sin /=.
apply/idP/idP; first by case/eqP => -> ->; rewrite 2!eqxx.
case/andP => /eqP ac /eqP bd.
apply/eqP/val_inj => /=; by rewrite ac bd.
Qed.

Definition half_anglec (x : R[i]) :=
  if 0 <= Im x then 
    Num.sqrt ((1 + Re x) / 2%:R) +i* Num.sqrt ((1 - Re x) / 2%:R)
  else
    Num.sqrt ((1 + Re x) / 2%:R) -i* Num.sqrt ((1 - Re x) / 2%:R).

Lemma norm_half_anglec (x : R[i]) : `|x| = 1 -> `|half_anglec x| == 1.
Proof.
move=> x1.
rewrite /half_anglec.
case: ifP => a0.
  rewrite normc_def /= sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // Re_half_anglec.
  rewrite sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
  by rewrite mulrC (mulrC (1 - Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatr_is_a_unit // sqrtr1.
rewrite normc_def /= sqr_sqrtr; last first.
  by rewrite divr_ge0 // ?Re_half_anglec // ler0n.
rewrite sqrrN sqr_sqrtr; last first.
  by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
by rewrite mulrC (mulrC (1 - Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatr_is_a_unit // sqrtr1.
Qed.

Definition half_angle (x : angle) := Angle (norm_half_anglec (normr_expi x)).

Lemma halfP (a : angle) : half_angle a + half_angle a = a.
Proof.
apply/eqP.
rewrite eq_angle; apply/andP; split.
  rewrite /cos /= add_angleE /add_angle /half_angle /= argK; last first.
    by rewrite normrM (eqP (norm_half_anglec (normr_expi _))) mulr1.
  rewrite /half_anglec. simpc. rewrite /=.
  move=> [:tmp].
  case: ifP => a0 /=.
    abstract: tmp.
    rewrite -2!expr2 sqr_sqrtr; last first.
      by rewrite divr_ge0 // ?Re_half_anglec // ?normr_expi // ler0n.
    rewrite sqr_sqrtr; last first.
      by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec // normr_expi.
    rewrite mulrC (mulrC (_ - _)) -mulrBr opprB addrC addrA subrK -mulr2n.
    by rewrite -(mulr_natl (Re _)) mulrA mulVr ?pnatr_is_a_unit // mul1r eqxx.
  rewrite mulNr mulrN opprK; exact: tmp.
rewrite /sin /= add_angleE /add_angle /half_angle /= argK; last first.
  by rewrite normrM (eqP (norm_half_anglec (normr_expi _))) mulr1.
rewrite /half_anglec. simpc. rewrite /=.
case: ifPn => a0 /=.
  rewrite mulrC -mulr2n -mulr_natl sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
  rewrite mulrAC sqrtrM; last by rewrite Re_half_anglec // normr_expi.
  rewrite -!mulrA -sqrtrM; last by rewrite invr_ge0 ler0n.
  rewrite -expr2 sqrtr_sqr !mulrA mulrC normrV ?unitfE ?pnatr_eq0 //.
  rewrite normr_nat !mulrA mulVr ?mul1r ?unitfE ?pnatr_eq0 //.
  rewrite -sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
  rewrite -subr_sqr expr1n.
  rewrite -(@eqr_expn2 _ 2%N) //; last by rewrite sqrtr_ge0.
  rewrite sqr_sqrtr //; last first.
    by rewrite subr_ge0 -(cos2Dsin2 a) /cos ler_paddr // sqr_ge0.
  by rewrite -(cos2Dsin2 a) /cos addrAC subrr add0r eqxx.
rewrite mulrN mulNr -opprB opprK eqr_oppLR.
rewrite mulrC -mulr2n -mulr_natl sqrtrM; last by rewrite Re_half_anglec // normr_expi.
rewrite mulrAC sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
rewrite -!mulrA -sqrtrM; last by rewrite invr_ge0 ler0n.
rewrite -expr2 sqrtr_sqr !mulrA mulrC normrV ?unitfE ?pnatr_eq0 //.
rewrite normr_nat !mulrA mulVr ?mul1r ?unitfE ?pnatr_eq0 //.
rewrite -sqrtrM; last by rewrite Re_half_anglec // normr_expi.
rewrite mulrC -subr_sqr expr1n.
rewrite -(@eqr_expn2 _ 2%N) //; last 2 first.
  by rewrite sqrtr_ge0.
  by rewrite ltrW // oppr_gt0 ltrNge.
rewrite sqr_sqrtr //; last first.
  by rewrite -(cos2Dsin2 a) addrAC subrr add0r sqr_ge0.
by rewrite sqrrN -(cos2Dsin2 a) addrAC subrr add0r.
Qed.

Definition vec_angle v w : angle := arg (v *d w +i* norm (v *v w)).

Lemma vec_anglev0 (a : 'rV[R]_3) : vec_angle a 0 = vec_angle 0 0. 
Proof. by rewrite /vec_angle 2!dotmulv0 2!crossmulv0. Qed.

Lemma vec_angle0v (a : 'rV[R]_3) : vec_angle 0 a = vec_angle 0 0. 
Proof. by rewrite /vec_angle 2!dotmul0v 2!crossmul0v. Qed.

Definition vec_angle0 := (vec_anglev0, vec_angle0v).

Lemma cos_vec_angleNv a b : a != 0 -> b != 0 -> 
  cos (vec_angle (- a) b) = - cos (vec_angle a b).
Proof.
move=> a0 b0.
rewrite /vec_angle /cos crossmulNv normN expi_arg; last first.
  rewrite eq_complex /= negb_and.
  case/boolP : (a *d b == 0) => ab; last by rewrite dotmulNv oppr_eq0 ab.
  by rewrite dotmulNv (eqP ab) oppr0 eqxx /= norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite expi_arg; last first.
  rewrite eq_complex /= negb_and.
  by case/boolP : (_ == 0) => ab //=; rewrite norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite (_ : `|- a *d b +i* norm (a *v b)| = `|a *d b +i* norm (a *v b)|); last first.
  by rewrite 2!normc_def /= dotmulNv sqrrN.
by rewrite /= mul0r oppr0 mulr0 subr0 expr0n /= addr0 subr0 dotmulNv mulNr.
Qed.

Lemma cos_vec_anglevN a b : a != 0 -> b != 0 -> 
  cos (vec_angle a (- b)) = - cos (vec_angle a b).
Proof.
move=> a0 b0.
rewrite /vec_angle /cos crossmulC crossmulNv opprK dotmulvN [in LHS]expi_arg; last first.
  rewrite eq_complex /= negb_and.
  case/boolP : (a *d b == 0) => ab. 
    by rewrite oppr_eq0 (eqP ab) eqxx /= norm_eq0 dotmul_eq0_crossmul_neq0 // dotmulC.
  by rewrite oppr_eq0 ab.
rewrite expi_arg; last first.
  rewrite eq_complex /= negb_and.
  by case/boolP : (_ == 0) => ab //=; rewrite norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite (_ : `|- (a *d b) +i* norm (b *v a)| = `|a *d b +i* norm (a *v b)|); last first.
  by rewrite 2!normc_def /= sqrrN crossmulC normN.
by rewrite /= mul0r oppr0 mulr0 expr0n /= addr0 subr0 mulr0 subr0 mulNr.
Qed.

Lemma vec_angle_switch a b : vec_angle a b = vec_angle b a.
Proof. by rewrite /vec_angle dotmulC crossmulC normN. Qed.

Lemma vec_angleZ (u v : 'rV_3) k : 0 < k ->
  vec_angle u (k *: v) = vec_angle u v.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite scaler0 !vec_angle0.
move=> k0; by rewrite /vec_angle dotmulvZ linearZ /= normZ ger0_norm ?ltrW // complexZ argZ.
Qed.

Lemma vec_angleZ_neg (u v : 'rV[R]_3) k : k < 0 ->
  vec_angle u (k *: v) = vec_angle (- u) v.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite oppr0 !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite scaler0 !vec_angle0.
move=> k0.
rewrite /vec_angle dotmulvZ linearZ /= normZ ltr0_norm //.
by rewrite mulNr complexZ argZ_neg // opp_conjc dotmulNv crossmulNv normN.
Qed.

Lemma vec_anglevv u : u != 0 -> vec_angle u u = 0.
Proof.
move=> u0.
rewrite /vec_angle /= crossmulvv norm0 complexr0 dotmulvv arg_Re ?arg1 //.
by rewrite ltr_neqAle sqr_ge0 andbT eq_sym sqrf_eq0 norm_eq0.
Qed.

Lemma polarization_identity (a b : 'rV[R]_3) : 
  a *d b = 1 / 4%:R * (norm (a + b) ^+ 2 - norm (a - b) ^+ 2).
Proof.
apply: (@mulrI _ 4%:R); first exact: pnatr_is_a_unit.
rewrite [in RHS]mulrA div1r divrr ?pnatr_is_a_unit // mul1r.
rewrite -2!dotmulvv dotmulD dotmulD mulr_natl (addrC (a *d a)).
rewrite (_ : 4 = 2 + 2)%N // mulrnDr -3![in RHS]addrA; congr (_ + _).
rewrite opprD addrCA 2!addrA -(addrC (a *d a)) subrr add0r.
rewrite addrC opprD 2!dotmulvN dotmulNv opprK subrK.
by rewrite -mulNrn opprK.
Qed.

Lemma dotmul_cos u v : u *d v = norm u * norm v * cos (vec_angle u v).
Proof.
wlog /andP[u0 v0] : u v / (u != 0) && (v != 0).
  case/boolP : (u == 0) => [/eqP ->{u}|u0]; first by rewrite dotmul0v norm0 !mul0r.
  case/boolP : (v == 0) => [/eqP ->{v}|v0]; first by rewrite dotmulv0 norm0 !(mulr0,mul0r).
  apply; by rewrite u0.
rewrite /vec_angle /cos. set x := _ +i* _.
case/boolP  : (x == 0) => [|x0].
  rewrite eq_complex /= => /andP[/eqP H1 H2].
  exfalso.
  move: H2; rewrite norm_eq0 => /colinear_dotmul/esym.
  rewrite H1 expr0n (_ : (_ == _)%:R = 0) // => /eqP.
  by rewrite 2!dotmulvv mulf_eq0 2!expf_eq0 /= 2!norm_eq0 (negbTE u0) (negbTE v0).
case/boolP : (u *d v == 0) => uv0.
  by rewrite (eqP uv0) expi_arg //= (eqP uv0) !mul0r -mulrN opprK mulr0 addr0 mulr0.
rewrite expi_arg //.
rewrite normc_def Re_scale; last first.
  rewrite sqrtr_eq0 -ltrNge -(addr0 0) ltr_le_add //.
    by rewrite exprnP /= ltr_neqAle sqr_ge0 andbT eq_sym -exprnP sqrf_eq0.
  by rewrite /= sqr_ge0.
rewrite /=.
rewrite norm_crossmul' addrC subrK sqrtr_sqr ger0_norm; last first.
  by rewrite mulr_ge0 // norm_ge0.
rewrite mulrA mulrC mulrA mulVr ?mul1r //.
by rewrite unitrMl // unitfE norm_eq0.
Qed.

Lemma dotmul0_vec_angle u v : u != 0 -> v != 0 -> 
  u *d v = 0 -> `| sin (vec_angle u v) | = 1.
Proof.
move=> u0 v0 /eqP.
rewrite dotmul_cos mulf_eq0 => /orP [ | /eqP/cos0sin1 //].
by rewrite mulf_eq0 2!norm_eq0 (negbTE u0) (negbTE v0).
Qed.

Lemma normD a b : norm (a + b) = 
  Num.sqrt (norm a ^ 2 + norm a * norm b * cos (vec_angle a b) *+ 2 + norm b ^ 2).
Proof.
rewrite /norm dotmulD {1}dotmulvv -exprnP sqr_sqrtr ?le0dotmul //.
by rewrite -exprnP sqr_sqrtr ?le0dotmul // (dotmul_cos a b).
Qed.

Lemma normB a b : norm (a - b) = 
  Num.sqrt (norm a ^ 2 + norm a * norm b * cos (vec_angle a b) *- 2 + norm b ^ 2).
Proof.
rewrite /norm dotmulD {1}dotmulvv -exprnP sqr_sqrtr ?le0dotmul //.
rewrite -exprnP sqr_sqrtr ?le0dotmul // !dotmulvv !sqrtr_sqr normN.
rewrite dotmulvN dotmul_cos ger0_norm ?norm_ge0 // ger0_norm ?norm_ge0 //.
by rewrite mulNrn.
Qed.

Lemma cosine_law' a b c :
  norm (b - c) ^+ 2 = norm (c - a) ^+ 2 + norm (b - a) ^+ 2 -
  norm (c - a) * norm (b - a) * cos (vec_angle (b - a) (c - a)) *+ 2.
Proof.
rewrite -[in LHS]dotmulvv (_ : b - c = b - a - (c - a)); last first.
  by rewrite -!addrA opprB (addrC (- a)) (addrC a) addrK.
rewrite dotmulD dotmulvv [in X in _ + _ + X = _]dotmulvN dotmulNv opprK dotmulvv dotmulvN.
rewrite addrAC (addrC (norm (b - a) ^+ _)); congr (_ + _).
by rewrite dotmul_cos mulNrn (mulrC (norm (b - a))).
Qed.

Lemma cosine_law a b c : norm (c - a) != 0 -> norm (b - a) != 0 ->
  cos (vec_angle (b - a) (c - a)) = 
  (norm (b - c) ^+ 2 - norm (c - a) ^+ 2 - norm (b - a) ^+ 2) /
  (norm (c - a) * norm (b - a) *- 2).
Proof.
move=> H0 H1.
rewrite (cosine_law' a b c) -2!addrA addrCA -opprD subrr addr0.
rewrite -mulNrn -mulr_natr mulNr -mulrA -(mulrC 2%:R) mulrA.
rewrite -mulNrn -[in X in _ = - _ / X]mulr_natr 2!mulNr invrN mulrN opprK.
rewrite mulrC mulrA mulVr ?mul1r // unitfE mulf_eq0 negb_or pnatr_eq0 andbT.
by rewrite mulf_eq0 negb_or H0 H1.
Qed.

Lemma norm_crossmul u v : 
  norm (u *v v) = norm u * norm v * `| sin (vec_angle u v) |.
Proof.
suff /eqP : (norm (u *v v))^+2 = (norm u * norm v * `| sin (vec_angle u v) |)^+2.
  rewrite -eqr_sqrt ?sqr_ge0 // 2!sqrtr_sqr ger0_norm; last by rewrite norm_ge0.
  rewrite ger0_norm; first by move/eqP.
  by rewrite -mulrA mulr_ge0 // ?norm_ge0 // mulr_ge0 // ? norm_ge0.
rewrite norm_crossmul' dotmul_cos !exprMn.
apply/eqP; rewrite subr_eq -mulrDr.
rewrite real_normK; last first.
  rewrite /sin; case: (expi _) => a b /=; rewrite realE //.
  case: (lerP 0 b) => //= b0; by rewrite ltrW.
by rewrite addrC cos2Dsin2 mulr1.
Qed.

Lemma vec_angle0_inv u v : norm u = 1 -> norm v = 1 ->
  vec_angle u v = 0 -> u = v.
Proof.
move=> u1 v1; rewrite /vec_angle => uv.
have : `|u *d v +i* norm (u *v v)| = 1.
  rewrite {1}dotmul_cos {1}norm_crossmul u1 v1 3!mul1r normc_def /=.
  apply/eqP; rewrite -(@eqr_expn2 _ 2%N) //; last by rewrite ler0c sqrtr_ge0.
  by rewrite norm2 cos2Dsin2 sqrtr1.
move/arg0_inv/(_ uv)/eqP; rewrite eq_complex /= => /andP[].
rewrite dotmul_cos u1 v1 2!mul1r => uv1 _.
apply/eqP.
rewrite -subr_eq0 -norm_eq0 normB (eqP uv1) mulr1 u1 v1 mulr1 -exprnP.
by rewrite expr1n addrAC {1 2}(_ : 1 = 1%:R) // -natrD subrr sqrtr0.
Qed.

Lemma vec_anglepi_inv u v : norm u = 1 -> norm v = 1 ->
  vec_angle u v = pi -> u = - v.
Proof.
move=> u1 v1; rewrite /vec_angle => uv.
have : `|u *d v +i* norm (u *v v)| = 1.
  rewrite {1}dotmul_cos {1}norm_crossmul u1 v1 3!mul1r normc_def /=.
  apply/eqP; rewrite -(@eqr_expn2 _ 2%N) //; last by rewrite ler0c sqrtr_ge0.
  by rewrite norm2 cos2Dsin2 sqrtr1.
move/argpi_inv/(_ uv)/eqP; rewrite eq_complex /= => /andP[].
rewrite dotmul_cos u1 v1 2!mul1r => uv1 _.
apply/eqP.
rewrite -subr_eq0 -norm_eq0 normD opprK (eqP uv1) u1 v1 !mul1r.
by rewrite -exprnP expr1n addrAC mulr2n -opprD subrr sqrtr0.
Qed.

Lemma cos_vec_angle a b : norm a != 0 -> norm b != 0 -> 
  `| cos (vec_angle a b) | = Num.sqrt (1 - (norm (a *v b) / (norm a * norm b)) ^+ 2).
Proof.
move=> Ha Hb.
rewrite norm_crossmul mulrAC divrr // ?mul1r; last by rewrite unitfE mulf_neq0.
rewrite norm2.
move: (cos2Dsin2 (vec_angle a b)) => /eqP; rewrite eq_sym -subr_eq => /eqP ->.
by rewrite sqrtr_sqr.
Qed.

Lemma orth_preserves_vec_angle M v w : M \is 'O_3[R] ->
  vec_angle v w = vec_angle (v *m M) (w *m M).
Proof.
move=> HM.
by rewrite /vec_angle (proj2 (orth_preserves_dotmul _) HM v w) -orth_preserves_norm_crossmul.
Qed.

End angle.

Section normalize_orthogonalize.

Variables (R : rcfType) (n : nat).
Let vector := 'rV[R]_n.

Definition normalize (v : vector) := 1 / norm v *: v.

Lemma normalizeI (a : vector) : normalize (normalize a) = normalize a.
Proof.
rewrite /normalize.
case/boolP : (norm a == 0) => a0.
  rewrite norm_eq0 in a0; by rewrite (eqP a0) 2!scaler0.
rewrite norm_eq0 in a0; rewrite normZ scalerA; congr (_ *: _).
rewrite normrM ger0_norm // ?ler01 // normrV ?unitfE ?norm_eq0 //.
rewrite ger0_norm // ?norm_ge0 //.
rewrite (div1r (norm a)) mulVr ?unitfE ?norm_eq0 //.
by rewrite div1r invr1 div1r.
Qed.

Lemma norm_normalize v : v != 0 -> norm (normalize v) = 1.
Proof.
move=> v0; rewrite /normalize normZ ger0_norm; last first.
  by rewrite divr_ge0 // ?ler01 // norm_ge0.
by rewrite div1r mulVr // unitf_gt0 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
Qed.

Lemma normalize_eq0 v : (norm (normalize v) == 0) = (norm v == 0).
Proof.
apply/idP/idP => [|/eqP v0].
  rewrite norm_eq0.
  case/boolP : (v == 0) => [/eqP -> | v0]; first by rewrite norm0.
  by rewrite -norm_eq0 norm_normalize // (negbTE (@oner_neq0 _)).
by rewrite /normalize v0 div1r invr0 scale0r norm0.
Qed.

Lemma norm_scale_normalize u : norm u *: normalize u = u.
Proof.
case/boolP : (u == 0) => [/eqP -> {u}|u0]; first by rewrite norm0 scale0r.
by rewrite /normalize scalerA div1r divrr ?scale1r // unitfE norm_eq0.
Qed.

Lemma dotmul_normalize u : u *d normalize u = norm u.
Proof.
case/boolP : (u == 0) => [/eqP ->{u}|u0]; first by rewrite norm0 dotmul0v.
rewrite -{1}(norm_scale_normalize u) dotmulZv dotmulvv norm_normalize //.
by rewrite expr1n mulr1.
Qed.

Definition orthogonalize (u v : 'rV[R]_n) : 'rV[R]_n := 
  v - (v *d normalize u) *: normalize u.

Lemma orthogonalizeP u v : u *d orthogonalize u v = 0.
Proof.
rewrite dotmulDr dotmulvN dotmulvZ dotmul_normalize mulrC -dotmulvZ.
by rewrite norm_scale_normalize dotmulC subrr.
Qed.

End normalize_orthogonalize.

Lemma orthogonalize_neq0 {R : rcfType} (u v : 'rV[R]_3) : 
  ~~ colinear u v -> orthogonalize u v != 0.
Proof.
move=> uv.
rewrite /orthogonalize subr_eq0; apply: contra uv => /eqP ->.
by rewrite colinear_sym /normalize scalerA scale_colinear.
Qed.

Section triad.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.

Variable a b c : coordinate.
Hypothesis ab : a != b.
Hypothesis abc : ~~ colinear (b - a) (c - a).

Definition xtriad := normalize (b - a).

Definition ytriad := normalize (orthogonalize xtriad (c - a)).

Definition triad := (xtriad, ytriad, xtriad *v ytriad).

Let ac : a != c.
Proof. by apply: contra abc => /eqP ->; rewrite subrr /colinear crossmulv0. Qed.

Lemma xtriad_norm : norm xtriad = 1.
Proof. by rewrite /xtriad norm_normalize // subr_eq0 eq_sym. Qed.

Lemma xtriad_neq0 : xtriad != 0.
Proof. by rewrite -norm_eq0 xtriad_norm oner_neq0. Qed.

Lemma ytriad_norm : norm ytriad = 1.
Proof. 
rewrite /ytriad norm_normalize // orthogonalize_neq0 // /xtriad /normalize.
apply: contra abc; apply colinearZ2.
by rewrite div1r invr_eq0 norm_eq0 subr_eq0 eq_sym.
Qed.

Lemma ytriad_neq0 : ytriad != 0.
Proof. by rewrite -norm_eq0 ytriad_norm oner_neq0. Qed.

Lemma xytriad_ortho : xtriad *d ytriad = 0.
Proof. by rewrite /= /xtriad /ytriad {2}/normalize dotmulvZ orthogonalizeP mulr0. Qed.

Definition ztriad := xtriad *v ytriad.

Lemma ztriad_norm : norm ztriad = 1.
Proof. by rewrite norm_crossmul_normal // ?xtriad_norm // ?ytriad_norm // xytriad_ortho. Qed.

Lemma ztriad_neq0 : ztriad != 0.
Proof. by rewrite -norm_eq0 ztriad_norm oner_neq0. Qed.

Lemma triad_is_ortho : triple_prod_mat xtriad ytriad ztriad \is 'O_3[R].
Proof.
apply/orthogonalP.
case=> -[i0|[i1|[i2|//]]]; case=> -[j0|[j1|[j2|//]]] /=; rewrite !rowK /SimplFunDelta /=.
- by rewrite dotmulvv xtriad_norm // expr1n.
  by rewrite xytriad_ortho.
  by rewrite dotmul_crossmulA crossmulvv dotmul0v.
- by rewrite dotmulC xytriad_ortho.
  by rewrite dotmulvv ytriad_norm // expr1n.
  by rewrite /ztriad dotmul_crossmulCA crossmulvv dotmulv0.
- by rewrite dotmulC dotmul_crossmulA crossmulvv dotmul0v.
  by rewrite -dotmul_crossmulA crossmulvv dotmulv0.
  by rewrite dotmulvv ztriad_norm // expr1n.
Qed.

Lemma triad_is_orthonormal : triple_prod_mat xtriad ytriad ztriad \is 'SO_3[R].
Proof.
rewrite rotationE triad_is_ortho /= -crossmul_triple dotmul_crossmulA -/ztriad.
by rewrite dotmul_cos ztriad_norm !mul1r vec_anglevv ?cos0 // -norm_eq0 ztriad_norm ?oner_neq0.
Qed.

End triad.

Section transformation_given_three_points.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Variables l1 l2 l3 r1 r2 r3 : coordinate.
Hypotheses (l12 : l1 != l2) (r12 : r1 != r2).
Hypotheses (l123 : ~~ colinear (l2 - l1) (l3 - l1)) 
           (r123 : ~~ colinear (r2 - r1) (r3 - r1)).

Definition rots : 'M_3 * 'M_3 :=
  let: (Xl, Yl, Zl) := triad l1 l2 l3 in
  let: (Xr, Yr, Zr) := triad r1 r2 r3 in
  (triple_prod_mat Xl Yl Zl,
   triple_prod_mat Xr Yr Zr).

Lemma rots1_is_SO : rots.1 \is 'SO_3[R]. Proof. exact: triad_is_orthonormal. Qed.
Lemma rots2_is_SO : rots.2 \is 'SO_3[R]. Proof. exact: triad_is_orthonormal. Qed.

Definition rot3 := rots.1^T *m rots.2.

Lemma rot3_is_SO : rot3 \is 'SO_3[R].
Proof. by rewrite rpredM // ?rots2_is_SO // rotationV rots1_is_SO. Qed.

Definition trans3 : vector := r1 - l1 *m rot3.

Lemma xtriad_l_r : xtriad l1 l2 *m rot3 = xtriad r1 r2.
Proof.
rewrite /rot3 /rots /= mulmxA triple_prod_mat_mulmx xytriad_ortho.
rewrite dotmul_crossmulA crossmulvv dotmul0v dotmulvv xtriad_norm //.
rewrite expr1n triple_prod_matE (mul_row_col 1%:M) mul1mx (mul_row_col 0%:M).
do 2 rewrite mul_scalar_mx scale0r; by do 2 rewrite addr0.
Qed.

Lemma ytriad_l_r : ytriad l1 l2 l3 *m rot3 = ytriad r1 r2 r3.
Proof.
rewrite /rot3 /rots /= mulmxA triple_prod_mat_mulmx dotmulC xytriad_ortho.
rewrite dotmulvv ytriad_norm // expr1n dotmul_crossmulCA crossmulvv dotmulv0.
rewrite triple_prod_matE.
rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
rewrite (mul_row_col 1%:M) mul_scalar_mx scale1r.
by rewrite mul_scalar_mx scale0r addr0.
Qed.

Lemma ztriad_l_r : ztriad l1 l2 l3 *m rot3 = ztriad r1 r2 r3.
Proof.
rewrite /rot3 /rots /= mulmxA triple_prod_mat_mulmx.
rewrite {1}/ztriad dotmulC dotmul_crossmulA crossmulvv dotmul0v.
rewrite {1}/ztriad -dotmul_crossmulA crossmulvv dotmulv0.
rewrite dotmulvv ztriad_norm // expr1n triple_prod_matE.
do 2 rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite mul_scalar_mx scale1r.
Qed.

End transformation_given_three_points.

Ltac simp := rewrite ?Monoid.simpm ?(mulNr,mulrN,opprK).

Section canonical_frame.

Variable R : rcfType.

Definition row3 (a b c : R) : 'rV[R]_3 := \row_p 
  [eta \0 with 0 |-> a, 1 |-> b, 2%:R |-> c] p.

Definition veci : 'rV[R]_3 := row3 1 0 0.
Definition vecj : 'rV[R]_3 := row3 0 1 0.
Definition veck : 'rV[R]_3 := row3 0 0 1.

Lemma icoor (p : 'rV[R]_3) : p 0 0 = p *d veci.
Proof. by rewrite /dotmul mxE sum3E !mxE /=; simp. Qed.

Lemma jcoor (p : 'rV[R]_3) : p 0 1 = p *d vecj.
Proof. by rewrite /dotmul mxE sum3E !mxE /=; simp. Qed.

Lemma kcoor (p : 'rV[R]_3) : p 0 2%:R = p *d veck.
Proof. by rewrite /dotmul mxE sum3E !mxE /=; simp. Qed.

Lemma normi : norm veci = 1.
Proof. by rewrite /norm dotmulE sum3E !mxE /=; simp; rewrite sqrtr1. Qed.

Lemma normj : norm vecj = 1.
Proof. by rewrite /norm dotmulE sum3E !mxE /=; simp; rewrite sqrtr1. Qed.

Lemma normk : norm veck = 1.
Proof. by rewrite /norm dotmulE sum3E !mxE /=; simp; rewrite sqrtr1. Qed.

Lemma vecij : veci *v vecj = veck.
Proof.
rewrite crossmulE; apply/rowP => i.
rewrite !mxE /=. simp => /=. by rewrite oppr0 addr0.
Qed.

Lemma vecik : veci *v veck = - vecj.
Proof.
rewrite crossmulE; apply/rowP => i.
rewrite !mxE /=. simp => /=. rewrite oppr0. 
case: ifP => [|_]; first by rewrite oppr0.
case: ifP => //.
case: ifP => //; by rewrite oppr0.
Qed.

Lemma vecjk : vecj *v veck = veci.
Proof.
rewrite crossmulE; apply/rowP => i.
rewrite /= !mxE /=. simp => /=. by rewrite subr0 oppr0.
Qed.

End canonical_frame.

(* row-vector * Ry => rotation around the y axis (x goes towards z) *)
Definition Ry R (a : angle R) := triple_prod_mat
  (\row_k [eta \0 with 0 |-> cos a, 1 |-> 0, 2%:R |-> sin a] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> 1, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> - sin a, 1 |-> 0, 2%:R |-> cos a] k).

Lemma xRy R (a : angle R) : @veci R *m Ry a = 
  \row_k [eta \0 with 0 |-> cos a, 1 |-> 0, 2%:R |-> sin a] k.
Proof. apply/matrixP => i j. rewrite !mxE /= sum3E !mxE /=. by simp. Qed.

Lemma yRy R (a : angle R) : @vecj R *m Ry a = @vecj R.
Proof. apply/matrixP => i j. rewrite !mxE /= sum3E !mxE /=. by simp. Qed.

Lemma zRy R (a : angle R) : @veck R *m Ry a =
  \row_k [eta \0 with 0 |-> - sin a, 1 |-> 0, 2%:R |-> cos a] k.
Proof. apply/matrixP => i j. rewrite !mxE /= sum3E !mxE /=. by simp. Qed.

Lemma Ry_is_O R a : Ry a \is 'O_3[R].
Proof.
rewrite orthogonalE.
suff : Ry a *m (Ry a)^T = 1 by move=> <-.
rewrite /Ry triple_prod_matE.
set row1 := \row_k _. set row2 := \row_k _. set row3 := \row_k _.
rewrite (tr_col_mx row1) (mul_col_row row1 _ row1^T).
  rewrite (mx11_scalar (row1 *m _)) -/(row1 *d row1) dotmulE sum3E.
  rewrite ![row1 _ _]mxE /= mulr0 addr0 -2!expr2 exprnP cos2Dsin2.
have -> : row1 *m (col_mx row2 row3)^T = 0.
  rewrite tr_col_mx mul_mx_row (mx11_scalar (_ *m _)) -/(row1 *d row2) dotmulE sum3E.
  rewrite (mx11_scalar (_ *m _)) -/(row1 *d row3) dotmulE sum3E.
  rewrite ![row1 0 _]mxE /= ![row2 0 _]mxE /= ![row3 0 _]mxE /= !(mulr0,add0r,mul0r,addr0).
  rewrite mulrN addrC mulrC subrr -row_mx0 (_ : 0%:M = 0) //.
  by apply/matrixP => i j; rewrite !mxE (ord1 i) (ord1 j) eqxx /= mulr1n.
have -> : col_mx row2 row3 *m row1^T = 0.
  rewrite mul_col_mx (mx11_scalar (_ *m _)) -/(row2 *d row1).
  rewrite (mx11_scalar (_ *m _)) -/(row3 *d row1) 2!dotmulE 2!sum3E.
  rewrite ![row1 0 _]mxE ![row2 0 _]mxE ![row3 0 _]mxE /= !(mul0r,mulr0,addr0) mulrC mulrN addrC subrr.
  rewrite -col_mx0 (_ : 0%:M = 0) //.
  by apply/matrixP => i j; rewrite !mxE (ord1 i) (ord1 j) eqxx /= mulr1n.
have -> : col_mx row2 row3 *m (col_mx row2 row3)^T = 1.
  rewrite tr_col_mx mul_col_row.
  rewrite (mx11_scalar (_ *m _)) -/(row2 *d row2) dotmulE sum3E.
  rewrite (mx11_scalar (_ *m _)) -/(row2 *d row3) dotmulE sum3E.
  rewrite (mx11_scalar (_ *m _)) -/(row3 *d row2) dotmulE sum3E.
  rewrite (mx11_scalar (_ *m _)) -/(row3 *d row3) dotmulE sum3E.
  rewrite ![row2 0 _]mxE ![row3 0 _]mxE /= !(mulr0,add0r,mul0r,addr0,mulr1).
  rewrite mulNr mulrN opprK addrC -2!expr2 exprnP cos2Dsin2 (_ : 0%:M = 0); last first.
    by apply/matrixP => i j; rewrite !mxE (ord1 i) (ord1 j) eqxx /= mulr1n.
  by rewrite -scalar_mx_block idmxE.
by rewrite -scalar_mx_block idmxE.
Qed.

Lemma triple_prod_mat_rowE {R : rcfType} (M : 'M[R]_3) :
  M = triple_prod_mat (row 0 M) (row 1 M) (row 2%:R M).
Proof.
rewrite /triple_prod_mat.
apply/matrixP => i j.
rewrite mxE /=.
case/boolP : (i == 0) => [/eqP -> |]; first by rewrite mxE.
rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE.
Qed.

Lemma det1row {R : rcfType} (M : 'M[R]_3) : 
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 ->
  row 0 M *d row 1 M = 0 ->
  row 2%:R M = row 0 M *v row 1 M -> \det M == 1.
Proof.
move=> M01 M11 H1 H2.
rewrite (triple_prod_mat_rowE M) det_triple_prod_mat H2 dotmul_crossmulA.
rewrite crossmulC double_crossmul H1 scale0r add0r opprK dotmulvv.
by rewrite M01 expr1n scale1r dotmulvv M11 expr1n.
Qed.

Lemma orthorow {R : rcfType} (M : 'M[R]_3) : 
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 ->
  row 0 M *d row 1 M = 0 ->
  row 2%:R M = row 0 M *v row 1 M -> M \is 'O_3[R].
Proof.
move=> normx1 normy1 xy0 zxy0 /=.
apply/orthogonalP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulvv normx1 expr1n.
  rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite xy0.
  by rewrite zxy0 dotmul_crossmulA crossmulvv dotmul0v.
rewrite ifnot0 => /orP [] /eqP -> /=.
case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulC.
rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite dotmulvv normy1 expr1n.
by rewrite zxy0 dotmul_crossmulCA crossmulvv dotmulv0.
case/boolP : (j == 0) => [/eqP -> /=|].
  by rewrite zxy0 dotmulC dotmul_crossmulA crossmulvv dotmul0v.
rewrite ifnot0 => /orP [] /eqP -> /=.
  by rewrite zxy0 dotmulC dotmul_crossmulCA crossmulvv dotmulv0.
rewrite dotmulvv zxy0 norm_crossmul normx1 normy1 2!mul1r.
by rewrite dotmul0_vec_angle // ?expr1n // -norm_eq0 ?normx1 ?normy1 oner_neq0.
Qed.

Lemma orthorow2 {R : rcfType} (M : 'M[R]_3) : 
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 -> norm (row 2%:R M) = 1 ->
  row 0 M *d row 1 M = 0 ->
  row 0 M *d row 2%:R M = 0 ->
  row 1 M *d row 2%:R M = 0 ->
  M \is 'O_3[R].
Proof.
move=> normx1 normy1 normz1 xy0 xz0 yz0 /=.
apply/orthogonalP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulvv normx1 expr1n.
  rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite xy0.
  by rewrite xz0.
rewrite ifnot0 => /orP [] /eqP -> /=.
case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulC.
rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite dotmulvv normy1 expr1n.
by rewrite yz0.
case/boolP : (j == 0) => [/eqP -> /=|].
  by rewrite dotmulC xz0.
rewrite ifnot0 => /orP [] /eqP -> /=.
  by rewrite dotmulC yz0.
by rewrite dotmulvv normz1 expr1n.
Qed.

Module Frame.
Section frame.
Variable R : rcfType.
Record t := mk {
  orig : 'rV[R]_3 ;
  M :> 'M[R]_3 ;
  x := row 0 M ;
  y := row 1 M ;
  z := row 2%:R M ;
  normx : norm x = 1 ;
  normy : norm y = 1 ;
  xy : x *d y = 0 ;
  zxy : z = x *v y  
}.
End frame.
Lemma frame_ortho R (f : t R) : M f \in 'O_3[R]. 
Proof.
case: f => orig M x0 y0 z0 normx1 normy1 xy0 zxy0 /=.
by rewrite orthorow.
Qed.
Lemma frame_rot R (f : t R) : M f \in 'SO_3[R]. 
Proof.
rewrite rotationE frame_ortho /=.
case: f => orig M x y z x1 y1 xy xyz /=.
by rewrite det1row.
Qed.

End Frame.
Coercion FrameM {R} := @Frame.M R.

Definition canonical_M {R} := triple_prod_mat (@veci R) (@vecj R) (@veck R).
Lemma norm_canonical_x {R} : norm (row 0 (@canonical_M R)) = 1.
Proof. apply/eqP; rewrite -sqrp_eq1 ?norm_ge0 // -dotmulvv dotmulE sum3E !mxE /=. by simp. Qed.
Lemma norm_canonical_y {R} : norm (row 1 (@canonical_M R)) = 1.
Proof. apply/eqP; rewrite -sqrp_eq1 ?norm_ge0 // -dotmulvv dotmulE sum3E !mxE /=. by simp. Qed.
Lemma canonical_xy {R} : row 0 (@canonical_M R) *d row 1 canonical_M = 0.
Proof. rewrite dotmulE sum3E !mxE /=; by simp. Qed.
Lemma canonical_zxy {R} : row 2%:R (@canonical_M R) = row 0 (@canonical_M R) *v row 1 canonical_M.
Proof.
rewrite crossmulE; apply/rowP => i; rewrite !mxE /=. simp. rewrite oppr0. simp. reflexivity.
Qed.

Definition canonical_frame R : Frame.t R := Frame.mk
  (\row_i 0) (@norm_canonical_x R) norm_canonical_y canonical_xy canonical_zxy.

Inductive vec {R} (f : @Frame.t R) : Type := Vec of 'rV[R]_3.

Definition vec_of {R} (f : @Frame.t R) (x : vec f) := let: Vec v := x in v.

Definition absolute_vec {R} (f : @Frame.t R) (x : 'rV[R]_3) : 'rV[R]_3 :=
  x *m f.

Lemma absolute_vec_can {R} (x : vec (canonical_frame R)) :
  absolute_vec (canonical_frame R) (vec_of x) = vec_of x.
Proof.
rewrite /absolute_vec.
apply/rowP => i.
case/boolP : (i == 0) => [/eqP -> |].
  by rewrite mxE sum3E !mxE /=; simp.
rewrite ifnot0 => /orP [] /eqP ->; by rewrite mxE sum3E !mxE /=; simp.
Qed.

Module MapRot.
Section maprot_sect.
Variable R : rcfType.
Variables A B : Frame.t R.
Record t := {
  M :> 'M[R]_3 ; (* rotation of frame B w.r.t. frame A *)
  HM : forall i j, M i j = row j A *d row i B (* def 1.1 du handbook *)
}.
End maprot_sect.
End MapRot.
Coercion RotM {R} (A B : Frame.t R) := @MapRot.M _ A B.

Lemma delta_mx_mul {R: rcfType} (M : 'M[R]_3) (i j : _) : 
  (delta_mx 0 j *m M) (0 : 'I_1) i = M j i.
Proof.
rewrite !mxE sum3E !mxE /=.
case/boolP : (j == 0) => [/eqP -> /=|]; first by simp.
rewrite ifnot0 => /orP [] /eqP -> /=; by simp.
Qed.

Lemma MapRotP {R : rcfType} (A B : Frame.t R) (M : MapRot.t A B) (x : vec A) : 
  absolute_vec A (vec_of x *m M) = absolute_vec B (vec_of x).
Proof.
case: x => x /=.
rewrite /absolute_vec -mulmxA; congr (_ *m _).
have -> : M = B *m A^T :> 'M[R]_3.
  apply/matrixP => i j.
  case: M => /= M ->.
  rewrite 2!rowE dotmul_trmx dotmul_delta_mx -mulmxA.
  by rewrite (delta_mx_mul (A *m B^T)) -{1}(trmxK A) -trmx_mul mxE.
rewrite -mulmxA.
move: (Frame.frame_ortho A).
rewrite orthogonalEC => /eqP.
rewrite mulmxE => ->; by rewrite mulr1.
Qed.

Definition Rx R (a : angle R) := triple_prod_mat
  (\row_k [eta \0 with 0 |-> 1, 1 |-> 0, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> cos a, 2%:R |-> - sin a] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> sin a, 2%:R |-> cos a] k).

Definition Rz R (a : angle R) := triple_prod_mat
  (\row_k [eta \0 with 0 |-> cos a, 1 |-> - sin a, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> sin a, 1 |-> cos a, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> 0, 2%:R |-> 1] k).

Section frame_triad.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Variables l1 l2 l3 : coordinate.
Hypotheses (l12 : l1 != l2).
Hypotheses (l123 : ~~ colinear (l2 - l1) (l3 - l1)).

Definition M_triad := triple_prod_mat (xtriad l1 l2) (ytriad l1 l2 l3) (ztriad l1 l2 l3).

Lemma normx1_triad : norm (row 0 M_triad) = 1.
Proof. by rewrite /M_triad rowK /= xtriad_norm. Qed.

Lemma normy1_triad : norm (row 1 M_triad) = 1.
Proof. by rewrite /M_triad rowK /= ytriad_norm. Qed.

Lemma xy_triad : row 0 M_triad *d row 1 M_triad = 0.
Proof. by rewrite !rowK /= xytriad_ortho. Qed.

Lemma xyz_triad : row 2%:R M_triad = row 0 M_triad *v row 1 M_triad.
Proof. by rewrite !rowK /=. Qed.

Definition frame_triad : Frame.t R := Frame.mk l1 normx1_triad normy1_triad xy_triad xyz_triad.

(* therefore, x * frame_triad^T turns a vector x in the canonical frame into the frame_triad *)

End frame_triad.

(*Module Frame.
Section frame_section.
Variable R : rcfType.
Local Notation coordinate := 'rV[R]_3.
Local Notation basisType := 'M[R]_3.
Definition x_ax : basisType -> 'rV[R]_3 := row 0.
Definition y_ax : basisType -> 'rV[R]_3 := row 1%R.
Definition z_ax : basisType -> 'rV[R]_3 := row 2%:R.

Record t := mkT {
  origin : coordinate ;
  basis :> basisType ;
  _ : unitmx basis }.

Lemma unit (f : t) : basis f \in GRing.unit. Proof. by case: f. Qed.
End frame_section.
End Frame.

Coercion Framebasis R (f : Frame.t R) : 'M[R]_3 := Frame.basis f.
*)
(*Hint Immediate Frame.unit.*)

(*Section about_frame.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := Frame.t R.

(* coordinate in frame f *)
Inductive coor (f : frame) : Type := Coor of 'rV[R]_3.

Definition absolute_coor (f : frame) (x : coor f) : 'rV[R]_3 :=
  match x with Coor v => Frame.origin f + v *m Frame.basis f end.

Definition relative_coor f (x : coordinate) : coor f :=
  Coor _ ((x - Frame.origin f) *m (Frame.basis f)^-1).

Lemma absolute_coorK f (x : coor f) : relative_coor f (absolute_coor x) = x.
Proof.
case: x => /= v.
by rewrite /relative_coor addrC addKr -mulmxA mulmxV // ?mulmx1 // Frame.unit.
Qed.

Lemma relative_coorK f (x : coordinate) : absolute_coor (relative_coor f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // ?Frame.unit // mulmx1 addrC addrNK. Qed.

(* vector in frame f *)
Inductive vec (f : frame) : Type := Vec of 'rV[R]_3.

Definition absolute_vec f (x : vec f) : 'rV[R]_3 :=
  match x with Vec v => v *m Frame.basis f end.

Definition relative_vec f (x : vector) : vec f :=
  Vec _ (x *m (Frame.basis f)^-1).

Lemma absolute_vecK f (x : vec f) : relative_vec f (absolute_vec x) = x.
Proof. case: x => /= v. by rewrite /relative_vec -mulmxA mulmxV // ?Frame.unit // mulmx1. Qed.

Lemma relative_vecK f (x : vector) : absolute_vec (relative_vec f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // ?Frame.unit // mulmx1. Qed.

End about_frame.*)

Section homogeneous_transformation.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Record transform : Type := Transform {
  translation : vector;
  rot : 'M[R]_3 ;
  _ : rot \in 'SO_3[R] }.

(* homogeneous transformation *)
Coercion hmx (T : transform) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx (translation T)^T 1).

Definition hrot_of_transform (T : transform) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx 0 1).

Definition htrans_of_transform (T : transform) : 'M[R]_4 :=
  row_mx (col_mx 1 0) (col_mx (translation T)^T 1).

Lemma hmxE (T : transform) : T = htrans_of_transform T *m hrot_of_transform T :> 'M_4.
Proof.
rewrite /hmx /htrans_of_transform /hrot_of_transform.
rewrite (mul_mx_row (row_mx (col_mx 1 0) (col_mx (translation T)^T 1)) (col_mx (rot T) 0)).
rewrite mul_row_col mulmx0 addr0 mul_row_col mulmx0 add0r mulmx1.
by rewrite mul_col_mx mul1mx mul0mx.
Qed.

Definition inv_htrans (T : transform) := row_mx (col_mx 1 0) (col_mx (- (translation T)^T) 1).

Lemma inv_htransP T : htrans_of_transform T *m inv_htrans T = 1.
Proof.
rewrite /htrans_of_transform /inv_htrans mul_mx_row.
rewrite (mul_row_col (col_mx 1 0) (col_mx (translation T)^T 1)) mulmx0 addr0 mulmx1.
rewrite (mul_row_col (col_mx 1 0) (col_mx (translation T)^T 1)) mulmx1.
rewrite mul_col_mx mul1mx mul0mx add_col_mx addrC subrr add0r.
rewrite -(block_mxEh (1 :'M_3) 0 0 1).
rewrite -[in RHS](@submxK _ 3 1 3 1 (1 : 'M_4)).
congr (@block_mx _ 3 1 3 1); apply/matrixP => i j.
by rewrite !mxE -!val_eqE.
rewrite !mxE -val_eqE /= (ord1 j) addn0.
move: (ltn_ord i); by rewrite ltn_neqAle => /andP [] /negbTE ->.
rewrite !mxE -val_eqE /= (ord1 i) addn0.
by move: (ltn_ord j); rewrite ltn_neqAle eq_sym => /andP [] /negbTE ->.
by rewrite !mxE -!val_eqE.
Qed.

Definition homogeneous := 'rV[R]_4.

(*Definition hvect (x : vector) : homogeneous := row_mx x 0. *)
Inductive hvect := HVec of vector.
Coercion homogeneous_of_hvect (hv : hvect) : 'rV[R]_4 :=
  let: HVec x := hv in row_mx x 0.

(*Definition hcoor (x : coordinate) : homogeneous := row_mx x 1.*)
Inductive hcoor := HCor of coordinate.
Coercion homogeneous_of_hcoor (hc : hcoor) : 'rV[R]_4 :=
  let: HCor x := hc in row_mx x 1.

Definition coord_of_h (x : homogeneous) : coordinate := 
  lsubmx (castmx (erefl, esym (addn1 3)) x).

Lemma coord_of_hB a b : coord_of_h (a - b) = coord_of_h a - coord_of_h b.
Proof. apply/rowP => i; by rewrite !mxE !castmxE /= esymK !cast_ord_id !mxE. Qed.

Lemma coord_of_hE (x : homogeneous) : coord_of_h x = \row_(i < 3) x 0 (inord i).
Proof.
apply/rowP => i; rewrite !mxE castmxE /= esymK !cast_ord_id; congr (x 0 _).
apply val_inj => /=; by rewrite inordK // (ltn_trans (ltn_ord i)).
Qed.

Definition htrans_of_vector (x : vector) (T : transform) : homogeneous :=
  (T *m (HVec x)^T)^T.

Lemma htrans_of_vectorE a T : htrans_of_vector a T = a *m row_mx (rot T)^T 0.
Proof.
rewrite /htrans_of_vector /hmx /hvect.
rewrite (tr_row_mx a) (mul_row_col (col_mx (rot T) 0)) linearD /= trmx_mul.
by rewrite (tr_col_mx (rot T)) trmx_mul !trmx0 !trmxK mul0mx addr0.
Qed.

Lemma linear_htrans_of_vector T : linear (htrans_of_vector^~ T).
Proof. move=> ? ? ?; by rewrite 3!htrans_of_vectorE mulmxDl -scalemxAl. Qed.

Definition htrans_of_coordinate (x : coordinate) (T : transform) : homogeneous :=
  (T *m (HCor x)^T)^T.

Lemma htrans_of_coordinateB a b T :
  htrans_of_coordinate a T - htrans_of_coordinate b T = htrans_of_vector (a - b) T.
Proof.
rewrite {1}/htrans_of_coordinate {1}/hmx.
rewrite (tr_row_mx a) trmx1 (mul_row_col (col_mx (rot T) 0)) linearD /=.
rewrite mulmx1 trmx_mul trmxK (tr_col_mx (rot T)) trmx0.
rewrite (tr_col_mx (translation T)^T) trmxK trmx1.
rewrite {1}/htrans_of_coordinate {1}/hmx.
rewrite trmx_mul trmxK.
rewrite (tr_row_mx (col_mx (rot T) 0)) (tr_col_mx (translation T)^T) trmxK trmx1.
rewrite (tr_col_mx (rot T)) trmx0 (mul_row_col b) mul1mx.
rewrite addrAC opprD -!addrA [in X in _ + (_ + X) = _]addrC subrr addr0.
rewrite /htrans_of_vector /hmx /hvect.
rewrite (tr_row_mx (a - b)) trmx0 trmx_mul.
rewrite (tr_col_mx (a - b)^T) trmx0.
rewrite (tr_row_mx (col_mx (rot T) 0)) trmxK.
rewrite (mul_row_col (a - b)) mul0mx addr0.
rewrite (tr_col_mx (rot T)) trmx0.
by rewrite mulmxBl.
Qed.

Definition homogeneous_ap (x : coordinate) (T : transform) : coordinate :=
  (*\row_(i < 3) (homogeneous_mx T *m col_mx  x^T 1 (* 0 for vectors? *) )^T 0 (inord i).*)
  coord_of_h (htrans_of_coordinate x T).

Lemma homogeneous_apE x T : homogeneous_ap x T = 
  lsubmx (castmx (erefl, esym (addn1 3)) (htrans_of_coordinate x T)).
Proof.
rewrite /homogeneous_ap.
apply/rowP => i; rewrite !mxE.
by rewrite castmxE /= esymK cast_ord_id /htrans_of_coordinate !mxE.
Qed.

Lemma htrans_of_vector_preserves_norm a T :
  norm (coord_of_h (htrans_of_vector a T)) = norm a.
Proof.
rewrite htrans_of_vectorE /coord_of_h mul_mx_row mulmx0.
rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
rewrite (cast_row_mx _ (a *m (rot T)^T)) row_mxKl castmx_id.
rewrite orth_preserves_norm // orthogonalV rotation_sub //; by case: T.
Qed.

Lemma coord_of_ht_htrans_of_vectorE u T :
  coord_of_h (htrans_of_vector u T) = u *m (rot T)^T.
Proof.
rewrite htrans_of_vectorE; apply/rowP => i.
rewrite mxE castmxE /= esymK cast_ord_id mul_mx_row mulmx0.
rewrite (_ : cast_ord (addn1 3) _ = lshift 1 i); last by apply val_inj.
by rewrite (row_mxEl (u *m (rot T)^T)).
Qed.

Lemma hcoor_inv_htrans a t r (Hr : r \is 'SO_3[R]) :
  (HCor a) *m (inv_htrans (Transform t Hr))^T = HCor (a - t) :> homogeneous.
Proof.
rewrite /inv_htrans /= tr_row_mx 2!tr_col_mx !trmx1 trmx0.
rewrite (mul_row_col a) mul1mx mul_mx_row mulmx1 mulmx0 add_row_mx add0r.
by rewrite linearN /= trmxK.
Qed.

Lemma hcoor_hrot_of_transform a t r (Hr : r \is 'SO_3[R]) :
  (HCor a) *m (hrot_of_transform (Transform t Hr))^T = HCor (a *m r^T) :> homogeneous.
Proof.
rewrite /hrot_of_transform /= (tr_row_mx (col_mx r 0)) !tr_col_mx !trmx0 trmx1.
rewrite (mul_row_col a) mul1mx (mul_mx_row a r^T) mulmx0 (add_row_mx (a *m r^T)).
by rewrite addr0 add0r.
Qed.

End homogeneous_transformation.

Section isometry_def.

Variable (R : rcfType) (n : nat).
Let coordinate := 'rV[R]_n.

Definition preserves_diff (f : coordinate -> coordinate) :=
  forall i j, norm (i - j) = norm (f i - f j).

Record isometry := mkIsometry {
  iso :> coordinate -> coordinate ;
  is_iso : preserves_diff iso}.

End isometry_def.

Local Notation "''SE_' n [ R ]" := (isometry R n)
  (at level 8, n at level 2, format "''SE_' n [ R ]").

Section orthogonal_frame.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

CoInductive oframe (u1 u2 u3 : vector) := OFrame of
  norm u1 = 1 & norm u2 = 1 & norm u3 = 1 &
  u1 *d u2 = 0 & u2 *d u3 = 0 & u1 *d u3 = 0.

Lemma orthogonal_expansion_helper u1 u2 u3 : oframe u1 u2 u3 ->
  forall p, p *d u1 = 0 -> p *d u2 = 0 -> p *d u3 = 0 -> p = 0.
Proof.
case=> x1 y1 z1 xy xz yz p.
do 3 rewrite dotmulE sum3E.
move=> H1 H2 H3.
have abs : p *m (triple_prod_mat u1 u2 u3) ^T = 0.
  rewrite triple_prod_mat_mulmx dotmulE sum3E H1 dotmulE sum3E H2 dotmulE sum3E H3.
  rewrite (_ : 0%:M = 0); last by apply/matrixP => ? ?; rewrite !mxE mul0rn.
  by rewrite 2!row_mx0.
have H0 : triple_prod_mat u1 u2 u3 \is 'O_3[R].
  apply/orthogonalP => i j.
  rewrite !rowK /=.
  case: ifPn => [/eqP -> |].
    case: ifPn => [/eqP -> |]; first by rewrite dotmulvv x1 expr1n eqxx.
    by rewrite ifnot0 => /orP [] /eqP ->.
  rewrite ifnot0 => /orP [] /eqP -> /=.
    case: ifPn => [/eqP -> |]; first by rewrite dotmulC xy.
    rewrite ifnot0 => /orP [] /eqP -> //=; by rewrite dotmulvv y1 expr1n.
  case: ifPn => [/eqP ->|]; first by rewrite dotmulC yz.
  rewrite ifnot0 => /orP [] /eqP -> //=; first by rewrite dotmulC.
  by rewrite dotmulvv z1 expr1n.
move/eqP: abs.
rewrite mul_mx_rowfree_eq0; first by move/eqP.
apply/row_freeP; exists (triple_prod_mat u1 u2 u3).
apply/eqP; by rewrite -orthogonalEC.
Qed.

Lemma orthogonal_expansion (p : coordinate) u1 u2 u3 : oframe u1 u2 u3 -> 
   p = (p *d u1) *: u1 + (p *d u2) *: u2 + (p *d u3) *: u3.
Proof.
case=> x1 y1 z1 xy xz yz.
set y : vector := (p *d u1) *: u1 + (p *d u2) *: u2 + (p *d u3) *: u3.
suff /eqP : p - y = 0; first by rewrite subr_eq0 => /eqP.
apply (@orthogonal_expansion_helper u1 u2 u3).
- by apply OFrame.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv dotmulvv x1 expr1n mulr1.
  rewrite 2!opprD 2!addrA subrr add0r dotmulZv (dotmulC u2) xy mulr0 oppr0.
  by rewrite dotmulZv (dotmulC u3) yz mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv xy mulr0 add0r.
  rewrite dotmulZv dotmulvv y1 expr1n mulr1 opprD addrA subrr.
  by rewrite dotmulZv (dotmulC u3) xz mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv yz mulr0 add0r dotmulZv.
  by rewrite xz mulr0 add0r dotmulZv dotmulvv z1 expr1n mulr1 subrr.
Qed.

Lemma frame_canonical : oframe (@veci R) (@vecj _) (@veck _).
Proof.
split.
by rewrite normi.
by rewrite normj.
by rewrite normk.
by rewrite -jcoor mxE.
by rewrite -kcoor mxE.
by rewrite -kcoor mxE.
Qed.

Lemma oriented_frame_of_oframe u1 u2 u3 (f : oframe u1 u2 u3) :
  `| u1 *d (u2 *v u3) | = 1.
Proof.
case: f => x1 y1 z1 xy yz xz; rewrite crossmul_triple.
apply/orthogonal_det/orthorow2; by rewrite !rowK.
Qed.

Lemma dotmul1_inv (u v : vector) : norm u = 1 -> norm v = 1 -> u *d v = 1 -> u = v.
Proof.
move=> u1 v1.
rewrite dotmul_cos u1 v1 2!mul1r.
move/cos1_angle0.
by apply vec_angle0_inv.
Qed.

Lemma dotmulN1_inv (u v : vector) : norm u = 1 -> norm v = 1 -> u *d v = - 1 -> u = - v.
Proof.
move=> u1 v1.
rewrite dotmul_cos u1 v1 2!mul1r.
move/cosN1_angle0.
by apply vec_anglepi_inv.
Qed.

Lemma oframe_crossmul e1 e2 e3 (f : oframe e1 e2 e3) : e3 = e1 *v e2 \/ e3 = - e1 *v e2.
Proof.
move: (oriented_frame_of_oframe f).
case: (lerP 0 (e1 *d (e2 *v e3))) => H.
  rewrite ger0_norm // => {H}.
  rewrite dotmul_crossmulA.
  move/dotmul1_inv => H; left; rewrite H //.
  case: f => He1 He2 ? e1e2 *.
  rewrite norm_crossmul He1 He2 2!mul1r cos0sin1 //.
  do 2 rewrite -[LHS](mul1r).
  rewrite -{1}He1 -He2 mulrA.
  by rewrite -dotmul_cos.
  by case: f.
rewrite ltr0_norm // => {H} /eqP.
rewrite eqr_oppLR => /eqP.
rewrite dotmul_crossmulA.
move/dotmulN1_inv => H; right. rewrite crossmulNv H // ?opprK //.
case: f => He1 He2 ? e1e2 *.
rewrite norm_crossmul He1 He2 2!mul1r cos0sin1 //.
do 2 rewrite -[LHS](mul1r).
rewrite -{1}He1 -He2 mulrA.
by rewrite -dotmul_cos.
by case: f.
Qed.

Lemma oframe_positive e1 e2 e3 (f : oframe e1 e2 e3) : e3 = e1 *v e2 ->
  e2 = e3 *v e1 /\ e1 = e2 *v e3.
Proof.
move=> H; split.
  rewrite H crossmulC double_crossmul.
  case: f => x1 ? ? K *.
  by rewrite K scale0r add0r opprK dotmulvv x1 expr1n scale1r.
rewrite H double_crossmul.
case: f => ? y1 ? K *.
by rewrite dotmulvv y1 expr1n scale1r dotmulC K scale0r subr0.
Qed.

Lemma oframe_negative e1 e2 e3 (f : oframe e1 e2 e3) : e3 = - e1 *v e2 ->
  e2 = e1 *v e3 /\ e1 = e3 *v e2.
Proof.
move=> H; split.
  rewrite H crossmulNv crossmulvN double_crossmul.
  case: f => x1 ? ? K *.
  by rewrite dotmulvv x1 expr1n scale1r K scale0r add0r opprK.
rewrite H crossmulNv crossmulC crossmulvN opprK double_crossmul.
case: f => ? y1 ? K *.
by rewrite dotmulvv y1 expr1n scale1r dotmulC K scale0r subr0.
Qed.

Lemma lem35 (e1 e2 e3 : vector)  (f : oframe e1 e2 e3) v v1 v2 v3 w w1 w2 w3 :
  v = v1 *: e1 + v2 *: e2 + v3 *: e3 ->
  w = w1 *: e1 + w2 *: e2 + w3 *: e3 ->
  let eps := e1 *d (e2 *v e3) in 
  v *v w = eps *: ((v2 * w3 - v3 * w2) *: e1 -
                   (v1 * w3 - v3 * w1) *: e2 +
                   (v1 * w2 - v2 * w1) *: e3).
Proof.
move=> Hv Hw eps.
rewrite Hv Hw.
rewrite !linearD /=.
rewrite !linearZ /=.
rewrite (crossmulC _ e1).
rewrite (crossmulC _ e2).
rewrite (crossmulC _ e3).
rewrite !linearD /=.
rewrite (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 add0r.
move: (f).
case/oframe_crossmul => e3e1e2.
  case: (oframe_positive f e3e1e2) => H1 H2.
  rewrite (_ : _ *v _ = v2 *: e3); last by rewrite linearZ /= -e3e1e2.
  rewrite scalerN (_ : _ *v _ = - v3 *: e2); last first.
    by rewrite linearZ /= crossmulC -H1 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = - v1 *: e3); last first.
    by rewrite linearZ /= crossmulC e3e1e2 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  rewrite (_ : _ *v _ = v3 *: e1); last by rewrite linearZ /= -H2.
  rewrite scalerN (_ : _ *v _ = v1 *: e2); last by rewrite linearZ /= H1.
  rewrite scalerN (_ : _ *v _ = - v2 *: e1); last first.
    by rewrite linearZ /= crossmulC -H2 scaleNr scalerN.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0 (_ : eps = 1); last first.
    rewrite /eps -H2 dotmulvv; case: f => -> *; by rewrite expr1n.
  rewrite !scale1r -![in LHS]addrA addrC.
  rewrite -![in LHS]addrA.
  rewrite addrCA. 
  rewrite addrC.
  rewrite ![in LHS]addrA.
  rewrite -addrA; congr (_ + _); last first.
    by rewrite !scalerA -scaleNr -scalerDl /= addrC mulrC (mulrC w1).
  rewrite -addrA addrACA addrC; congr (_ + _).
    by rewrite -scaleNr !scalerA -scalerDl addrC mulrC mulNr (mulrC w2).
  by rewrite !scalerA -scalerBl scalerN -scaleNr opprB mulrC (mulrC w3).
case: (oframe_negative f e3e1e2) => H1 H2.
rewrite (_ : _ *v _ = - v2 *: e3); last first.
  by rewrite linearZ /= e3e1e2 crossmulNv scalerN scaleNr opprK.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = v3 *: e2); last first.
  by rewrite linearZ /= -H1.
rewrite scalerN.
rewrite (_ : _ *v _ = v1 *: e3); last first.
  by rewrite linearZ /= crossmulC -crossmulNv -e3e1e2.
rewrite scalerN.
rewrite (_ : _ *v _ = 0); last first.
  by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 addr0.
rewrite (_ : _ *v _ = - v3 *: e1); last first.
  by rewrite linearZ /= crossmulC -H2 scalerN scaleNr.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = - v1 *: e2); last first.
  by rewrite linearZ /= crossmulC -H1 scalerN scaleNr.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = v2 *: e1); last first.
  by rewrite linearZ /= -H2.
rewrite scalerN.
rewrite (_ : _ *v _ = 0); last first.
  by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 addr0.
rewrite (_ : eps = - 1); last first.
   rewrite /eps crossmulC -H2 dotmulvN dotmulvv.
   case: f => -> *.
   by rewrite expr1n.
rewrite -![in LHS]addrA addrC -addrA.
rewrite addrCA -addrA addrC ![in LHS]addrA -addrA; congr (_ + _); last first.
  by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w2).
rewrite -addrA addrACA; congr (_ + _).
  by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w3).
by rewrite !scalerA -scalerBl scalerN mulrN1 scaleNr opprK mulrC (mulrC w1).
Qed.

End orthogonal_frame.

Section tangent_vectors_and_frames.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Record tvec (p : coordinate) := TVec {tvec_field :> vector}.
Definition vtvec p (v : tvec p) := let: TVec v := v in v.

CoInductive tframe (p : coordinate) (u1 u2 u3 : vector) := 
  TFrame : oframe u1 u2 u3 -> tframe p u1 u2 u3.
Definition oframe_of_tframe p u1 u2 u3 (f : tframe p u1 u2 u3) := let: TFrame f := f in f.

Definition tframe_i p u1 u2 u3 (f : tframe p u1 u2 u3) : tvec p :=
  TVec p u1.
Definition tframe_j p u1 u2 u3 (f : tframe p u1 u2 u3) : tvec p :=
  TVec p u2.
Definition tframe_k p u1 u2 u3 (f : tframe p u1 u2 u3) : tvec p :=
  TVec p u3.

Lemma frame_trans u1 u2 u3 p (f : tframe p u1 u2 u3) t :
  tframe (p + t) u1 u2 u3.
Proof. by case: f => -[] x1 y1 z1 xy yz xz. Qed.

End tangent_vectors_and_frames.

Coercion vtvec_field_coercion := vtvec.

Section central_isometry.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Lemma central_isometry_preserves_norm (f : 'SE_3[R]) : 
  f 0 = 0 -> preserves_norm f.
Proof. move=> f0 p; by rewrite -(subr0 (f p)) -f0 -(is_iso f) subr0. Qed.

Lemma central_isometry_preserves_dot_products (f : 'SE_3[R]) : 
  f 0 = 0 -> preserves_dot_products f.
Proof.
move=> f0 a b.
have : norm (f a - f b) = norm (a - b) by rewrite -(is_iso f).
rewrite /norm => /eqP.
rewrite eqr_sqrt ?le0dotmul // !dotmulDl !dotmulDr !dotmulvv !normN.
rewrite !(central_isometry_preserves_norm f0) !addrA 2!(addrC _ (norm b ^+ 2)).
move/eqP/addrI.
rewrite -2!addrA => /addrI.
rewrite -(dotmulC (f a)) dotmulvN -(dotmulC a) dotmulvN -2!mulr2n.
move/eqP.
rewrite -mulr_natr -[in X in _ == X -> _]mulr_natr 2!mulNr eqr_opp.
by move/eqP/mulIr => -> //; rewrite unitfE pnatr_eq0.
Qed.

Lemma frame_central_iso (f : 'SE_3[R]) u1 u2 u3 : f 0 = 0 ->
  oframe u1 u2 u3 ->
  oframe (f u1) (f u2) (f u3).
Proof.
move=> f0; case => x1 y1 z1 xy yz xz.
apply OFrame.
by rewrite /= (central_isometry_preserves_norm).
by rewrite /= (central_isometry_preserves_norm).
by rewrite /= (central_isometry_preserves_norm).
by rewrite /= (central_isometry_preserves_dot_products f0).
by rewrite /= (central_isometry_preserves_dot_products f0).
by rewrite /= (central_isometry_preserves_dot_products f0).
Qed.

Lemma central_isometry_is_linear (f : 'SE_3[R]) : f 0 = 0 -> linear f.
Proof.
move=> f0 k /= a b.
have Hp : forall p, 
  f p = p 0 0 *: f (@veci _) + p 0 1 *: f (@vecj _) + p 0 2%:R *: f (@veck _).
  move=> p.
  have -> : f p = f p *d f (@veci _) *: f (@veci _) 
             + f p *d f (@vecj _) *: f (@vecj _)
             + f p *d f (@veck _) *: f (@veck _).
    rewrite -orthogonal_expansion //.
    by apply frame_central_iso => //; apply frame_canonical.
  by rewrite 3!(central_isometry_preserves_dot_products f0) // -icoor -jcoor -kcoor.
rewrite Hp (Hp a) (Hp b) !mxE /= !(scalerDl, scalerDr).
rewrite !scalerA -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrC -!addrA.
Qed.

Definition matrix_of_iso (f : 'SE_3[R]) : linear f ->
  {M : {linear 'rV[R]_3 -> 'rV[R]_3} & forall x, f x = M x}.
Proof.
move=> H.
have @g : {linear 'rV[R]_3 -> 'rV[R]_3}.
  exists f.
  apply: (@GRing.Linear.class_of_axiom _ _ _ (fun k x => k *: x)).
    by apply GRing.Scale.scale_law.
  move=> k u v; by move: (H k u v).
by exists g.
Defined.

Lemma trans_ortho_of_iso (f : 'SE_3[R]) :
  { trans : 'rV[R]_3 & { rot : 'M[R]_3 | (forall x : 'rV[R]_3, f x == x *m rot + trans) /\
    rot \is 'O_3[R] /\
    trans = f 0 } }.
Proof.
set T := f 0.
set Tm1f := fun x => f x - T. 
have Tm1f_is_iso : preserves_diff Tm1f.
  rewrite /preserves_diff => i j.
  by rewrite /Tm1f -addrA opprB 2!addrA subrK -(is_iso f).
have Tm1f0 : Tm1f 0 = 0 by rewrite /Tm1f subrr.
have linearTm1f : linear (mkIsometry Tm1f_is_iso).
  by apply central_isometry_is_linear.
have orthogonalTm1f : preserves_dot_products Tm1f.
  move=> x y /=.
  exact: (@central_isometry_preserves_dot_products (mkIsometry Tm1f_is_iso) Tm1f0).  
exists T.
case: (@matrix_of_iso (mkIsometry Tm1f_is_iso) linearTm1f) => g Hg.
exists (lin1_mx g); split; last first.
  split; last by done.
  apply orth_preserves_dotmul.
  move=> x y /=.
  move: (orthogonalTm1f x y).
  move: (Hg x) => /= ->.
  move: (Hg y) => /= -> <-.
  by rewrite 2!mul_rV_lin1.
move=> x.
have <- : Tm1f x = x *m lin1_mx g.
  by rewrite mul_rV_lin1 /=.
by rewrite /Tm1f subrK.
Qed.

Definition ortho_of_iso (f : 'SE_3[R]) : 'M[R]_3 := 
  projT1 (projT2 (trans_ortho_of_iso f)).

Lemma ortho_of_iso_is_ortho f : ortho_of_iso f \is 'O_3[R].
Proof.
rewrite /ortho_of_iso.
by case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
Qed.

Definition iso_sgn (f : 'SE_3[R]) : R := \det (ortho_of_iso f).

End central_isometry.

Section derivative_map.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Definition derivative_map (f : 'SE_3[R]) p (v : tvec p) : tvec (f p) :=
  let C := ortho_of_iso f in
  TVec _ (vtvec v *m C).

Local Notation "f '_*'" := (@derivative_map f _) (at level 5).

Lemma derivative_map_prop (f : 'SE_3[R]) p (u v : tvec p) :
  norm (vtvec (f _* u) - vtvec (f _* v)) = norm (vtvec u - vtvec v).
Proof.
rewrite /derivative_map /=.
rewrite -(mulmxBl (vtvec u) (vtvec v) (ortho_of_iso f) ).
by rewrite orth_preserves_norm // ortho_of_iso_is_ortho.
Qed.

Lemma lem32 p (e1 e2 e3 : vector) (tf : tframe p e1 e2 e3) (f : 'SE_3[R]) :
  vtvec (f _* (TVec p e1)) *d (vtvec (f _* (TVec p e2)) *v vtvec (f _* (TVec p e3))) = 
  iso_sgn f * (e1 *d (e2 *v e3)).
Proof.
case: tf => fo.
move: (orthogonal_expansion e1 (frame_canonical R)).
set a11 := _ *d veci R.
set a12 := _ *d vecj R.
set a13 := _ *d veck R => He1.
move: (orthogonal_expansion e2 (frame_canonical R)).
set a21 := _ *d veci R.
set a22 := _ *d vecj R.
set a23 := _ *d veck R => He2.
move: (orthogonal_expansion e3 (frame_canonical R)).
set a31 := _ *d veci R.
set a32 := _ *d vecj R.
set a33 := _ *d veck R => He3.
have e1a : e1 = row3 a11 a12 a13.
  apply/rowP => i.
  rewrite !mxE /=.
  case: ifPn => [/eqP ->|].
    by rewrite /a11 icoor.
  rewrite ifnot0 => /orP [] /eqP -> /=.
    by rewrite /a12 jcoor.
  by rewrite /a13 kcoor.
have e2a : e2 = row3 a21 a22 a23.
  apply/rowP => i.
  rewrite !mxE /=.
  case: ifPn => [/eqP ->|].
    by rewrite /a21 icoor.
  rewrite ifnot0 => /orP [] /eqP -> /=.
    by rewrite /a22 jcoor.
  by rewrite /a23 kcoor.
have e3a : e3 = row3 a31 a32 a33.
  apply/rowP => i.
  rewrite !mxE /=.
  case: ifPn => [/eqP ->|].
    by rewrite /a31 icoor.
  rewrite ifnot0 => /orP [] /eqP -> /=.
    by rewrite /a32 jcoor.
  by rewrite /a33 kcoor.
transitivity (\det ((ortho_of_iso f)^T *m 
  (triple_prod_mat (row3 a11 a12 a13) (row3 a21 a22 a23) (row3 a31 a32 a33))^T)).
  rewrite /=.
  rewrite -det_tr trmx_mul trmxK mulmx_triple_prod_mat.
  by rewrite -crossmul_triple -e1a -e2a -e3a trmxK.
rewrite det_mulmx det_tr; congr (_ * _).
rewrite det_tr.
by rewrite -crossmul_triple; congr (_ *d (_ *v _)).
Qed.

Lemma preserves_cross p (u v : tvec p) (f : 'SE_3[R]) :
  vtvec (f _* (TVec p ((vtvec u) *v (vtvec v)))) = 
  iso_sgn f *: vtvec (TVec (f p) (vtvec (f _* u) *v vtvec (f _* v))).
Proof.
set tf : tframe _ _ _ _ := frame_trans (TFrame 0 (frame_canonical R)) p.
set u1p := tframe_i tf.
set u2p := tframe_j tf.
set u3p := tframe_k tf.
move: (orthogonal_expansion (vtvec u) (oframe_of_tframe tf)).
set u1 := _ *d @veci _.
set u2 := _ *d @vecj _.
set u3 := _ *d @veck _ => Hu.
move: (orthogonal_expansion (vtvec v) (oframe_of_tframe tf)).
set v1 := _ *d @veci _.
set v2 := _ *d @vecj _.
set v3 := _ *d @veck _ => Hv.
set e1 := f _* (TVec p (u1p)).
set e2 := f _* (TVec p (u2p)).
set e3 := f _* (TVec p (u3p)).
have Ku : f _* u = u1 *: vtvec e1 + u2 *: vtvec e2 + u3 *: vtvec e3 :> vector.
  by rewrite /= Hu 2!mulmxDl !scalemxAl.
have Kv : f _* v = v1 *: vtvec e1 + v2 *: vtvec e2 + v3 *: vtvec e3 :> vector.
  by rewrite /= Hv 2!mulmxDl !scalemxAl.
set eps := vtvec e1 *d (vtvec e2 *v vtvec e3).
have : vtvec (TVec (f p) (vtvec (f _* u) *v vtvec (f _* v))) = 
  eps *: vtvec (f _* (TVec p ((vtvec u) *v (vtvec v)))).
  rewrite /=.
  rewrite (@lem35 _ (vtvec e1) (vtvec e2) (vtvec e3) _ (vtvec (f _* u)) u1 u2 u3 (vtvec (f _* v)) v1 v2 v3) //; last first.
    split => //=.
    by rewrite orth_preserves_norm ?ortho_of_iso_is_ortho // normi.
    by rewrite orth_preserves_norm ?ortho_of_iso_is_ortho // normj.
    by rewrite orth_preserves_norm ?ortho_of_iso_is_ortho // normk.
    rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_ortho //. 
    by case: (frame_canonical R).
    rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_ortho //. 
    by case: (frame_canonical R).
    rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_ortho //. 
    by case: (frame_canonical R).
  rewrite /=.
  rewrite /eps.
  have -> : veci R *m ortho_of_iso f = vtvec e1 by done.
  have -> : vecj R *m ortho_of_iso f = vtvec e2 by done.
  have -> : veck R *m ortho_of_iso f = vtvec e3 by done.
  congr (_ *: _).
  rewrite Hu Hv.
  do 2 rewrite linearD [in RHS]/=.
  rewrite 2!mulmxDl.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite crossmulC scalerN.
  rewrite linearD [in RHS]/=.
  rewrite [in X in _ = - (_ *: X) *m _ + _ + _]linearD.
  rewrite [in RHS]/=.
  rewrite (_ : veci R *v (u1 *: _) = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite (_ : veci R *v (u2 *: _) = u2 *: veck R); last first.
    rewrite linearZ /=.
    by rewrite vecij.
  rewrite (_ : veci R *v (u3 *: _) = - u3 *: vecj R); last first.
    by rewrite linearZ /= vecik scalerN scaleNr.
  rewrite add0r.
  rewrite mulNmx -[in RHS]scalemxAl [in RHS]mulmxDl.
  rewrite -![in RHS]scalemxAl.
  have -> : veck R *m ortho_of_iso f = vtvec e3 by done.
  have -> : vecj R *m ortho_of_iso f = vtvec e2 by done.
  rewrite [in RHS]scalerDr.
  rewrite opprD.
  rewrite crossmulC [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite scaleNr scalerN opprK.
  rewrite (_ : _ *v _ = - u1 *: veck R); last first.
    by rewrite linearZ /= crossmulC vecij scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite addr0.
  rewrite (_ : _ *v _ = u3 *: veci R); last first.
    by rewrite linearZ /= vecjk.
  rewrite scaleNr opprK mulmxBl.
  rewrite -![in RHS]scalemxAl.
  have -> : veci R *m ortho_of_iso f = vtvec e1 by done.
  have -> : veck R *m ortho_of_iso f = vtvec e3 by done.
  rewrite scalerDr scalerN.
  rewrite crossmulC [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite (_ : _ *v _ = u1 *: vecj R); last first.
    by rewrite linearZ /= crossmulC vecik opprK.
  rewrite (_ : _ *v _ = - u2 *: veci R); last first.
    by rewrite linearZ /= crossmulC vecjk scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite subr0 scaleNr opprK mulmxDl mulNmx.
  rewrite -![in RHS]scalemxAl.
  have -> : veci R *m ortho_of_iso f = vtvec e1 by done.
  have -> : vecj R *m ortho_of_iso f = vtvec e2 by done.
  rewrite -![in RHS]addrA [in RHS]addrC -[in RHS]addrA [in RHS]addrCA -[in RHS]addrA [in RHS]addrC.
  rewrite ![in RHS]addrA -[in RHS]addrA.
  congr (_ + _); last first.
    by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u1).
  rewrite scalerDr.
  rewrite -![in RHS]addrA [in RHS]addrCA [in RHS]addrC ![in RHS]addrA -addrA; congr (_ + _).
  by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u2).
  by rewrite scalerN !scalerA -scalerBl -scaleNr opprB mulrC (mulrC u1).
move=> ->.
suff <- : iso_sgn f = eps.
  rewrite scalerA. 
  rewrite -expr2.
  rewrite /iso_sgn -norm2.
  by rewrite orthogonal_det ?ortho_of_iso_is_ortho // expr1n scale1r.
rewrite /eps.
rewrite /e1 /e2 /e3.
rewrite lem32 /=. 
  by rewrite vecjk dotmulvv normi expr1n mulr1.
split.
exact: frame_canonical.
Qed.

End derivative_map.

Notation "f '_*'" := (@derivative_map _ f _) (at level 5).

Section rigid_transformation_is_homogenous_transformation.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

(*Definition direct_iso (f : 'SE_3[R]) := \det (ortho_of_iso f) == 1.
Definition indirect_iso (f : 'SE_3[R]) := \det (ortho_of_iso f) == -1.*)

Definition preserves_orientation (f : 'SE_3[R]) := forall p (u v : tvec p),
  vtvec (f _* (TVec p ((vtvec u) *v (vtvec v)))) =
  TVec (f p) (vtvec (f _* u) *v vtvec (f _* v)).

Lemma direct_iso_preserves_cross_products (f : 'SE_3[R]) :
  iso_sgn f == 1 -> preserves_orientation f.
Proof.
move=> H p u v; move: H.
rewrite preserves_cross /iso_sgn => /eqP ->.
by rewrite scale1r.
Qed.

Lemma preserves_cross_is_direct p (u v : tvec p) (f : 'SE_3[R]) : 
  ~~ colinear (vtvec u) (vtvec v) ->
  vtvec (f _* (TVec p ((vtvec u) *v (vtvec v)))) = 
  vtvec (TVec (f p) (vtvec (f _* u) *v vtvec (f _* v))) -> 
  iso_sgn f == 1.
Proof.
move=> uv0.
rewrite preserves_cross /iso_sgn => H.
apply/eqP.
move: (orthogonal_det (ortho_of_iso_is_ortho f)).
case: (lerP 0 (\det (ortho_of_iso f))) => K.
  by rewrite ger0_norm //.
rewrite ltr0_norm // => /eqP.
rewrite eqr_oppLR => /eqP K1.
rewrite K1 scaleN1r in H.
simpl in H.
move/esym/opp_self : H.
move: (mulmxr_crossmulr (vtvec u) (vtvec v) (ortho_of_iso_is_ortho f)).
rewrite K1 scaleN1r.
move/esym/eqP.
rewrite eqr_oppLR => /eqP ->.
move/eqP.
rewrite oppr_eq0.
rewrite mul_mx_rowfree_eq0; last first.
  apply/row_freeP.
  exists (ortho_of_iso f)^T.
  apply/eqP.
  by rewrite -orthogonalE ortho_of_iso_is_ortho.
move: uv0.
rewrite /colinear.
by move/negbTE => ->.
Qed.

Lemma preserves_norm_orientation_is_htrans (to : 'SE_3[R]) : 
  iso_sgn to == 1 ->
  (exists T : transform R, forall i, to i = homogeneous_ap (i) T).
Proof.
rewrite /iso_sgn /ortho_of_iso.
case: (trans_ortho_of_iso to) => t [r [rt0 - rt1]] /= r1.
have Hr : r^T \is 'SO_3[R].
  by rewrite rotationV rotationE (proj1 rt1).
set T := Transform t Hr.
exists T => i.
(* goal at this point: to i = homogeneous_ap (from i) T *)
rewrite homogeneous_apE /htrans_of_coordinate trmx_mul trmxK.
rewrite hmxE trmx_mul mulmxA.
set fromi' := (HCor (i)) *m _.
suff <- : HCor (to i) = fromi' *m (htrans_of_transform T)^T :> homogeneous R.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  by rewrite (cast_row_mx _ (to i)) row_mxKl castmx_id.
rewrite -[LHS]mulmx1 -trmx1.
move: (inv_htransP T) => /(congr1 trmx) => <-.
rewrite trmx_mul mulmxA; congr (_ *m _).
rewrite {}/fromi'.
suff : to i - t = i *m r.
  rewrite hcoor_inv_htrans => ->.
  by rewrite hcoor_hrot_of_transform trmxK.
move/eqP: (rt0 i) => ->.
by rewrite addrK.
Qed.

(*Variable from : seq coordinate.

Definition preserves_norm_new := 
  forall i j, i \in from -> j \in from ->
  norm (i - j) = norm (to i - to j).

Definition preserves_cos_angle_new := forall i j k, 
  i \in from -> j \in from -> k \in from ->
  cos (vec_angle (j - i) (k - i)) =
  cos (vec_angle (to j - to i) (to k - to i)).

Lemma preserves_norm_cos_angle_new : preserves_norm_new -> preserves_cos_angle_new.
Proof.
move=> H i j k Hi Hj Hk; case/boolP : (norm (k - i) == 0) => [H0|H0].
  rewrite norm_eq0 in H0; rewrite (eqP H0); move: H0.
  rewrite -norm_eq0 (H _ _ Hk Hi) norm_eq0 => /eqP ->; by rewrite /vec_angle 2!dotmulv0 2!crossmulv0.
case/boolP : (norm (j - i) == 0) => H1.
  rewrite norm_eq0 in H1; rewrite (eqP H1); move: H1.
  rewrite -norm_eq0 (H _ _ Hj Hi) norm_eq0 => /eqP ->; by rewrite /vec_angle 2!dotmul0v 2!crossmul0v.
rewrite [in LHS](cosine_law H0 H1); apply/esym; by rewrite [in LHS]cosine_law -?H.
Qed.

Lemma preserves_dotmul_new : preserves_norm_new -> 
  forall p q r, p \in from -> q \in from -> r \in from ->
  (to p - to q) *d (to r - to q) = (p - q) *d (r - q).
Proof.
move=> pnorm p q r Hp Hq Hr.
by rewrite !dotmul_cos -(pnorm _ _ Hp Hq) -(pnorm _ _ Hr Hq) -[in LHS](preserves_norm_cos_angle_new).
Qed.
*)

(* old displacementP direct part1 *)
Lemma htrans_preserves_norm (to : coordinate -> coordinate) :
  (exists T : transform R, forall i, to i = homogeneous_ap i T) ->
  preserves_diff to.
Proof.
case=> [T /= HT] => /= m0 m1.
rewrite 2!HT -(htrans_of_vector_preserves_norm (m0 - m1) T).
by rewrite -htrans_of_coordinateB coord_of_hB.
Qed.

Definition preserves_angle (to : coordinate -> coordinate) :=
  forall i j k, vec_angle (j - i) (k - i) =
                vec_angle (to j - to i) (to k - to i).

(* old displacementP direct part2 *)
Lemma htrans_preserves_angle to :
  (exists T : transform R, forall i, to i = homogeneous_ap (i) T) ->
  preserves_angle to.
Proof.
case=> [T /= HT] => /= m0 m1 k.
rewrite 3!HT /homogeneous_ap -2!coord_of_hB 2!htrans_of_coordinateB.
rewrite 2!coord_of_ht_htrans_of_vectorE -orth_preserves_vec_angle //.
rewrite orthogonalV; apply rotation_sub; by case: T HT.
Qed.

Lemma htrans_preserves_orientation (to : coordinate -> coordinate) (T : transform R) 
  (HT : (forall i, to i = homogeneous_ap i T)) :
  preserves_orientation (mkIsometry (htrans_preserves_norm (ex_intro _ _ HT))).
Proof.
move=> p u v.
simpl.
(*
case=> [T /= HT] => /= i j k l a b c a' b' c'.
rewrite /a' /b' /c' !HT /homogeneous_ap -2!coord_of_hB 2!htrans_of_coordinateB.
rewrite !coord_of_ht_htrans_of_vectorE -coord_of_hB htrans_of_coordinateB.
rewrite coord_of_ht_htrans_of_vectorE -mulmxr_crossmulr_SO; last first.
  case: T HT => *; by rewrite rotationV.
rewrite -(@orth_preserves_vec_angle _ (rot T)^T) // orthogonalV.
case: T HT => ? r /= Hr _; rewrite rotationE in Hr; by case/andP : Hr.
Qed.*) Abort.

(*
(* hypothesis that there is at least three non-colinear points in the rigid body *)
Variables l1 l2 l3 r1 r2 r3 : coordinate.
Hypotheses (l12 : l1 != l2) (r12 : r1 != r2).
Hypotheses (l123 : ~~ colinear (l2 - l1) (l3 - l1)) (r123 : ~~ colinear (r2 - r1) (r3 - r1)).
Variable n' : nat.
Let n := n'.+3.
(*Variables from to : coordinate ^ n.
Hypotheses (from0 : from 0 = l1) (from1 : from 1 = l2) (from2 : from 2%:R = l3).*)
Hypotheses (from0 : l1 \in from) (from1 : l2 \in from) (from2 : l3 \in from).
Hypotheses (to0 : to l1 = r1) (to1 : to l2 = r2) (to2 : to l3 = r3).

Definition preserves_sin_angle_new := forall i j k, 
  i \in from -> j \in from -> k \in from ->
  `| sin (vec_angle (j - i) (k - i)) | =
  `| sin (vec_angle (to j - to i) (to k - to i)) |.

Lemma preserves_cos_sin_angle_new : preserves_cos_angle_new -> preserves_sin_angle_new.
Proof.
move=> H i j k Hi Hj Hk; apply/eqP.
rewrite -(@eqr_expn2 _ 2 _ _ erefl) ?normr_ge0; try reflexivity.
apply/eqP; rewrite -[in LHS]normrX -[in RHS]normrX.
set a := (X in `| sin X ^+ _ | = _). set b := (X in _ = `| sin X ^+ _| ).
move: (cos2Dsin2 a) => /esym/eqP.
rewrite addrC -subr_eq => /eqP Ha.
move: (cos2Dsin2 b) => /esym/eqP.
rewrite addrC -subr_eq => /eqP Hb.
rewrite [in LHS]ger0_norm; last by rewrite sqr_ge0.
rewrite [in RHS]ger0_norm; last by rewrite sqr_ge0.
by rewrite -[in LHS]Ha -Hb [in LHS]H.
Qed.

Lemma rigid_preserves_cos_vec_angleD_new : preserves_norm_new -> forall i j k l cst, 
  j \in from -> i \in from -> k \in from -> l \in from ->
  cos (vec_angle (to j - to i) ((to k - to i) - cst *: (to l - to i))) =
  cos (vec_angle (j - i) ((k - i) - cst *: (l - i))).
Proof.
move=> pnorm /= i0 j k l cst Hj Hi Hk Hl.
case/boolP : (cst == 0) => [/eqP ->{cst}|cst0]. 
  by rewrite 2!scale0r 2!subr0 [in RHS](preserves_norm_cos_angle_new).
rewrite /vec_angle.
set rhs := RHS. set a := _ +i* _. rewrite {}/rhs.
set lhs := LHS. set b := _ +i* _. rewrite {}/lhs.
suff : a = b by move=> ->.
rewrite {}/a {}/b.
apply/eqP; rewrite eq_complex /=.
apply/andP; split; apply/eqP.
  rewrite [in LHS]dotmulDr [RHS]dotmulDr [in LHS]dotmul_cos [in RHS]dotmul_cos.
  rewrite [in RHS](pnorm j i0 Hj Hi) -[in LHS](pnorm k i0 Hk Hi) [in RHS](preserves_norm_cos_angle_new pnorm Hi Hj Hk).
  rewrite -2!scaleNr 2!dotmulvZ 2!dotmul_cos -(pnorm j i0 Hj Hi) -(pnorm l i0 Hl Hi).
  rewrite -[in X in X + _ = _](preserves_norm_cos_angle_new pnorm Hi Hj Hk). 
  rewrite -[in X in _ + X = _](preserves_norm_cos_angle_new pnorm Hi Hj Hl). 
  by rewrite -[in X in _ = X + _](preserves_norm_cos_angle_new pnorm). 
set a := to j - to i0. set b := to k - to i0. set c := to l - to i0.
set a' := j - i0. set b' := k - i0. set c' := l - i0.
rewrite [in LHS]linearD [in RHS]linearD /= -2!scaleNr 2!linearZ /= [in LHS](normD (a *v b) (- cst *: (a *v c))).
rewrite [in RHS](normD (a' *v b') (- cst *: (a' *v c'))).
rewrite -[in RHS](_ : norm (a *v b) = norm (a' *v b')); last first.
  rewrite [in LHS]norm_crossmul [in RHS]norm_crossmul /a /b /a' /b' (pnorm _ _ Hj Hi).
  rewrite (pnorm _ _ Hk Hi).
    by rewrite [in RHS](preserves_cos_sin_angle_new (preserves_norm_cos_angle_new pnorm)).
rewrite -[in RHS](_ : norm (- cst *: (a *v c)) = norm (- cst *: (a' *v c'))); last first.
  rewrite [in RHS]normZ [in LHS]normZ.
  rewrite [in RHS]norm_crossmul [in LHS]norm_crossmul /a /c /a' /c'.
     rewrite (pnorm _ _ Hj Hi) (pnorm _ _ Hl Hi).
  by rewrite [in RHS](preserves_cos_sin_angle_new (preserves_norm_cos_angle_new pnorm)).
case: (ltrP cst 0) => cst0'.
  rewrite (_ : - cst = `| cst |); last by rewrite ltr0_norm.
  rewrite [in LHS]vec_angleZ; last by rewrite normr_gt0 ltr0_neq0.
  rewrite [in RHS]vec_angleZ; last by rewrite normr_gt0 ltr0_neq0.
  rewrite [in LHS](_ : vec_angle _ _ = vec_angle (a' *v b') (a' *v c')); first by reflexivity.
  apply preserve_vec_angle_crossmul2.
    by rewrite (pnorm _ _ Hj Hi).
    by rewrite (pnorm _ _ Hk Hi).
    by rewrite (pnorm _ _ Hl Hi).
    by rewrite -[in LHS](preserves_norm_cos_angle_new pnorm).
    by rewrite -[in LHS](preserves_norm_cos_angle_new pnorm).
    by rewrite -[in LHS](preserves_norm_cos_angle_new pnorm).
rewrite [in LHS]vec_angleZ_neg; last by rewrite oppr_lt0 ltr_neqAle eq_sym cst0.
rewrite [in RHS]vec_angleZ_neg; last by rewrite oppr_lt0 ltr_neqAle eq_sym cst0.
case/boolP : (a *v b == 0) => [/eqP|] ab0.
  by rewrite ab0 norm0 -exprnP expr0n /= mul0r [in LHS]mul0r mul0r. 
case/boolP : (a *v c == 0) => [/eqP|] ac0.
  by rewrite ac0 scaler0 norm0 mulr0 [in LHS]mul0r mul0r.
rewrite [in LHS](cos_vec_angleNv ab0 ac0).
case/boolP : (a' *v b' == 0) => [/eqP|] ab'0.
  have -> : norm (a *v b) = 0.
    transitivity (norm (a' *v b')).
      rewrite [in LHS]norm_crossmul [in RHS]norm_crossmul /a /b /a' /b'.
      rewrite (pnorm _ _ Hj Hi) (pnorm _ _ Hk Hi).
      by rewrite [in RHS](preserves_cos_sin_angle_new (preserves_norm_cos_angle_new pnorm)).
    by rewrite ab'0 norm0.
  by rewrite [in LHS]mul0r 3!mul0r.
case/boolP : (a' *v c' == 0) => [/eqP|] ac'0.
  rewrite normZ (_ : norm (a *v c) = 0); last first.
    rewrite norm_crossmul -(pnorm _ _ Hj Hi) -(pnorm _ _ Hl Hi).
    rewrite -[in LHS](preserves_cos_sin_angle_new (preserves_norm_cos_angle_new pnorm) Hi Hj Hl) -norm_crossmul.
    by apply/eqP; rewrite norm_eq0; apply/eqP.
  by rewrite [in LHS]mulr0 [in LHS]mulr0 mul0r mulr0 mulr0 mul0r.
rewrite [in RHS](cos_vec_angleNv ab'0 ac'0).
rewrite [in LHS](_ : vec_angle _ _ = vec_angle (a' *v b') (a' *v c')); first by reflexivity.
apply preserve_vec_angle_crossmul2.
  by rewrite (pnorm _ _ Hj Hi).
  by rewrite (pnorm _ _ Hk Hi).
  by rewrite (pnorm _ _ Hl Hi).
  by rewrite -[in LHS](preserves_norm_cos_angle_new pnorm).
  by rewrite -[in LHS](preserves_norm_cos_angle_new pnorm).
  by rewrite -[in LHS](preserves_norm_cos_angle_new pnorm).
Qed.

(* old displacementP converse *)
Lemma preserves_norm_orientation_is_htrans : 
  preserves_norm_new -> preserves_angle_new ->
  (exists T : transform R, forall i, i \in from -> to i = homogeneous_ap (i) T).
Proof.
move=> pnorm porientation.
set r := rot3 l1 l2 l3 r1 r2 r3.
move: (rot3_is_SO l12 r12 l123 r123).
rewrite -rotationV => Hr.
set t := trans3 l1 l2 l3 r1 r2 r3.
set T := Transform t Hr.
exists T => i Hi.
(* goal at this point: to i = homogeneous_ap (from i) T *)
rewrite homogeneous_apE /htrans_of_coordinate trmx_mul trmxK.
rewrite hmxE trmx_mul mulmxA.
set fromi' := (HCor (i)) *m _.
suff : HCor (to i) = fromi' *m (htrans_of_transform T)^T :> homogeneous R.
  move=> <-.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  by rewrite (cast_row_mx _ (to i)) row_mxKl castmx_id.
rewrite -[LHS]mulmx1 -trmx1.
move: (inv_htransP T) => /(congr1 trmx) => <-.
rewrite trmx_mul mulmxA.
congr (_ *m _).
rewrite {}/fromi'.
suff : to i - t = i *m r.
  rewrite hcoor_inv_htrans => ->; by rewrite hcoor_hrot_of_transform trmxK.
rewrite /t /trans3 -/r opprB -(addrC (- r1)) addrA -(opprK (l1 *m r)).
apply/eqP; rewrite subr_eq; apply/eqP.
rewrite -mulmxBl /r /rot3 mulmxA.
rewrite -(mulmx1 (to i - r1)).
move/rotation_sub : (rots2_is_SO l1 l2 l3 r12 r123).
rewrite orthogonalEC => /eqP /(congr1 trmx).
rewrite trmx_mul trmxK trmx1 => <-.
rewrite mulmxA.
set M1 := (X in X *m _ = _). set M2 := (X in _ = X *m _).
rewrite (_ : M1 = M2); first by reflexivity.
rewrite {}/M1 {}/M2 {1}/rots triple_prod_mat_mulmx {1}/rots triple_prod_mat_mulmx.
(* goal at this point: 
  projections of (to i - r1) along x_r/y_r/z_r
  = projections of (to i - l1) along x_l/y_l/z_l
*)
rewrite (_ : _ *d xtriad r1 r2 = (i - l1) *d xtriad l1 l2); last first.
  by rewrite /xtriad /normalize 2!dotmulvZ -to0 -to1 (pnorm l2 l1 from1 from0) (preserves_dotmul_new pnorm) //.
rewrite (_ : _ *d ytriad r1 r2 r3 = (i - l1) *d ytriad l1 l2 l3); last first.
(*  rewrite /ytriad /normalize 2!dotmulZ.
  rewrite {2 4}/orthogonalize [in LHS]dotmulDr [in RHS]dotmulDr.
  rewrite /normalize (xtriad_norm l12) (xtriad_norm r12).
  rewrite divrr ?scale1r; last by rewrite unitr1.
  rewrite !dotmulvN !dotmulZ.
  rewrite -from0 -from1 -from2 -to1 -to0 -to2.
  rewrite !(preserves_dotmul pnorm) !pnorm.
  suff Htmp : norm (orthogonalize (xtriad (to 0) (to 1)) (to 2%:R - to 0)) =
         norm (orthogonalize (xtriad (from 0) (from 1)) (from 2%:R - from 0)).
    by rewrite [in LHS]Htmp.
  rewrite /orthogonalize.*)
  rewrite dotmul_cos (ytriad_norm r12 r123) dotmul_cos (ytriad_norm l12 l123) 2!mulr1.
  rewrite -to0 -to1 -to2 (pnorm _ _ Hi from0). 
  rewrite {1}/ytriad {1}/orthogonalize {1}/normalize.
  rewrite vec_angleZ; last first.
    rewrite (_ : _ - _ - _ = orthogonalize (xtriad (to l1) (to l2)) (to l3 - to l1)); last by reflexivity.
    rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT.
    by rewrite eq_sym -normalize_eq0 to0 to1 to2 norm_eq0 ytriad_neq0.
  rewrite {2}/normalize scalerA {3}/xtriad {2}/normalize scalerA.
  rewrite [in LHS](@rigid_preserves_cos_vec_angleD_new pnorm l1 i l3 l2
    ((to l3 - to l1) *d normalize (xtriad (to l1) (to l2)) *
        (1 / norm (xtriad (to l1) (to l2))) * (1 / norm (to l2 - to l1))) Hi from0 from2 from1).
  rewrite /ytriad [in RHS]/normalize vec_angleZ; last first.
    rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT.
    by rewrite eq_sym -normalize_eq0 norm_eq0 ytriad_neq0.
  rewrite [in RHS]/orthogonalize {3}/normalize {3}[in RHS]/xtriad {3}/normalize scalerA.
  rewrite xtriad_norm; last by rewrite to0 to1.
  rewrite xtriad_norm; last by done.
  rewrite -[in RHS]scalerA.
  suff -> : (to l3 - to l1) *d normalize (xtriad (to l1) (to l2)) = 
    (l3 - l1) *d normalize (xtriad (l1) (l2)).
    by rewrite -(pnorm _ _ from1 from0) ![in RHS]scalerA -mulrA.
  rewrite /normalize 2!dotmulvZ xtriad_norm //; last by rewrite to0 to1.
  rewrite 2!dotmulvZ xtriad_norm; last by done.
  by rewrite (pnorm _ _ from1 from0) (preserves_dotmul_new pnorm from2 from0 from1). 
rewrite (_ : _ *d (xtriad r1 r2 *v ytriad r1 r2 r3) =
             (i - l1) *d (xtriad l1 l2 *v ytriad l1 l2 l3)); first by reflexivity.
rewrite dotmul_cos dotmul_cos -{1}to0 -(pnorm _ _ Hi from0).
rewrite [in LHS](ztriad_norm r12 r123) [in RHS](ztriad_norm l12 l123) mulr1.
suff Htmp : cos (vec_angle (to i - r1) (xtriad r1 r2 *v ytriad r1 r2 r3)) =
  cos (vec_angle (i - l1) (xtriad l1 l2 *v ytriad l1 l2 l3)).
  by rewrite [in LHS]Htmp.
rewrite /xtriad /normalize linearZ /= vec_angleZ; last first.
  rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
  by rewrite -norm_eq0 -normalize_eq0 (ytriad_norm r12 r123) oner_neq0.
rewrite linearZ /= vec_angleZ; last first.
  rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
  by rewrite -norm_eq0 -normalize_eq0 (ytriad_norm l12 l123) oner_neq0.
rewrite crossmulZ vec_angleZ; last first.
  by rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0 subr_eq0 eq_sym.
rewrite crossmulZ vec_angleZ; last first.
  by rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0 subr_eq0 eq_sym.
rewrite /orthogonalize.
rewrite -to0 -to1 -to2.
rewrite normalizeI {2}/normalize scalerA.
rewrite normalizeI {3}/normalize scalerA.
have -> : (to l3 - to l1) *d normalize (to l2 - to l1) = (l3 - l1) *d normalize (l2 - l1).
  by rewrite /normalize 2!dotmulvZ (pnorm _ _ from1 from0) -(preserves_dotmul_new pnorm from2 from0 from1).
rewrite linearD /= [in RHS]linearD /= 2!crossmulvN linearZ /= crossmulvv [in LHS]scaler0 subr0.
rewrite linearZ /= crossmulvv scaler0 subr0.
have -> : (l2 - l1) *v (l3 - l1) = (l2 - l1) *v (l3 - l1) + l1 - l1.
  by rewrite addrK.
have -> : ((to l2 - to l1) *v (to l3 - to l1)) = 
  to ((l2 - l1) *v (l3 - l1) + l1) - to l1.
  admit.
by rewrite -porientation.
Abort.
*)

End rigid_transformation_is_homogenous_transformation.

(*
Section rigid_transformation_is_homogenous_transformation.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Definition preserves_angle n (from to : coordinate ^ n) :=
  forall i j k, vec_angle (from j - from i) (from k - from i) =
                vec_angle (to j - to i) (to k - to i).

(* old displacementP direct part1 *)
Lemma htrans_preserves_norm m (from to : coordinate ^ m) : 
  (exists T : transform R, forall i, to i = homogeneous_ap (from i) T) ->
  preserves_norm from to.
Proof.
case=> [T /= HT] => /= m0 m1.
rewrite 2!HT -(htrans_of_vector_preserves_norm (from m0 - from m1) T).
by rewrite -htrans_of_coordinateB coord_of_hB.
Qed.

(* old displacementP direct part2 *)
Lemma htrans_preserves_angle m (from to : coordinate ^ m) : 
  (exists T : transform R, forall i, to i = homogeneous_ap (from i) T) ->
  preserves_angle from to.
Proof.
case=> [T /= HT] => /= m0 m1 k.
rewrite 3!HT /homogeneous_ap -2!coord_of_hB 2!htrans_of_coordinateB.
rewrite 2!coord_of_ht_htrans_of_vectorE -orth_preserves_vec_angle //.
rewrite orthogonalV; apply rotation_sub; by case: T HT.
Qed.

Lemma htrans_preserves_orientation m (from to : coordinate ^ m) : 
  (exists T : transform R, forall i, to i = homogeneous_ap (from i) T) ->
  preserves_orientation from to.
Proof.
case=> [T /= HT] => /= i j k l a b c a' b' c'.
rewrite /a' /b' /c' !HT /homogeneous_ap -2!coord_of_hB 2!htrans_of_coordinateB.
rewrite !coord_of_ht_htrans_of_vectorE -coord_of_hB htrans_of_coordinateB.
rewrite coord_of_ht_htrans_of_vectorE -mulmxr_crossmulr_SO; last first.
  case: T HT => *; by rewrite rotationV.
rewrite -(@orth_preserves_vec_angle _ (rot T)^T) // orthogonalV.
case: T HT => ? r /= Hr _; rewrite rotationE in Hr; by case/andP : Hr.
Qed.

(* hypothesis that there is at least three non-colinear points in the rigid body *)
Variables l1 l2 l3 r1 r2 r3 : coordinate.
Hypotheses (l12 : l1 != l2) (r12 : r1 != r2).
Hypotheses (l123 : ~~ colinear (l2 - l1) (l3 - l1)) (r123 : ~~ colinear (r2 - r1) (r3 - r1)).
Variable n' : nat.
Let n := n'.+3.
Variables from to : coordinate ^ n.
Hypotheses (from0 : from 0 = l1) (from1 : from 1 = l2) (from2 : from 2%:R = l3).
Hypotheses (to0 : to 0 = r1) (to1 : to 1 = r2) (to2 : to 2%:R = r3).

(* old displacementP converse *)
Lemma preserves_norm_orientation_is_htrans : 
  preserves_norm from to -> preserves_orientation from to ->
  (exists T : transform R, forall i, to i = homogeneous_ap (from i) T).
Proof.
move=> pnorm porientation.
set r := rot3 l1 l2 l3 r1 r2 r3.
move: (rot3_is_SO l12 r12 l123 r123).
rewrite -rotationV => Hr.
set t := trans3 l1 l2 l3 r1 r2 r3.
set T := Transform t Hr.
exists T => i.
(* goal at this point: to i = homogeneous_ap (from i) T *)
rewrite homogeneous_apE /htrans_of_coordinate trmx_mul trmxK.
rewrite hmxE trmx_mul mulmxA.
set fromi' := (HCor (from i)) *m _.
suff : HCor (to i) = fromi' *m (htrans_of_transform T)^T :> homogeneous R.
  move=> <-.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  by rewrite (cast_row_mx _ (to i)) row_mxKl castmx_id.
rewrite -[LHS]mulmx1 -trmx1.
move: (inv_htransP T) => /(congr1 trmx) => <-.
rewrite trmx_mul mulmxA.
congr (_ *m _).
rewrite {}/fromi'.
suff : to i - t = from i *m r.
  rewrite hcoor_inv_htrans => ->; by rewrite hcoor_hrot_of_transform trmxK.
rewrite /t /trans3 -/r opprB -(addrC (- r1)) addrA -(opprK (l1 *m r)).
apply/eqP; rewrite subr_eq; apply/eqP.
rewrite -mulmxBl /r /rot3 mulmxA.
rewrite -(mulmx1 (to i - r1)).
move/rotation_sub : (rots2_is_SO l1 l2 l3 r12 r123).
rewrite orthogonalEC => /eqP /(congr1 trmx).
rewrite trmx_mul trmxK trmx1 => <-.
rewrite mulmxA.
set M1 := (X in X *m _ = _). set M2 := (X in _ = X *m _).
rewrite (_ : M1 = M2); first by reflexivity.
rewrite {}/M1 {}/M2 {1}/rots triple_prod_mat_mulmx {1}/rots triple_prod_mat_mulmx.
(* goal at this point: 
  projections of (to i - r1) along x_r/y_r/z_r
  = projections of (to i - l1) along x_l/y_l/z_l
*)
rewrite (_ : _ *d xtriad r1 r2 = (from i - l1) *d xtriad l1 l2); last first.
  by rewrite /xtriad /normalize 2!dotmulvZ -from0 -from1 -to0 -to1 pnorm (preserves_dotmul pnorm).
rewrite (_ : _ *d ytriad r1 r2 r3 = (from i - l1) *d ytriad l1 l2 l3); last first.
(*  rewrite /ytriad /normalize 2!dotmulZ.
  rewrite {2 4}/orthogonalize [in LHS]dotmulDr [in RHS]dotmulDr.
  rewrite /normalize (xtriad_norm l12) (xtriad_norm r12).
  rewrite divrr ?scale1r; last by rewrite unitr1.
  rewrite !dotmulvN !dotmulZ.
  rewrite -from0 -from1 -from2 -to1 -to0 -to2.
  rewrite !(preserves_dotmul pnorm) !pnorm.
  suff Htmp : norm (orthogonalize (xtriad (to 0) (to 1)) (to 2%:R - to 0)) =
         norm (orthogonalize (xtriad (from 0) (from 1)) (from 2%:R - from 0)).
    by rewrite [in LHS]Htmp.
  rewrite /orthogonalize.*)
  rewrite dotmul_cos (ytriad_norm r12 r123) dotmul_cos (ytriad_norm l12 l123) 2!mulr1.
  rewrite -from0 -to0 -to1 -from1 -to2 -from2 pnorm. 
  rewrite {1}/ytriad {1}/orthogonalize {1}/normalize.
  rewrite vec_angleZ; last first.
    rewrite (_ : _ - _ - _ = orthogonalize (xtriad (to 0) (to 1)) (to 2%:R - to 0)); last by reflexivity.
    rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT.
    by rewrite eq_sym -normalize_eq0 to0 to1 to2 norm_eq0 ytriad_neq0.
  rewrite {2}/normalize scalerA {3}/xtriad {2}/normalize scalerA.
  rewrite [in LHS](rigid_preserves_cos_vec_angleD pnorm 0 i 2%:R 1 
    ((to 2%:R - to 0) *d normalize (xtriad (to 0) (to 1)) *
        (1 / norm (xtriad (to 0) (to 1))) * (1 / norm (to 1 - to 0)))).
  rewrite /ytriad [in RHS]/normalize vec_angleZ; last first.
    rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT.
    by rewrite eq_sym -normalize_eq0 from0 from1 from2 norm_eq0 ytriad_neq0.
  rewrite [in RHS]/orthogonalize {3}/normalize {3}[in RHS]/xtriad {3}/normalize scalerA.
  rewrite xtriad_norm; last by rewrite to0 to1.
  rewrite xtriad_norm; last by rewrite from0 from1.
  rewrite -[in RHS]scalerA.
  suff -> : (to 2%:R - to 0) *d normalize (xtriad (to 0) (to 1)) = 
    (from 2%:R - from 0) *d normalize (xtriad (from 0) (from 1)).
    by rewrite -(pnorm 1 0) ![in RHS]scalerA -mulrA.
  rewrite /normalize 2!dotmulvZ xtriad_norm //; last by rewrite to0 to1.
  rewrite 2!dotmulvZ xtriad_norm; last by rewrite from0 from1.
  by rewrite pnorm (preserves_dotmul pnorm). 
rewrite (_ : _ *d (xtriad r1 r2 *v ytriad r1 r2 r3) =
             (from i - l1) *d (xtriad l1 l2 *v ytriad l1 l2 l3)); first by reflexivity.
rewrite dotmul_cos dotmul_cos -{1}to0 -pnorm from0.
rewrite [in LHS](ztriad_norm r12 r123) [in RHS](ztriad_norm l12 l123) mulr1.
suff Htmp : cos (vec_angle (to i - r1) (xtriad r1 r2 *v ytriad r1 r2 r3)) =
  cos (vec_angle (from i - l1) (xtriad l1 l2 *v ytriad l1 l2 l3)).
  by rewrite [in LHS]Htmp.
rewrite /xtriad /normalize linearZ /= vec_angleZ; last first.
  rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
  by rewrite -norm_eq0 -normalize_eq0 (ytriad_norm r12 r123) oner_neq0.
rewrite linearZ /= vec_angleZ; last first.
  rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
  by rewrite -norm_eq0 -normalize_eq0 (ytriad_norm l12 l123) oner_neq0.
rewrite crossmulZ vec_angleZ; last first.
  by rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0 subr_eq0 eq_sym.
rewrite crossmulZ vec_angleZ; last first.
  by rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0 subr_eq0 eq_sym.
rewrite /orthogonalize.
rewrite -to0 -to1 -to2 -from0 -from1 -from2.
rewrite normalizeI {2}/normalize scalerA.
rewrite normalizeI {3}/normalize scalerA.
have -> : (to 2%:R - to 0) *d normalize (to 1 - to 0) = (from 2%:R - from 0) *d normalize (from 1 - from 0).
  by rewrite /normalize 2!dotmulvZ pnorm -(preserves_dotmul pnorm).
rewrite linearD /= [in RHS]linearD /= 2!crossmulvN linearZ /= crossmulvv [in LHS]scaler0 subr0.
rewrite linearZ /= crossmulvv scaler0 subr0.
by rewrite [in LHS](rigid_preserves_cos_vec_angle_crossmul pnorm porientation).
Qed.

End rigid_transformation_is_homogenous_transformation.
*)

Section chains.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := Frame.t R.

Record joint := mkJoint {
  offset : R ;
  joint_angle : angle R }.

Record link := mkLink {
  length : R ;
  twist : angle R }.

Variable n' : nat.
Let n := n'.+1.
Variables chain : {ffun 'I_n -> frame * link * joint}.
Definition frames := fun i => (chain (insubd ord0 i)).1.1.
Definition links := fun i => (chain (insubd ord0 i)).1.2.
Definition joints := fun i => (chain (insubd ord0 i)).2.

(* by definition, zi = axis of joint i *)

Local Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Local Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Definition common_normal_xz (i : 'I_n) :=
  (Frame.z (frames i.-1)) _|_ (Frame.z (frames i)), (Frame.x (frames i.-1)).

End chains.

Section anti_sym_def.

Variables (n : nat) (R : rcfType).

Definition anti := [qualify M : 'M[R]_n | M == - M^T].
Fact anti_key : pred_key anti. Proof. by []. Qed.
Canonical anti_keyed := KeyedQualifier anti_key.

Definition sym := [qualify M : 'M[R]_n | M == M^T].
Fact sym_key : pred_key sym. Proof. by []. Qed.
Canonical sym_keyed := KeyedQualifier sym_key.

End anti_sym_def.

Local Notation "''so_' n [ R ]" := (anti n R)
  (at level 8, n at level 2, format "''so_' n [ R ]").

Section skew.

Variable R : rcfType.

Lemma antiE {n} M : (M \is 'so_n[R]) = (M == - M^T). Proof. by []. Qed.

Lemma symE {n} M : (M \is sym n R) = (M == M^T). Proof. by []. Qed.

Let vector := 'rV[R]_3.

Lemma anti_diag {n} M (i : 'I_n) : M \is 'so_n[R] -> M i i = 0.
Proof.
rewrite antiE -addr_eq0 => /eqP/matrixP/(_ i i); rewrite !mxE.
by rewrite -mulr2n -mulr_natr => /eqP; rewrite mulf_eq0 pnatr_eq0 orbF => /eqP.
Qed.

Lemma antiP {n} (A B : 'M[R]_n) : A \is 'so_n[R] -> B \is 'so_n[R] -> 
  (forall i j : 'I_n, (i < j)%N -> A i j = - B j i) -> A = B.
Proof.
move=> soA soB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by do 2 rewrite anti_diag //.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (soA); by rewrite antiE => /eqP ->; rewrite 2!mxE AB // opprK.
move=> {ij}ij; rewrite AB //.
move: (soB); rewrite antiE -eqr_oppLR => /eqP/matrixP/(_ i j).
rewrite !mxE => <-; by rewrite opprK.
Qed.

Lemma symP {n} (A B : 'M[R]_n) : A \in sym n R -> B \in sym n R -> 
  (forall i j : 'I_n, (i <= j)%N -> A i j = B i j) -> A = B.
Proof.
move=> symA symB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite AB.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (symA) (symB) => /eqP -> /eqP ->; by rewrite 2!mxE AB // leq_eqVlt ij orbC.
by move=> {ij}ij; rewrite AB // leq_eqVlt ij orbC.
Qed.

(* (anti)symmetric parts of a matrix *)
Definition symp {n} (A : 'M[R]_n) := 1/2%:R *: (A + A^T).
Definition antip {n} (A : 'M[R]_n) := 1/2%:R *: (A - A^T).

Lemma symp_antip {n} (A : 'M[R]_n) : A = symp A + antip A.
Proof.
rewrite /symp /antip -scalerDr addrCA addrK -mulr2n- scaler_nat.
by rewrite scalerA div1r mulVr ?pnatr_is_a_unit // scale1r.
Qed.

Lemma antip_is_so {n} (M : 'M[R]_n) : antip M \is 'so_n[R].
Proof.
rewrite antiE /antip; apply/eqP; rewrite [in RHS]linearZ -scalerN /=.
by rewrite [in RHS]linearD /= opprD linearN /= opprK trmxK addrC.
Qed.

Lemma antip_scaler_closed {n} : GRing.scaler_closed 'so_n[R].
Proof.
move=> ? ?; rewrite antiE => /eqP H; by rewrite antiE linearZ /= -scalerN -H.
Qed.

Lemma sym_symp {n} (M : 'M[R]_n) : symp M \in sym n R.
Proof.
by apply/eqP; rewrite /symp linearZ /= [in RHS]linearD /= trmxK addrC.
Qed.

Lemma sym_oppr_closed {n} : oppr_closed (sym n R).
Proof. move=> /= M /eqP HM; apply/eqP; by rewrite linearN /= -HM. Qed.

Lemma sym_addr_closed {n} : addr_closed (sym n R).
Proof.
split; first by rewrite symE trmx0.
move=> /= A B; rewrite 2!symE => /eqP sA /eqP sB.
by rewrite symE linearD /= -sA -sB.
Qed.

Canonical SymOpprPred n := OpprPred (@sym_oppr_closed n).
Canonical SymAddrPred n := AddrPred (@sym_addr_closed n).

Lemma sym_scaler_closed {n} : GRing.scaler_closed (sym n R).
Proof. move=> ? ?; rewrite 2!symE => /eqP H; by rewrite linearZ /= -H. Qed.

Lemma sym1 {n} : 1%:M \is sym n R.
Proof. by rewrite symE trmx1. Qed.

Lemma mul_tr_vec_sym (u : vector) : u^T *m u \is sym 3 R.
Proof. apply/eqP; by rewrite trmx_mul trmxK. Qed.

(* TODO: Canonical? *)

Lemma trace_anti {n} (M : 'M[R]_n) : M \is 'so_n[R] -> \tr M = 0.
Proof.
move/anti_diag => m; by rewrite /mxtrace (eq_bigr (fun=> 0)) // sumr_const mul0rn.
Qed.

Definition skew_mx (w : vector) : 'M[R]_3 := - \matrix_i (w *v delta_mx 0 i).

Lemma skew_mx0 : skew_mx 0 = 0.
Proof.
by apply/matrixP => i j; rewrite !mxE -crossmul_triple crossmul0v dotmulv0 oppr0.
Qed.

Lemma anti_skew u : skew_mx u \is 'so_3[R].
Proof.
rewrite antiE; apply/eqP/matrixP => i j; rewrite !mxE -triple_prod_mat_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma skew01 u : skew_mx u 0 1 = - u 0 2%:R.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, addr0, subr0). Qed.

Lemma skew02 u : skew_mx u 0 2%:R = u 0 1%:R.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, add0r, opprK). Qed.

Lemma skew10 u : skew_mx u 1 0 = u 0 2%:R.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew01 opprK. Qed.

Lemma skew12 u : skew_mx u 1 2%:R = - u 0 0.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, subr0). Qed.

Lemma skew20 u : skew_mx u 2%:R 0 = - u 0 1%:R.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew02. Qed.

Lemma skew21 u : skew_mx u 2%:R 1 = u 0 0.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew12 opprK. Qed.

Lemma skewii u i : skew_mx u i i = 0.
Proof. by rewrite anti_diag // anti_skew. Qed.

Definition skewij := (skew01, skew10, skew02, skew20, skew21, skew12, skewii).

Lemma skew_mxE (u w : vector) : u *m (skew_mx w) = u *v w.
Proof.
rewrite [RHS]crossmulC -crossmulvN [u]row_sum_delta -/(mulmxr _ _) !linear_sum.
apply: eq_bigr=> i _; by rewrite !linearZ /= -rowE linearN /= rowK crossmulvN.
Qed.

(* more general result for antisymmetric matrices? *)
Lemma det_skew_mx (u : 'rV[R]_3) : \det (skew_mx u) = 0.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite skew_mx0 det0.
apply/eqP/det0P; exists u => //; by rewrite skew_mxE crossmulvv.
Qed.

Lemma sqr_antip (M : 'M[R]_3) : M \is 'so_3[R] ->
  M ^+ 2 = \matrix_i [eta \0 with 0 |-> (\row_j [eta \0 with 
0 |-> - M 0 1 ^+ 2 - M 0 2%:R ^+ 2, 1 |-> - M 1 2%:R * M 0 2%:R, 2%:R |-> M 0 1 * M 1 2%:R] j),
 1 |-> (\row_j [eta \0 with 
0 |-> - M 1 2%:R * M 0 2%:R, 1 |-> - M 0 1 ^+ 2 - M 1 2%:R ^+ 2, 2%:R |-> - M 0 1 * M 0 2%:R] j), 
 2%:R |-> (\row_j [eta \0 with 
0 |-> M 1 2%:R * M 0 1, 1 |-> - M 0 2%:R * M 0 1, 2%:R |-> - M 0 2%:R ^+ 2 - M 1 2%:R ^+ 2] j)] i.
Proof.
move=> a; apply/matrixP => i j.
rewrite !mxE /= sum3E /a.
case: ifPn => [/eqP ->|]; first rewrite [in RHS]mxE.
  case: ifPn => [/eqP ->|].
    rewrite anti_diag // mulr0 add0r {2}(eqP a) 2!mxE mulrN -expr2; congr (_ + _).
    by rewrite {2}(eqP a) !mxE mulrN -expr2.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !anti_diag //; simp => //=.
  by rewrite {2}(eqP a) 2!mxE mulrN mulrC.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !mxE.  
  case: ifPn => [/eqP ->|].
    rewrite !anti_diag //; simp => /=; by rewrite {2}(eqP a) 2!mxE mulrN.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !anti_diag //; simp => //=.
    rewrite {1}(eqP a) 2!mxE mulNr -expr2; congr (_ + _).
    by rewrite {2}(eqP a) 2!mxE mulrN -expr2.
    by rewrite {1}(eqP a) 2!mxE mulNr.
case: ifPn => [/eqP ->|].
  rewrite !anti_diag //; simp => /=.
  by rewrite {1}(eqP a) 2!mxE {2}(eqP a) 2!mxE mulrN mulNr opprK.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !anti_diag //; simp => //=.
  by rewrite {1}(eqP a) 2!mxE mulNr.
rewrite {1}(eqP a) 2!mxE mulNr -expr2; congr (_ + _).
by rewrite {1}(eqP a) 2!mxE mulNr -expr2.
Qed.

Lemma sqr_skewE (u : 'rV[R]_3) : let a := skew_mx u in 
  a ^+ 2 = \matrix_i [eta \0 with 0 |-> (\row_j [eta \0 with 
0 |-> - u 0 2%:R ^+ 2 - u 0 1 ^+ 2, 1 |-> u 0 0 * u 0 1, 2%:R |-> u 0 0 * u 0 2%:R] j),
 1 |-> (\row_j [eta \0 with 
0 |-> u 0 0 * u 0 1, 1 |-> - u 0 2%:R ^+ 2 - u 0 0 ^+ 2, 2%:R |-> u 0 1 * u 0 2%:R] j), 
 2%:R |-> (\row_j [eta \0 with 
0 |-> u 0 0 * u 0 2%:R, 1 |-> u 0 1 * u 0 2%:R, 2%:R |-> - u 0 1%:R ^+ 2 - u 0 0 ^+ 2] j)] i.
Proof.
move=> a; rewrite (sqr_antip (anti_skew u)); apply/matrixP => i j.
rewrite [in LHS]mxE [in RHS]mxE /=.
case: ifPn => [_|]; first rewrite 2!mxE.
  case: ifPn => [_|]; first by rewrite !skewij; simp; rewrite sqrrN.
  case: ifPn => [_|]; first by rewrite !skewij; simp.
  case: ifPn => [_|//]; by rewrite !skewij mulrN mulNr opprK mulrC.
case: ifPn => [_|]; first rewrite 2!mxE.
  case: ifPn => [_|]; first by rewrite !skewij opprK.
  case: ifPn => [_|]; first by rewrite !skewij 2!sqrrN.
  case: ifPn => [_|//]; by rewrite !skewij opprK mulrC.
case: ifPn => [_|//]; first rewrite 2!mxE.
case: ifPn => [_|]; first by rewrite !skewij mulrN mulNr opprK.
case: ifPn => [_|]; first by rewrite !skewij mulrN mulNr opprK.
case: ifPn => [_|//]; by rewrite !skewij sqrrN.
Qed.

Lemma sym_sqr_skew u : skew_mx u ^+ 2 \is sym 3 R.
Proof.
rewrite sqr_skewE /sym; apply/eqP/matrixP => i j; rewrite !mxE /=.
case: ifPn => [i0|].
  rewrite !mxE /=.
  case: ifPn => [j0|]; first by rewrite !mxE /= i0.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE i0.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite !mxE /=.
  case: ifPn => [j0|]; first by rewrite !mxE.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE.
rewrite !mxE.
  case: ifPn => [j0|]; first by rewrite !mxE.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE.
Qed.

Lemma mul_tr_vecij (u : 'rV[R]_3) i j : (u^T *m u) i j = u 0 i * u 0 j.
Proof.
by rewrite mxE (bigD1 ord0) //= big1 ?mxE ?addr0 // => i0; rewrite (ord1 i0).
Qed.

Lemma sqr_skew u : skew_mx u ^+ 2 = u^T *m u - (norm u ^+ 2)%:A.
Proof.
apply (symP (sym_sqr_skew u)); last move=> i j.
  rewrite rpredD //; last by rewrite rpredN sym_scaler_closed // sym1.
  by rewrite mul_tr_vec_sym.
rewrite [in X in _ -> _ = X]mxE mul_tr_vecij.
case/boolP : (i == 0) => [/eqP -> _|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite sqr_skewE 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE 
      sum3E -!expr2 -addrA addrCA addrAC -addrA.
  rewrite ifnot0 => /orP [] /eqP ->; by rewrite sqr_skewE 5!mxE /= mulr0 subr0.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP -> //|].
  rewrite ifnot0 => /orP [] /eqP -> _.
    rewrite sqr_skewE 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE 
      sum3E -!expr2 addrAC.
    by rewrite sqr_skewE 5!mxE /= mulr0 subr0.
case/boolP : (j == 0) => [/eqP -> //|].
rewrite ifnot0 => /orP [] /eqP -> // _.
rewrite sqr_skewE 5!mxE /= -expr2 mulr1; apply/eqP.
by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE sum3E -!expr2.
Qed.

Lemma cube_skew (u : 'rV[R]_3) : let a := skew_mx u in a ^+ 3 = - (norm u) ^+ 2 *: a.
Proof.
move=> a.
rewrite exprS sqr_skewE.
apply/matrixP => i j.
rewrite mxE /= sum3E.
do 6 rewrite mxE /=.
move: (dotmulvv u).
rewrite dotmulE sum3E => /eqP H.
rewrite -{1}eqr_opp 2!opprD -!expr2 in H.
move: (H); rewrite subr_eq addrC => /eqP ->.
move: (H); rewrite addrAC subr_eq addrC => /eqP ->.
move: (H); rewrite -addrA addrC subr_eq addrC => /eqP ->.
rewrite [in RHS]mxE.
case/boolP : (i == 0) => [/eqP -> |].
  case: ifPn => [/eqP ->|].
    rewrite /a !skewij; simp => /=.
    by rewrite addrC !mulNr mulrAC -mulrA mulrC subrr.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a !skewij; simp => /=.
    rewrite -expr2 -mulrN mulrC -mulrDl; congr (_ * _).
    by rewrite opprD opprK subrK.
  rewrite -(mulrC (u 0 1)) -mulrA -mulrDr -mulNr mulrC; congr (_ * _).
  by rewrite addrC mulNr addrK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case: ifPn => [/eqP ->|].
    rewrite /a !skewij; simp => /=.
    rewrite mulrC -mulrDl -[in RHS]mulNr; congr (_ * _).
    by rewrite mulNr -expr2 addrK.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a !skewij; simp => /=.
    by rewrite -mulrA mulrC 2!mulNr -mulrBl subrr mul0r.
  rewrite -mulrA mulrC -mulrA -mulrBr mulrC; congr (_ * _).
  by rewrite opprD opprK addrCA -expr2 subrr addr0.
case: ifPn => [/eqP ->|].
  rewrite /a !skewij; simp => /=.
  rewrite -mulrN mulrC -mulrDl; congr (_ * _).
  by rewrite opprD opprK -expr2 subrK.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a !skewij; simp => /=.
  rewrite -mulrA mulrCA -mulrDr -[in RHS]mulNr [in RHS]mulrC; congr (_ * _).
  by rewrite addrC mulNr -expr2 addrK.
by rewrite -mulrA mulrCA -mulrA -mulrDr addrC mulNr subrr mulr0.
Qed.

Lemma skew_mx4 w : norm w = 1 -> skew_mx w ^+ 4 = - skew_mx w ^+ 2.
Proof. move=> w1; by rewrite exprS cube_skew // w1 expr1n scaleN1r mulrN -expr2. Qed.

Lemma mxtrace_sqr_skew_mx u : \tr ((skew_mx u) ^+ 2) = - (2%:R * (norm u) ^+ 2).
Proof.
rewrite /mxtrace sum3E sqr_skewE.
do 6 rewrite mxE /=.
rewrite -opprB opprK !addrA addrC !addrA -2!addrA.
rewrite [in RHS]mulr2n [in RHS]mulrDl [in RHS]opprD mul1r; congr (_ + _).
  rewrite -opprB opprK; congr (- _).
  by rewrite addrC addrA -dotmulvv dotmulE sum3E -!expr2.
rewrite -opprB -opprD opprK; congr (- _).
by rewrite addrC -addrA addrCA addrA  -dotmulvv dotmulE sum3E -!expr2.
Qed.


(* TODO: move? *)
Lemma row'0_triple_prod_mat tmp (XM : 'M[{poly R}]_3) :
  row' ord0 (triple_prod_mat tmp (row 1 XM) (row 2%:R XM)) = row' ord0 XM.
Proof.
rewrite row'_triple_prod_mat /=.
apply/matrixP => i j; rewrite !mxE.
case: ifPn => [/eqP ->|].
  by rewrite !mxE; simp_ord.
case: i => [] [] // [] // i _ /=.
by rewrite !mxE; simp_ord.
Qed.

(* TODO: move? *)
Lemma diag_sqr {n} (M : 'M[R]_n) (i : 'I_n) : (M *m M) i i = (row i M) *d (col i M)^T.
Proof.
rewrite mxE dotmulE; apply/eq_bigr => /= j _; by rewrite 3!mxE.
Qed.

Lemma tr_sqr (M : 'M[R]_3) : \tr (M^+2) = \sum_(i < 3) (row i M) *d (col i M)^T.
Proof. apply/eq_bigr => i _; by rewrite diag_sqr. Qed.

Lemma tr_sqr3 (M : 'M[R]_3) : \tr (M *m M) =
  \sum_i (M i i ^+2) + M 0 1 * M 1 0 *+ 2 + M 0 2%:R * M 2%:R 0 *+ 2 +
  M 1 2%:R * M 2%:R 1 *+ 2.
Proof.
rewrite sum3E tr_sqr sum3E !dotmulE !sum3E !mxE -!expr2 -!addrA; congr (_ + _).
do 3 rewrite addrC -!addrA; congr (_ + _).
do 3 rewrite addrC -!addrA; congr (_ + _).
congr (_ + _).
rewrite addrC -!addrA mulrC; congr (_ + _).
rewrite addrC -!addrA mulrC; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite mulrC.
Qed.

Lemma sqr_tr3 (M : 'M[R]_3) : (\tr M) ^+ 2 =
  \sum_i (M i i ^+2) + M 0 0 * M 1 1 *+ 2 + (M 0 0 + M 1 1) * M 2%:R 2%:R *+ 2.  
Proof.
rewrite /mxtrace sum3E 2!sqrrD sum3E .
rewrite -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
Qed.

(* TODO: move? *)
Lemma char_poly3_coef1 (M : 'M[R]_3) :
  let Z := 1 / 2%:R * (\tr M ^+ 2 - \tr (M ^+ 2)) in
  (char_poly M)`_1 = Z.
Proof.
move=> Z.
rewrite /char_poly /char_poly_mx det_mx33 !mxE mulr1n mulr0n !add0r.
rewrite !mulNr !mulrN !opprK.
rewrite !coefD.
(* 1 *)
rewrite [X in X + _ + _](_ : _ = M 0 0 * (M 2%:R 2%:R + M 1 1) +
   (M 1 1 * M 2%:R 2%:R - M 2%:R 1 * M 1 2%:R)); last first.
  rewrite coefM sum2E coefD coefX add0r coefN coefC [- _]/=.
  rewrite subn0 coefD.
  rewrite coefM sum2E subn0 coefD coefX add0r coefN (_ : _`_0 = M 1 1); last by rewrite coefC.
  rewrite coefD coefX coefN coefC subr0 mulr1.
  rewrite coefD coefN coefX coefN coefC subr0 mul1r.
  rewrite subnn coefD coefX add0r coefN coefC [in X in - M 1 1 - X]/=.
  rewrite coefM sum2E coefC coefC mulr0 add0r coefC mul0r subr0.
  rewrite coefD coefX coefN coefC subr0 mul1r.
  rewrite coefD coefM sum1E coefD coefX add0r coefN coefC [in X in - X * _`_ _]/=.
  rewrite coefD coefX add0r coefN coefC mulrN !mulNr opprK.
  rewrite coefN coefM sum1E coefC coefC [in X in M 1 1 * _ - X]/=.
  by rewrite -opprB mulrN 2!opprK.
rewrite [X in _ + X + _](_ : _ = - M 0 1 * M 1 0); last first.
  rewrite coefN coefM sum2E coefC [in X in X * _]/= subnn.
  rewrite coefD subn0 coefM sum2E.
  rewrite subn0 subnn coefC coefC mulr0 add0r.
  rewrite coefC mul0r add0r.
  rewrite coefM sum2E subn0 subnn coefC coefD coefX coefN coefC subr0 mulr1.
  rewrite coefC mul0r addr0 coefC mul0r addr0.
  by rewrite mulNr.
rewrite [X in _ + _ + X](_ : _ = - M 0 2%:R * M 2%:R 0); last first.
  rewrite coefN coefM sum2E subn0 subnn coefC.
  rewrite [in X in X * _]/=.
  rewrite coefD coefM sum2E subn0 coefC coefC mulr0 add0r.
  rewrite coefC mul0r add0r coefM sum2E subn0 subnn coefC [in X in X * _`_1]/=.
  by rewrite coefD coefX coefN coefC subr0 mulr1 coefC mul0r addr0 coefC mul0r addr0 mulNr.
rewrite /Z.
apply/(@mulrI _ 2%:R); first exact: pnatr_is_a_unit.
rewrite mulrA div1r divrr ?pnatr_is_a_unit // mul1r.
rewrite sqr_tr3.
rewrite tr_sqr3.
rewrite 3!opprD -[in RHS]addrAC [in RHS](addrC (\sum_ _ _)) 3![in RHS]addrA addrK.

rewrite mulrDr addrC mulNr mulrN (mulrC 2%:R) mulr_natr.
rewrite -2![in RHS]addrA [in RHS]addrC -[in RHS]addrA; congr (_ + _).
rewrite mulrDr addrC mulNr mulrN (mulrC 2%:R) mulr_natr.
rewrite [in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite addrA mulrDr addrC mulrN (mulrC 2%:R) mulr_natr mulrC -addrA; congr (_ + _).
rewrite (mulrC 2%:R) mulr_natr.
rewrite mulrDr.
rewrite mulrDl.
rewrite mulr2n.
rewrite [in RHS]mulr2n.
rewrite [in X in _ = _ + X]mulr2n.
rewrite -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + (_ + _)).
by rewrite addrCA.
Qed.

Lemma char_poly3 (M : 'M[R]_3) :
  let Z := 1 / 2%:R * ((\tr M) ^+ 2 - \tr (M ^+ 2)) in
  char_poly M = 'X^3 - (\tr M) *: 'X^2 + Z *: 'X - (\det M)%:P.
Proof.
move=> Z.
rewrite -(coefK (char_poly M)) (size_char_poly M).
apply/polyP.
case. (* coef0 *)
  rewrite coef_poly char_poly_det !coef_add_poly !coef_opp_poly !coefZ.
  rewrite !coefX !coefXn add0r mulr0 oppr0 mulr0 add0r add0r coefC /=.
  by rewrite exprS sqrrN expr1n mulr1 mulN1r.
case; last first.
  case. (* coef2 *)
    rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
    by rewrite add0r mulr0 mulr1 addr0 coefC subr0 char_poly_trace.
  case; last first. (* coef n >= 4 *)
    move=> n.
    rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
    by rewrite add0r mulr0 mulr0 coefC subr0 addr0 oppr0.
  (* coef3 *)
  rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
  rewrite mulr0 subr0 mulr0 addr0 coefC subr0; apply/eqP.
  rewrite (_ : _`_3 = lead_coef (char_poly M)); last first.
    by rewrite lead_coefE size_char_poly.
  by rewrite -monicE char_poly_monic.
(* coef1 *)
rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
rewrite add0r mulr1 mulr0 oppr0 add0r coefC subr0.
suff : (char_poly M)`_1 = Z by move=> ->.
by rewrite char_poly3_coef1.
Qed.

Lemma char_poly_skew_mx (u : 'rV[R]_3) : norm u = 1 -> 
  char_poly (skew_mx u) = 'X^3 + 'X.
Proof.
move=> u1.
rewrite char_poly3 det_skew_mx subr0 trace_anti ?anti_skew //.
rewrite scale0r subr0 expr0n add0r mulrN mxtrace_sqr_skew_mx mulrN opprK.
by rewrite u1 expr1n mulr1 div1r mulVr ?unitfE ?pnatr_eq0 // scale1r.
Qed.

Definition skew_mx_eigenvalues : seq R[i] := [:: 0; 'i; 0 -i* 1].

Ltac eigenvalue_skew_mx_eval_poly := 
  rewrite /map_poly horner_poly size_addl; [ |by rewrite size_polyXn size_polyX] ;
  rewrite size_polyXn sum4E !coefD !coefXn !coefX !add0r !mul0r !mul1r !add0r !addr0 mul1r.

Lemma eigenvalue_skew_mx (u : 'rV[R]_3) : norm u = 1 -> 
  eigenvalue (map_mx (fun x => x%:C) (skew_mx u)) =1 [pred k | k \in skew_mx_eigenvalues].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly (char_poly_skew_mx u1).
apply/rootP.
case: ifPn => [|Hk].
  rewrite inE => /orP [/eqP ->|]; first by rewrite /= horner_map !hornerE.
  rewrite inE => /orP [/eqP ->|].
    eigenvalue_skew_mx_eval_poly.
    by rewrite expr1 exprS sqr_i mulrN1 subrr.
  rewrite inE => /eqP ->.
  eigenvalue_skew_mx_eval_poly.
  apply/eqP. simpc. by rewrite addrC subrr eq_complex /= eqxx.
apply/eqP; apply: contra Hk.
eigenvalue_skew_mx_eval_poly.
rewrite (exprS _ 2) -{1}(mulr1 k) -mulrDr mulf_eq0 => /orP [/eqP ->|].
  by rewrite inE eqxx.
rewrite eq_sym addrC -subr_eq add0r -sqr_i eqf_sqr => /orP [/eqP <-|].
  by rewrite !inE eqxx orbC.
rewrite -eqr_oppLR => /eqP <-.
rewrite !inE orbA; apply/orP; right.
by rewrite eq_complex /= oppr0 !eqxx.
Qed.

End skew.

Section exponential_map.

Variable R : rcfType.

Definition exp_mx (phi : angle R) (w : 'M[R]_3) : 'M_3 :=
  1 + sin phi *: w + (1 - cos phi) *: w ^+ 2.

Lemma mul_exp_mx (a b : angle R) u : u ^+ 3 = - u ->
  exp_mx a u * exp_mx b u = exp_mx (a + b) u.
Proof.
move=> cube_u.
rewrite /exp_mx sinD cosD !mulrDr !mulrDl. 
simp => /=.
rewrite -scalerCA -2!scalerAl -expr2.
rewrite -scalerAl -scalerAr -exprSr cube_u (scalerN (sin b) u) (scalerN (1 - cos a)).
rewrite -(scalerAl (sin a)) -(scalerCA (1 - cos b) u) -(scalerAl (1 - cos b)) -exprS.
rewrite cube_u (scalerN _ u) (scalerN (sin a) (_ *: _)).
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
rewrite (_ : u ^+ 4 = - u ^+ 2); last by rewrite exprS cube_u mulrN -expr2.
rewrite 2!scalerN scalerA.
rewrite addrC -scaleNr -2!scalerDl -scalerBl; congr (_ *: _).
rewrite -!addrA; congr (_ + _).
rewrite mulrBr mulr1 mulrBl mul1r opprB opprB !addrA subrK addrC.
rewrite -(addrC (cos a)) !addrA -(addrC (cos a)) subrr add0r.
by rewrite addrC addrA subrr add0r mulrC.
Qed.

Lemma tr_exp_mx phi M : (exp_mx phi M)^T = exp_mx phi M^T.
Proof.
by rewrite /exp_mx !linearD /= !linearZ /= trmx1 expr2 trmx_mul expr2.
Qed.

Lemma inv_exp_mx phi M : M ^+ 4 = - M ^+ 2 -> exp_mx phi M * exp_mx phi (- M) = 1.
Proof.
move=> aM.
case/boolP : (cos phi == 1) => [/eqP cphi|cphi].
  by rewrite /exp_mx cphi subrr 2!scale0r !addr0 scalerN (cos1sin0 cphi) scale0r addr0 subr0 mulr1.
rewrite /exp_mx !mulrDr !mulrDl !mulr1 !mul1r -[RHS]addr0 -!addrA; congr (_ + _).
rewrite !addrA (_ : (- M) ^+ 2 = M ^+ 2); last by rewrite expr2 mulNr mulrN opprK -expr2.
rewrite -!addrA (addrCA (_ *: M ^+ 2)) !addrA scalerN subrr add0r.
rewrite (_ : (1 - _) *: _ * _ = - (sin phi *: M * ((1 - cos phi) *: M ^+ 2))); last first.
  rewrite mulrN; congr (- _).
  rewrite -2!scalerAr -!scalerAl -exprS -exprSr 2!scalerA; congr (_ *: _).
  by rewrite mulrC.
rewrite -!addrA (addrCA (- (sin phi *: _ * _))) !addrA subrK.
rewrite mulrN -scalerAr -scalerAl -expr2 scalerA -expr2.
rewrite -[in X in _ - _ + _ + X = _]scalerAr -scalerAl -exprD scalerA -expr2.
rewrite -scalerBl -scalerDl.
move: (cos2Dsin2 phi) => /eqP; rewrite eq_sym addrC -subr_eq => /eqP <-.
rewrite -{2}(expr1n _ 2) subr_sqr -{1 3}(mulr1 (1 - cos phi)) -mulrBr -mulrDr.
rewrite opprD addrA subrr add0r -(addrC 1) -expr2 -scalerDr.
apply/eqP; rewrite scaler_eq0 sqrf_eq0 subr_eq0 eq_sym (negbTE cphi) /=.
by rewrite aM subrr.
Qed.

Lemma trace_exp_mx_skew_mx (phi : angle R) w : norm w = 1 ->
  \tr (exp_mx phi (skew_mx w)) = 1 + 2%:R * cos phi.
Proof.
move=> w1.
rewrite 2!mxtraceD !mxtraceZ /= mxtrace1.
rewrite (trace_anti (anti_skew _)) mulr0 addr0 mxtrace_sqr_skew_mx w1.
rewrite (_ : - _ = - 2%:R); last by rewrite expr1n mulr1.
by rewrite mulrDl addrA mul1r -natrB // mulrC mulrN -mulNr opprK.
Qed.

(* see table 1.1 of handbook of robotics *)
Lemma exp_mx_skew_mxE phi (w : 'rV[R]_3) : norm w = 1 ->
  let va := 1 - cos phi in let ca := cos phi in let sa := sin phi in
  exp_mx phi (skew_mx w) = triple_prod_mat
  (\row_k [eta \0 with 0 |-> w 0 0 ^+2 * va + ca, 
                       1 |-> w 0 0 * w 0 1 * va - w 0 2%:R * sa, 
                       2%:R |-> w 0 0 * w 0 2%:R * va + w 0 1 * sa] k)
  (\row_k [eta \0 with 0 |-> w 0 0 * w 0 1 * va + w 0 2%:R * sa, 
                       1 |-> w 0 1 ^+2 * va + ca, 
                       2%:R |-> w 0 1 * w 0 2%:R * va - w 0 0 * sa] k)
  (\row_k [eta \0 with 0 |-> w 0 0 * w 0 2%:R * va - w 0 1 * sa, 
                       1 |-> w 0 1 * w 0 2%:R * va + w 0 0 * sa, 
                       2%:R |-> w 0 2%:R ^+2 * va + ca] k).
Proof.
move=> w1 va ca sa.
apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    rewrite sqr_skewE !mxE /=.
    rewrite (_ : - _ - _ = w 0 0 ^+ 2 - 1); last first.
      rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
      by rewrite !opprD !addrA subrr add0r addrC.
    rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
    by rewrite /va opprB addrC subrK.
  rewrite ifnot0 => /orP [] /eqP ->.
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
  rewrite ifnot0 => /orP [] /eqP ->.
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    rewrite sqr_skewE !mxE /=.
    rewrite (_ : - _ - _ = w 0 1 ^+ 2 - 1); last first.
      rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
      by rewrite 2!opprD addrCA addrA subrK addrC.
    rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
    by rewrite /va opprB addrC subrK.
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
case/boolP : (j == 0) => [/eqP ->|].
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
rewrite ifnot0 => /orP [] /eqP ->.
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
rewrite sqr_skewE !mxE /=.
rewrite (_ : - _ - _ = w 0 2%:R ^+ 2 - 1); last first.
  rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
  by rewrite 2!opprD [in RHS]addrC subrK addrC.
rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
by rewrite /va opprB addrC subrK.
Qed.

Definition exp_skew_mx_eigenvalues (phi : angle R) : seq R[i] := 
  [:: 1; expi phi; expi (- phi)].

Lemma exp_mx_is_ortho (a : angle R) (w : 'rV_3) : norm w = 1 ->
  exp_mx a (skew_mx w) \is 'O_3[R].
Proof.
move=> w1.
rewrite orthogonalE tr_exp_mx.
move: (anti_skew w); rewrite antiE -eqr_oppLR => /eqP <-.
by rewrite inv_exp_mx // skew_mx4. 
Qed.

Lemma rank_exp_mx (a : angle R) (w : 'rV_3) : norm w = 1 ->
  \rank (exp_mx a (skew_mx w)) = 3.
Proof.
move=> w1; by rewrite mxrank_unit // orthogonal_unit // exp_mx_is_ortho.
Qed.

Lemma det_exp_mx0 w : norm w = 1 -> \det (exp_mx 0 (skew_mx w)) = 1.
Proof. move=> w1; by rewrite /exp_mx sin0 cos0 subrr 2!scale0r 2!addr0 det1. Qed.

Lemma det_exp_mx (phi : angle R) w : norm w = 1 -> 
  \det (exp_mx phi (skew_mx w)) = 1.
Proof.
move=> w1.
move: (exp_mx_is_ortho (half_angle phi) w1).
move/orthogonal_det/eqP.
rewrite -(@eqr_expn2 _ 2%N) // expr1n norm2 expr2 -det_mulmx.
rewrite mulmxE mul_exp_mx; last by rewrite cube_skew w1 expr1n scaleN1r.
move/eqP; by rewrite halfP.
Qed.

Lemma eigenvalue_exp_mx (a : angle R) (w : 'rV[R]_3) : norm w = 1 ->
  eigenvalue (map_mx (fun x => x%:C) (exp_mx a (skew_mx w))) =1 
    [pred k | k \in exp_skew_mx_eigenvalues a].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly.
Abort.

Lemma trace_sqr_exp_mx_skew_mx (phi : angle R) w : norm w = 1 ->
  \tr (exp_mx phi (skew_mx w) ^+ 2) = - (1 + 2%:R * cos phi) ^+ 2(*?*).
Proof.
move=> w1.
Abort.

End exponential_map.

Section Rodrigues.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Record angle_axis := AngleAxis {
  angle_axis_val : angle R * vector ;
  _ : norm (angle_axis_val.2) == 1
 }.

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

Lemma aaxis_of1 (a : angle R) (v : vector) : norm v = 1 ->
  aaxis (angle_axis_of a v) = v.
Proof.
move=> v1; rewrite aaxis_of; last by rewrite -norm_eq0 v1 oner_neq0.
by rewrite v1 invr1 scale1r.
Qed.

Lemma aangle_of (a : angle R) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

Coercion rodrigues_mx r := 
  let (phi, w) := (aangle r, aaxis r) in exp_mx phi (skew_mx w).

Definition rodrigues (x : vector) r := 
  let (phi, w) := (aangle r, aaxis r) in
  cos phi *: x + (1 - cos phi) * (x *d w) *: w + sin phi *: (x *v w).

Lemma rodriguesP u r : rodrigues u r = u *m r.
Proof.
rewrite /rodrigues; set phi := aangle _; set w := aaxis _.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE.
rewrite [in X in _ = _ + _ + X]crossmulC scalerN.
rewrite double_crossmul dotmulvv norm_axis [_ ^+ _]expr1n scale1r.
rewrite [in X in _ = _ + _ + X]dotmulC scalerBr opprB.
rewrite scalerA [in RHS](addrC (_ *: w)) [in RHS]addrA; congr (_ + _).
rewrite scalerDl opprD scaleNr opprK addrC addrA scale1r; congr (_ + _).
by rewrite addrAC subrr add0r.
Qed.

Lemma trace_rodrigues r : \tr (rodrigues_mx r) = 1 + 2%:R * cos (aangle r).
Proof. by rewrite trace_exp_mx_skew_mx // norm_axis. Qed.

Lemma rodrigues_mx_is_O r : norm (aaxis r) = 1 -> rodrigues_mx r \in 'O_3[R].
Proof.
move=> axis1.
rewrite /rodrigues_mx orthogonalE tr_exp_mx {2}(eqP (anti_skew _)) linearN /= trmxK.
by rewrite inv_exp_mx // skew_mx4.
Qed.

Lemma det_rodrigues_mx r : norm (aaxis r) = 1 -> \det (rodrigues_mx r) = 1.
Proof.
move=> ?; by rewrite /rodrigues_mx det_exp_mx.
Qed.

(* see table 1.2 of handbook of robotics *)
Definition angle_of_rotation (M : 'M[R]_3) := acos ((\tr M - 1) / 2%:R).
Definition axis_of_rotation (M : 'M[R]_3) : 'rV[R]_3 := 
  let phi := angle_of_rotation M in 
  (1 / (2%:R * sin phi) *: \row_i [eta \0 with 
    0 |-> M 2%:R 1 - M 1 2%:R, 1 |-> M 0 2%:R - M 2%:R 0, 2%:R |-> M 1 0 - M 0 1] i).
Definition angle_axis_of_rotation (M : 'M[R]_3) :=
  angle_axis_of (angle_of_rotation M) (axis_of_rotation M).

Definition log_mx (M : 'M[R]_3) : angle R * 'rV[R]_3 :=
  (angle_of_rotation M, axis_of_rotation M).

Lemma log_exp_mx (phi : angle R) (w : 'rV[R]_3) : 
  sin phi != 0 -> phi \in Opi_closed R -> norm w = 1 ->
  log_mx (exp_mx phi (skew_mx w)) = (phi, w).
Proof.
move=> sphi phiOpi w1 [:Hphi].
congr pair.
  abstract: Hphi.
  rewrite /angle_of_rotation trace_exp_mx_skew_mx // addrAC subrr add0r.
  by rewrite mulrC mulrA mulVr ?mul1r ?cosK // unitfE pnatr_eq0.
apply/rowP => i.
rewrite 2!mxE /= Hphi => [:twosphi].
case: ifPn => [/eqP ->|].
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r.
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r opprD addrAC addrA subrK.
  rewrite mulrN opprK -mulr2n -(mulr_natl (_ * _) 2).
  rewrite (mulrA 2%:R) div1r mulrCA mulrA divrr ?mul1r ?mxE //.
  abstract: twosphi.
  by rewrite unitfE mulf_neq0 // ?pnatr_eq0.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r.
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r opprD addrAC addrA subrK.
  rewrite mulrN opprK -mulr2n -(mulr_natl (_ * _) 2).
  by rewrite (mulrA 2%:R) div1r mulrCA mulrA divrr ?mul1r ?mxE.
rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r.
rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r opprD addrAC addrA subrK.
rewrite mulrN opprK -mulr2n -(mulr_natl (_ * _) 2).
by rewrite (mulrA 2%:R) div1r mulrCA mulrA divrr ?mul1r ?mxE.
Qed.

Definition unskew (M : 'M[R]_3) : 'rV[R]_3 :=
  \row_k [eta \0 with 0 |-> - M 1 2%:R, 1 |-> M 0 2%:R, 2%:R|-> - M 0 1] k.

Lemma unskew_skew u : unskew (skew_mx u) = u.
Proof.
apply/rowP => i; rewrite 3!mxE /=.
case: ifPn => [/eqP ->|]; first by rewrite crossmulE /= !mxE /=; simp => /=; rewrite subr0.
by rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !skewij // opprK.
Qed.

Lemma skew_unskew (M : 'M[R]_3) : M \is 'so_3[R] -> skew_mx (unskew M) = M.
Proof.
move=> soM.
rewrite /unskew.
apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite skewij anti_diag.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite skewij mxE //= opprK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite skewij mxE //= {1}(eqP soM) 2!mxE opprK.
  rewrite ifnot0 => /orP [] /eqP -> /=.
    by rewrite skewij anti_diag.
  by rewrite skewij mxE //= opprK.
case/boolP : (j == 0) => [/eqP ->|].
  by rewrite skewij mxE /= {1}(eqP soM) !mxE opprK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  by rewrite skewij !mxE /= {1}(eqP soM) !mxE opprK.
by rewrite skewij anti_diag.
Qed.

Lemma skew_mxZ k (u : 'rV[R]_3) : skew_mx (k *: u) = k *: skew_mx u.
Proof.
rewrite /skew_mx scalerN; congr (- _).
apply/matrixP => i j.
by rewrite mxE crossmulC linearZ /= -scalerN crossmulC opprK mxE 2![in RHS]mxE.
Qed.

Lemma unskew_mxZ k (M : 'M[R]_3) : unskew (k *: M) = k *: unskew M.
Proof.
apply/rowP => i; rewrite !mxE /=.
case: ifPn => [_|]; first by rewrite mulrN.
rewrite ifnot0 => /orP [] /eqP -> //=; by rewrite mulrN.
Qed.

Definition ln_mx (M : 'M[R]_3) : angle R * 'rV[R]_3 :=
  let phi := acos ((\tr M - 1) /2%:R) in
  (phi, 1 / (2%:R * sin phi) *: unskew (M - M^T)).

Lemma exp_ln M :
  let: (phi, w) := ln_mx M in
  sin phi != 0 ->
  exp_mx phi (skew_mx w) = M.
Proof.
move H : (ln_mx M) => h.
case: h => phi w in H *.
move=> sphi.
rewrite /exp_mx.
case : H => H1 H2.
rewrite -H2 H1 skew_mxZ.
rewrite (_ : 1 / (2%:R * sin phi) = (1 / sin phi) * (1 / 2 %:R)); last first.
  by rewrite invrM ?unitfE ?pnatr_eq0 // 2!mulrA mulr1.
rewrite -scalerA -skew_mxZ -unskew_mxZ.
rewrite skew_unskew; last by rewrite antip_is_so.
rewrite scalerA {1}div1r divrr ?unitfE // scale1r.
rewrite exprZn scalerA.
rewrite -/(antip M).
rewrite (_ : (1 - cos _) * _ = 2%:R / (\tr M + 1)); last first.
  admit. (* ok *)
apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite 3!mxE /= anti_diag ?addr0; last by rewrite antip_is_so.
    rewrite sqr_antip; last by rewrite antip_is_so.
    rewrite 3!mxE /=.
Abort.

Lemma rodriguesE M u (HM : M^T \in 'SO_3[R]) :
  norm (axis_of_rotation M) = 1 ->
  sin (angle_of_rotation M) != 0 (* to avoid singularity *) ->
  rodrigues u (angle_axis_of_rotation M) =
  homogeneous_ap u (Transform 0 HM).
Proof.
move=> norm1 sin0.
transitivity (u *m M); last first.
  (* TODO: lemma? *)
  rewrite homogeneous_apE /htrans_of_coordinate trmx_mul trmxK.
  rewrite (_ : (Transform 0 HM)^T = (hrot_of_transform (Transform 0 HM))^T); last first.
    by rewrite /hrot_of_transform /= /hmx /= trmx0.
  rewrite hcoor_hrot_of_transform /=.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  rewrite trmxK (@cast_row_mx _ _ _ _ _ _ (u *m M)) //.
  by rewrite row_mxKl /= castmx_id.
rewrite rodriguesP; congr (_ *m _).
rewrite /rodrigues_mx. set phi := aangle _. set w := aaxis _.

(*
rewrite /exp_mx.
rewrite -(exp_mx_log (M)).
rewrite /phi /w aangle_of.
rewrite aaxis_of1; last by done.
by rewrite /exp_mx.  
*)

rewrite exp_mx_skew_mxE; last by rewrite /w aaxis_of1.
have antiM : antip M = sin phi *: skew_mx w.
  apply/antiP.
  rewrite antip_is_so //.
  rewrite antip_scaler_closed // anti_skew //.
  move=> i j.
  case/boolP : (i == 0) => [/eqP ->|].
    case/boolP : (j == 0) => [/eqP -> //|].
    rewrite ifnot0 => /orP [] /eqP -> _.
      rewrite 5!mxE skewij /w aaxis_of1 // 2!mxE /= mulrA -mulrN opprB; congr (_ * _).
      rewrite mulrA -mulf_div [in RHS]mulrC mulrA [in RHS]div1r /phi.
      by rewrite aangle_of mulVr // unitfE.
    rewrite 5!mxE skewij /w aaxis_of1 // 2!mxE /= -mulrN opprK mulrA; congr (_ * _).
    rewrite mulrA -mulf_div [in RHS]mulrC mulrA [in RHS]div1r /phi.
    by rewrite aangle_of mulVr // unitfE.
  rewrite ifnot0 => /orP [] /eqP ->.
    case/boolP : (j == 0) => [/eqP ->//|].
    rewrite ifnot0 => /orP [] /eqP -> // _.
    rewrite 5!mxE skewij /w aaxis_of1 // 2!mxE /= -2!mulrN opprB mulrA; congr (_ * _).
    rewrite mulrA -mulf_div [in RHS]mulrC mulrA [in RHS]div1r /phi.
    by rewrite aangle_of mulVr // unitfE.
  by case: j => -[] // [] // [].
suff symM : symp M = 1 + (1 - cos phi) *: skew_mx w ^+ 2.
  rewrite (symp_antip M) antiM symM -exp_mx_skew_mxE; last by rewrite /w aaxis_of1.
  by rewrite /exp_mx addrAC.
rewrite sqr_skew {3}/w aaxis_of1 // norm1 expr1n.
rewrite scalerBl scale1r addrCA addrA scalemx1 subrK.
rewrite scalerBr opprB addrCA -{1}(scale1r (w^T *m w)) -scalerBl.
apply/symP.
  by rewrite sym_symp.
  rewrite rpredD //.
  by rewrite sym_scaler_closed // sym1.
  by rewrite sym_scaler_closed // mul_tr_vec_sym.
move=> i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> _|].
(*    rewrite ![in LHS]mxE /= 3!mxE /=.
    rewrite div1r -mulr2n -(mulr_natr (M 0 0) 2%N) -mulrCA mulVr ?unitfE ?pnatr_eq0 // mulr1.
    rewrite !mxE sum1E mxE -expr2 /w.
    rewrite aaxis_of1 // /axis_of_rotation /= !mxE /=.

    rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
    rewrite expr1n mxE mul_tr_vecij 3!mxE mulr1 -expr2.
    rewrite mulrBr mulr1 opprB addrC !addrA subrK.
apply/symP.
  by rewrite sym_symp.
  by rewrite rpredD // ?sym1 // sym_scaler_closed // sym_sqr_skew.
move=> i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> _|].
    rewrite ![in LHS]mxE /= 3!mxE /=.
    rewrite div1r -mulr2n -(mulr_natr (M 0 0) 2%N) -mulrCA mulVr ?unitfE ?pnatr_eq0 // mulr1.
    rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
    rewrite expr1n mxE mul_tr_vecij 3!mxE mulr1 -expr2.
    rewrite mulrBr mulr1 opprB addrC !addrA subrK.
    admit. (* M 0 0 *)
  rewrite ifnot0 => /orP [] /eqP -> _.
    rewrite ![in LHS]mxE /= 3!mxE /= add0r.
    rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
    rewrite expr1n mxE mul_tr_vecij 3!mxE mulr0 subr0.
    admit.
  rewrite ![in LHS]mxE /= 3!mxE /= add0r.
  rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
  rewrite expr1n mxE mul_tr_vecij 3!mxE mulr0 subr0.
  admit.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP -> //|].
  rewrite ifnot0 => /orP [] /eqP -> _.
    rewrite ![in LHS]mxE /= 3!mxE /=.
    rewrite -mulr2n -(mulr_natr (M 1 1) 2%N) -mulrCA div1r mulVr ?unitfE ?pnatr_eq0 // mulr1.
    rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
    rewrite expr1n mxE mul_tr_vecij 3!mxE mulr1 -expr2.
    rewrite mulrBr mulr1 opprB addrC !addrA subrK.
    admit. (* M 1 1 *)
  rewrite ![in LHS]mxE /= 3!mxE /= add0r.
  rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
  rewrite expr1n mxE mul_tr_vecij 3!mxE mulr0 subr0.
  admit.
case/boolP : (j == 0) => [/eqP -> //|].
rewrite ifnot0 => /orP [] /eqP -> _ //.
rewrite ![in LHS]mxE /= 3!mxE /=.
rewrite -mulr2n -(mulr_natr (M 2%:R 2%:R) 2%N) -mulrCA div1r mulVr ?unitfE ?pnatr_eq0 // mulr1.
rewrite sqr_skew (_ : norm w = 1); last by rewrite /w aaxis_of1.
rewrite expr1n mxE mul_tr_vecij 3!mxE mulr1 -expr2.
rewrite mulrBr mulr1 opprB addrC !addrA subrK.
admit.*)
Abort.

End Rodrigues.

Section quaternion.

Variable R : rcfType.

Record quat := mkQuat {quatl : R ; quatr : 'rV[R]_3 }.

Notation "x %:q" := (mkQuat x 0) (at level 2, format "x %:q").
Notation "x %:v" := (mkQuat 0 x) (at level 2, format "x %:v").
Notation "Q '_0'" := (quatl Q) (at level 1, format "Q '_0'").
Notation "Q '_i'" := ((quatr Q) 0 0) (at level 1, format "Q '_i'").
Notation "Q '_j'" := ((quatr Q) 0 1) (at level 1, format "Q '_j'").
Notation "Q '_k'" := ((quatr Q) 0 (2%:R : 'I_3)) (at level 1, format "Q '_k'").

Notation "'`i'" := (veci R)%:v.
Notation "'`j'" := (vecj R)%:v.
Notation "'`k'" := (veck R)%:v.

Local Notation "a *`i" := (mkQuat 0 (row3 a 0 0)) (at level 3).
Local Notation "a *`j" := (mkQuat 0 (row3 0 a 0)) (at level 3).
Local Notation "a *`k" := (mkQuat 0 (row3 0 0 a)) (at level 3).

Definition pair_of_quat (Q : quat) := let: mkQuat Q1 Q2 := Q in (Q1, Q2).
Definition quat_of_pair (Q : (R * 'rV[R]_3)%type) := let: (Q1, Q2) := Q in mkQuat Q1 Q2.

Lemma quat_of_pairK : cancel pair_of_quat quat_of_pair.
Proof. by case. Qed.

Definition quat_eqMixin := CanEqMixin quat_of_pairK.
Canonical Structure quat_eqType := EqType quat quat_eqMixin.
Definition quat_choiceMixin := CanChoiceMixin quat_of_pairK.
Canonical Structure quat_choiceType := ChoiceType quat quat_choiceMixin.

Lemma eq_quat (a b : quat) :
  (a == b) = [&& (a _0 == b _0), (a _i == b _i), (a _j == b _j) & (a _k == b _k)].
Proof.
case: a b => [a0 a1] [b0 b1] /=.
apply/idP/idP => [/eqP [-> ->]|/and3P [/eqP -> /eqP H1 /andP[/eqP H2 /eqP H3]]].
  by rewrite !eqxx.
apply/eqP; congr mkQuat; apply/rowP => i.
case/boolP : (i == 0) => [/eqP -> //|].
by rewrite ifnot0 => /orP [] /eqP ->.
Qed.

Definition addq (Q P : quat) := mkQuat (Q _0 + P _0) (quatr Q + quatr P).

Lemma addqC : commutative addq.
Proof. move=> Q P; congr mkQuat; by rewrite addrC. Qed. 

Lemma addqA : associative addq.
Proof. move=> Q1 Q2 Q3; congr mkQuat; by rewrite addrA. Qed.

Lemma add0q : left_id 0%:q addq.
Proof. case=> Q1 Q2; by rewrite /addq /= 2!add0r. Qed.

Definition oppq (Q : quat) := mkQuat (- Q _0) (- quatr Q).

Lemma addNq : left_inverse 0%:q oppq addq.
Proof. move=> Q; congr mkQuat; by rewrite addNr. Qed.

Definition quat_ZmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical quat_ZmodType := ZmodType quat quat_ZmodMixin.

Lemma quatE Q : Q = (Q _0)%:q + Q _i *`i + Q _j *`j + Q _k *`k.
Proof.
apply/eqP; rewrite eq_quat /=.
simp => /=.
rewrite eqxx /= !mxE /=.
simp => /=.
by rewrite !eqxx.
Qed.

Lemma oppqE a : oppq a = - a. Proof. done. Qed.

Lemma quat_real0 x : (x%:q == 0) = (x == 0).
Proof. apply/idP/idP => /eqP; by [case=> -> | move=> ->]. Qed.

Definition mulq (Q P : quat) :=
  let Q1 := Q _0 in let P1 := P _0 in
  let Q2 := quatr Q in let P2 := quatr P in
  mkQuat (Q1 * P1 - Q2 *d P2) (Q1 *: P2 + P1 *: Q2 + Q2 *v P2).

Lemma mulqA : associative mulq.
Proof.
move=> [a a'] [b b'] [c c']; congr mkQuat => /=.
- rewrite mulrDr mulrDl mulrA -!addrA; congr (_ + _).
  rewrite mulrN !dotmulDr !dotmulDl !opprD !addrA dotmul_crossmulA; congr (_ + _).
  rewrite addrC addrA; congr (_ + _ + _).
  by rewrite mulrC dotmulvZ mulrN.
  by rewrite dotmulZv.
  by rewrite dotmulvZ dotmulZv.
- rewrite 2![in LHS]scalerDr 1![in RHS]scalerDl scalerA.
  rewrite -4![in LHS]addrA -3![in RHS]addrA; congr (_ + _).
  rewrite [in RHS]scalerDr [in RHS]addrCA -[in RHS]addrA -[in LHS]addrA; congr (_ + _).
    by rewrite scalerA mulrC -scalerA.
  rewrite [in RHS]scalerDr [in LHS]scalerDl [in LHS]addrCA -[in RHS]addrA -addrA; congr (_ + _).
    by rewrite scalerA mulrC.
  rewrite (addrC (a *: _)) linearD /= (addrC (a' *v _)) linearD /=.
  rewrite -![in LHS]addrA ![in LHS]addrA (addrC (- _ *: a')) -![in LHS]addrA; congr (_ + _).
    by rewrite linearZ.
  rewrite [in RHS]crossmulC linearD /= opprD [in RHS]addrCA ![in LHS]addrA addrC -[in LHS]addrA.
  congr (_ + _); first by rewrite linearZ /= crossmulC scalerN.
  rewrite addrA addrC linearD /= opprD [in RHS]addrCA; congr (_ + _).
    by rewrite !linearZ /= crossmulC.
  rewrite 2!double_crossmul opprD opprK [in RHS]addrC addrA; congr (_ + _); last first.
    by rewrite scaleNr.
  by rewrite dotmulC scaleNr; congr (_ + _); rewrite dotmulC.
Qed.

Lemma mul1q : left_id 1%:q mulq.
Proof.
case=> a a'; rewrite /mulq /=; congr mkQuat; simp => /=.
  by rewrite dotmul0v subr0.
by rewrite crossmul0v scaler0 scale1r 2!addr0.
Qed.

Lemma mulq1 : right_id 1%:q mulq.
Proof.
case=> a a'; rewrite /mulq /=; congr mkQuat; simp => /=.
  by rewrite dotmulv0 subr0.
by rewrite scaler0 scale1r crossmulv0 add0r addr0.
Qed.

Lemma mulqDl : left_distributive mulq addq.
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulq /=; congr mkQuat => /=.
  by rewrite [in RHS]addrCA 2!addrA -mulrDl (addrC a) dotmulDl opprD addrA.
rewrite scalerDl -!addrA; congr (_ + _).
rewrite (addrCA (a' *v c')) [in RHS]addrCA; congr (_ + _).
rewrite scalerDr -addrA; congr (_ + _).
rewrite addrCA; congr (_ + _).
by rewrite crossmulC linearD /= crossmulC opprD opprK (crossmulC b').
Qed.

Lemma mulqDr : right_distributive mulq addq.
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulq /=; congr mkQuat => /=.
  rewrite mulrDr -!addrA; congr (_ + _).
  rewrite addrCA; congr (_ + _).
  by rewrite dotmulDr opprD.
rewrite scalerDr -!addrA; congr (_ + _).
rewrite (addrCA (a' *v b')) [in RHS]addrCA; congr (_ + _).
rewrite scalerDl -addrA; congr (_ + _).
by rewrite addrCA linearD.
Qed.

Lemma oneq_neq0 : 1%:q != 0 :> quat.
Proof. apply/eqP => -[]; apply/eqP. exact: oner_neq0. Qed.

Definition quat_RingMixin := RingMixin mulqA mul1q mulq1 mulqDl mulqDr oneq_neq0.
Canonical Structure quat_Ring := Eval hnf in RingType quat quat_RingMixin.

Lemma mulqE a b : mulq a b = a * b. Proof. done. Qed.

Lemma quat_realM (x y : R) : (x * y)%:q = x%:q * y%:q.
Proof.
by rewrite -mulqE /mulq /= dotmul0v subr0 scaler0 add0r scaler0 crossmulv0 addr0.
Qed.

Lemma iiN1 : `i * `i = -1.
Proof.
rewrite -mulqE /mulq /= scale0r crossmulvv dotmulE sum3E !mxE /=; simp => /=; congr mkQuat.
by rewrite /= oppr0.
Qed.

Lemma ijk : `i * `j = `k.
Proof.
rewrite -mulqE /mulq /= 2!scale0r dotmulE sum3E !mxE /= crossmulE !mxE /=; simp => /=. 
rewrite oppr0; congr mkQuat.
apply/rowP => i; rewrite !mxE /=; do 3 case: ifP => //; by simp.
Qed.

Lemma ikNj : `i * `k = - `j.
Proof.
rewrite -mulqE /mulq /= 2!scale0r dotmulE sum3E !mxE /= crossmulE !mxE /=; simp => /=.
congr mkQuat.
apply/rowP => i; rewrite !mxE /=.
do 3 case : ifP => //; by rewrite oppr0.
Qed.

Definition sqrq (Q : quat) := Q _0 ^+ 2 + norm (quatr Q) ^+ 2.

Lemma sqrq_eq0 Q : (sqrq Q == 0) = (Q == 0).
Proof.
case: Q => a a' /=; apply/idP/idP.
  by rewrite /sqrq /= paddr_eq0 ?sqr_ge0 // ?norm_ge0 // 2!sqrf_eq0 norm_eq0 => /andP[/eqP -> /eqP ->].
by case/eqP => -> ->; rewrite /sqrq /= norm0 expr0n addr0.
Qed.

Definition conjq (Q : quat) := mkQuat (quatl Q) (- quatr Q).
Notation "x '^*q'" := (conjq x) (at level 2, format "x '^*q'").

Lemma conjq0 : (0%:v)^*q = 0.
Proof. by apply/eqP; rewrite eq_quat /= !mxE oppr0 !eqxx. Qed.

Lemma conjqP (a : quat) : a * a^*q = (sqrq a)%:q.
Proof.
rewrite /mulq /=; congr mkQuat.
  by rewrite /= dotmulvN dotmulvv opprK -expr2.
by rewrite scalerN addNr add0r crossmulvN crossmulvv oppr0.
Qed.

Definition scaleq k (Q : quat) := mkQuat (k * quatl Q) (k *: quatr Q).

Lemma scaleqA a b w : scaleq a (scaleq b w) = scaleq (a * b) w.
Proof. rewrite /scaleq /=; congr mkQuat; by [rewrite mulrA | rewrite scalerA]. Qed.

Lemma scaleq1 : left_id 1 scaleq.
Proof.
by move=> q; rewrite /scaleq mul1r scale1r; apply/eqP; rewrite eq_quat /= !eqxx.
Qed.

Lemma scaleqDr : @right_distributive R quat scaleq +%R.
Proof. move=> a b c; by rewrite /scaleq /= mulrDr scalerDr. Qed.

Lemma scaleqDl w : {morph (scaleq^~ w : R -> quat) : a b / a + b}.
Proof. move=> m n; rewrite /scaleq mulrDl /= scalerDl; congr mkQuat. Qed.

Definition quat_lmodMixin := LmodMixin scaleqA scaleq1 scaleqDr scaleqDl.
Canonical quat_lmodType := Eval hnf in LmodType R quat quat_lmodMixin.

Lemma scaleqE (k : R) (a : quat) : 
  k *: a = k *: (a _0) %:q + k *: (a _i) *`i + k *: (a _j) *`j + k *: (a _k) *`k.
Proof.
apply/eqP; rewrite eq_quat /=; apply/and4P; split; [by simp | | | ]; by rewrite !mxE /=; simp.
Qed.

Lemma conjqE (Q : quat) : Q ^*q = - (1 / 2%:R) *: (Q + `i * Q * `i + `j * Q * `j + `k * Q * `k).
Proof.
apply/eqP; rewrite eq_quat; apply/and4P; split; apply/eqP.
  rewrite [in LHS]/= scaleqE /=.
  rewrite !(mul0r,mulr0,addr0) scale0r !add0r !dotmulDl.
  rewrite dotmulZv dotmulvv normi expr1n mulr1 dotmulC dotmul_crossmulA crossmulvv dotmul0v addr0.
  rewrite subrr add0r dotmulZv dotmulvv normj expr1n mulr1 dotmulC dotmul_crossmulA crossmulvv.
  rewrite dotmul0v addr0 dotmulZv dotmulvv normk expr1n mulr1 opprD addrA dotmulC dotmul_crossmulA.
  rewrite crossmulvv dotmul0v subr0 -opprD mulrN mulNr opprK -mulr2n -(mulr_natl (Q _0)) mulrA.
  by rewrite div1r mulVr ?mul1r // unitfE pnatr_eq0.
rewrite [in LHS]/= scaleqE /=. simp => /=.
rewrite !scale0r.
Abort.

Lemma conjq_scalar Q : (quatl Q)%:q = (1 / 2%:R) *: (Q + Q^*q).
Proof.
Abort.

Lemma conjq_vector Q : (quatr Q)%:v = (1 / 2%:R) *: (Q - Q^*q).
Abort.

Definition invq (Q : quat) : quat := (1 / sqrq Q) *: (Q ^*q).

Definition unitq : pred quat := [pred Q | Q != 0%:q].

Lemma mulVq : {in unitq, left_inverse 1 invq mulq}.
Proof.
move=> a; rewrite inE /= => a0.
rewrite /invq /mulq /=; congr mkQuat.
  rewrite dotmulZv -mulrA -mulrBr dotmulNv opprK dotmulvv.
  by rewrite div1r mulVr // unitfE sqrq_eq0.
rewrite scalerA scalerN -scalerBl mulrC subrr scale0r.
by rewrite scalerN crossmulNv crossmulZ crossmulvv scaler0 subrr.
Qed.

Lemma mulqV : {in unitq, right_inverse 1 invq mulq}.
Proof.
move=> a; rewrite inE /= => a0.
rewrite /invq /mulq /=; congr mkQuat.
  by rewrite scalerN dotmulvN opprK dotmulvZ mulrCA -mulrDr dotmulvv div1r mulVr // unitfE sqrq_eq0.
by rewrite scalerA scalerN -scaleNr -scalerDl mulrC addNr scale0r linearZ /= crossmulvN crossmulvv scalerN scaler0 subrr.
Qed.

Lemma unitqP : forall x y : quat, y * x = 1 /\ x * y = 1 -> unitq x.
Proof.
move=> x y [yx1 xy1]; rewrite /unitq inE; apply/eqP => x0.
move/esym: xy1; rewrite x0 mul0r.
apply/eqP; exact: oneq_neq0.
Qed.

Lemma invq0id : {in [predC unitq], invq =1 id}.
Proof.
move=> a; rewrite !inE negbK => /eqP ->.
by rewrite /invq /= conjq0 scaler0.
Qed.

Definition quat_UnitRingMixin := UnitRingMixin mulVq mulqV unitqP invq0id.
Canonical quat_unitRing := UnitRingType quat quat_UnitRingMixin.

Definition normq (Q : quat) := Num.sqrt (sqrq Q).

Lemma normq0 : normq 0 = 0.
Proof. by rewrite /normq /sqrq expr0n /= norm0 add0r expr0n sqrtr0. Qed.

Lemma eq0_normq x : normq x = 0 -> x = 0.
Proof.
rewrite /normq /sqrq => /eqP; rewrite -(@eqr_expn2 _ 2%N) // ?sqrtr_ge0 //.
rewrite sqr_sqrtr; last by rewrite addr_ge0 // ?sqr_ge0 // ?le0dotmul.
rewrite expr0n paddr_eq0 ?sqr_ge0 // 2!sqrf_eq0.
by case/andP; case: x => x0 x1 /= /eqP ->; rewrite norm_eq0 => /eqP ->.
Qed.

Lemma normqM (Q P : quat) : normq (mulq Q P) = normq Q * normq P.
Proof.
case: Q P => [a a'] [b b'] /=; apply/eqP.
rewrite /mulq /normq /= /sqrq /= -(@eqr_expn2 _ 2%N) // ?sqrtr_ge0 //; last first.
  by rewrite mulr_ge0 // sqrtr_ge0.
rewrite sqr_sqrtr //; last by rewrite addr_ge0 // ?sqr_ge0 // ?le0dotmul.
rewrite exprMn sqr_sqrtr //; last by rewrite le0dotmul.
rewrite sqr_sqrtr //; last by rewrite addr_ge0 // ?sqr_ge0 // ?le0dotmul.
rewrite sqrrB !dotmulDl !dotmulDr !dotmulvZ !dotmulZv.
rewrite {1}dotmul_crossmulCA crossmulvv dotmulv0 mulr0 addr0.
rewrite dotmul_crossmulA crossmulvv dotmul0v mulr0 addr0.
rewrite -dotmul_crossmulA crossmulvv dotmulv0 mulr0 add0r.
rewrite {1}crossmulC dotmulNv -dotmul_crossmulA crossmulvv dotmulv0 oppr0 mulr0 add0r.
rewrite (mulrCA b a) (dotmulC a' b') -!addrA (addrA (a * (b * _))).
rewrite -mulr2n 3!(addrCA _ (_ *+ 2)) (addrA (_ *+ 2)) -mulrA subrr add0r.
rewrite !dotmulvv norm_crossmul dotmul_cos addrCA !addrA addrC !addrA.
rewrite exprMn (@exprMn _ _ _ (cos _)) (mulrC (norm a')).
rewrite -mulrDr norm2 (addrC (sin _ ^+ 2)) vec_angle_switch cos2Dsin2 mulr1.
rewrite (@exprMn _ _ a) mulrA -expr2 -2!addrA (addrA (a ^+ 2 * _)) -mulrDr.
rewrite [Num.sqrt (b ^+ 2 + _ ) ^+ 2]sqr_sqrtr; last first.
  by rewrite addr_ge0 // ?le0dotmul // sqr_ge0.
rewrite mulrA -expr2 exprMn [in X in _ == X]mulrDl addrCA. 
apply/eqP; congr (_ + _).
by rewrite mulrDr mulrC addrC (mulrC (b ^+ 2)).
Qed.

Definition normQ Q := (normq Q)%:q. 

Lemma eq0_normQ x : normQ x = 0 -> x = 0.
Proof.
by rewrite /normQ => /eqP; rewrite quat_real0 => /eqP/eq0_normq.
Qed.

Definition lequat (Q P : quat) := 
  let: mkQuat Q1 Q2 := Q in let: mkQuat P1 P2 := P in
  (Q2 == P2) && (Q1 <= P1).

Lemma lequat_normD x y : lequat (normQ (x + y)) (normQ x + normQ y).
Proof.
Abort.

Definition ltquat (Q P : quat) := 
  let: mkQuat Q1 Q2 := Q in let: mkQuat P1 P2 := P in
  (Q2 == P2) && (Q1 < P1).

Lemma ltquat0_add : forall x y, ltquat 0 x -> ltquat 0 y -> ltquat 0 (x + y).
Abort.

Lemma ge0_lequat_total x y : lequat 0 x -> lequat 0 y -> lequat x y || lequat y x.
Abort.

Lemma normQM x y : normQ (x * y) = normQ x * normQ y.
Proof. by rewrite {1}/normQ normqM quat_realM. Qed.

Lemma lequat_def x y : lequat x y = (normQ (y - x) == y - x).
Abort.

Lemma ltquat_def x y : ltquat x y = (y != x) && lequat x y.
Abort.

Fail Definition quat_POrderedMixin := NumMixin lequat_normD ltquat0_add eq0_normQ
  ge0_lequat_total normQM lequat_def ltquat_def.
Fail Canonical Structure quat_numDomainType :=
  NumDomainType _ quat_POrderedMixin.

Record uquat := mkUQuat {
  quat_of_uquat :> quat ;
  _ : normq quat_of_uquat == 1 }.

Canonical uquat_subType := [subType for quat_of_uquat].

Lemma normuq (Q : uquat) : normq Q = 1.
Proof. by case: Q => /= Q /eqP. Qed.

Definition uquat_eqMixin := [eqMixin of uquat by <:].
Canonical uquat_eqType := EqType uquat uquat_eqMixin.
Definition uquat_choiceMixin := [choiceMixin of uquat by <:].
Canonical uquat_choiceType := ChoiceType uquat uquat_choiceMixin.

Lemma muluq_proof (Q P : uquat) : normq (mulq Q P) == 1.
Proof. by rewrite normqM 2!normuq mulr1. Qed.

Definition muluq (Q P : uquat) : uquat := mkUQuat (muluq_proof Q P).

Let vector := 'rV[R]_3.

(* rotation of a vector v about the direction "quatr Q" *)
Definition quat_rotation (Q : uquat) (v : vector) : quat := (Q : quat) * v%:v * Q^*q.

Definition associated_unit_quaternion (a : angle R) (w : 'rV[R]_3) :=
  mkQuat (cos (half_angle a)) (sin (half_angle a) *: w).

Lemma normq_associated_unit_quaternion a w : norm w = 1 -> 
  normq (associated_unit_quaternion a w) = 1.
Proof.
move=> w1.
by rewrite /normq /sqrq /= normZ exprMn w1 expr1n mulr1 norm2 cos2Dsin2 sqrtr1.
Qed.

Definition rotation_of_unit_quaternion' (q : uquat) : angle R * vector :=
  let a := scale_angle 2 (acos (q _0)) in
  (a, 
   if a == 0 then
     0 
   else
     (1 / (2%:R * sin (half_angle a)) *: quatr q)).
(* NB:
Record angle_axis := AngleAxis {
  angle_axis_val : angle R * vector ;
  _ : norm (angle_axis_val.2) == 1
 }.
*)

Lemma norm_rotation_of_unit_quaternion (q : uquat) : 
  norm (rotation_of_unit_quaternion' q).2 = 1.
Proof.
rewrite /rotation_of_unit_quaternion' /=.
case: ifPn => q00.
  admit.
Abort.

End quaternion.

(*

  option ('rV[R]_3 (* point *) * 'rV[R]_3 (* vec *) ).
Admitted.

Definition intersection (o o' : 'rV[R]_3) (v v' : 'rV[R]_3) : option 'rV[R]_3.
Admitted.

Definition length_prop (i : 'I_n) (f f' : frame) :
  unique_common_orthogonal (origin f) (origin f') ()
  length (links i) = `| |


Definition z_vec (i : 'I_n) := zframes i



joint i is located between links i-1 and i
z_vec (frames i) "is located along the axis of joint i"

the zi axis along the axis of joint i


Definition before_after_joint (i : 'I_n) : option (link * link):=
  match ltnP O i with
    | LtnNotGeq H (* 0 < i*) => Some (links i.-1, links i)
    | GeqNotLtn H (* i <= 0*) => None
  end.

link length and twist along and about the x_i-1 axis

Hypothesis :

Check forall i, (z_ax (basis (frames i))).

x_vec (frames i.-1) _|_ plane (z_vec (frames i.-1)),(z_vec (frames i))

length (links i) = distance from (z_vec (frames i.-1)) to (z_vec (frames i)) along (x_vec)





 *)


