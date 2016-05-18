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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Section extra.

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

Lemma trmxD (R : comRingType) m n (A B : 'M[R]_(m, n)) : (A + B)^T = A^T + B^T.
Proof. apply/matrixP => i j; by rewrite !mxE. Qed.

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

Variable R : rcfType.
Implicit Types u v : 'rV[R]_3.

Definition dotmul u v : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE u v : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma sum3E {T : rcfType} (f : 'I_3 -> T) : \sum_(i < 3) f i = f 0 + f 1 + f 2%:R.
Proof.
rewrite (bigD1 ord0) // (bigD1 (1 : 'I_3)) // (bigD1 (2%:R : 'I_3)) //= big_pred0 ?addr0 ?addrA //.
move=> i; by case/boolP : (i != 0) => //=; rewrite ifnot0 => /orP [] /eqP ->.
Qed.

Lemma dotmulC u v : u *d v = v *d u.
Proof. by rewrite /dotmul -[_ *m _]trmxK trmx_mul !trmxK mxE. Qed.

Lemma dotmul0v v : 0 *d v = 0.
Proof. by rewrite [LHS]mxE big1 // => i; rewrite mxE mul0r. Qed.

Lemma dotmulv0 v : v *d 0 = 0.
Proof. by rewrite dotmulC dotmul0v. Qed.

Lemma dotmulDr a b c : a *d (b + c) = a *d b + a *d c.
Proof. by rewrite {1}/dotmul trmxD mulmxDr mxE. Qed.

Lemma dotmulDl a b c : (b + c) *d a = b *d a + c *d a.
Proof. by rewrite dotmulC dotmulDr dotmulC (dotmulC c). Qed.

Lemma dotmulD u v : (u + v) *d (u + v) = u *d u + (u *d v) *+ 2 + v *d v.
Proof. rewrite dotmulDr 2!dotmulDl -!addrA; congr (_ + _); by rewrite dotmulC. Qed.

Lemma dotmulvN u v : u *d -v = - (u *d v).
Proof. by rewrite /dotmul linearN /= mulmxN mxE. Qed.

Lemma dotmulNv u v : - u *d v = - (u *d v).
Proof. by rewrite dotmulC dotmulvN dotmulC. Qed.

Lemma dotmulZ u k v : u *d (k *: v) = k * (u *d v).
Proof. by rewrite /dotmul linearZ /= -scalemxAr mxE. Qed.

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

Notation "*d%R" := (@dotmul _) : ring_scope.
Notation "u *d w" := (dotmul u w) (at level 40) : ring_scope.

Section orthogonal_def.

Variables (n : nat) (R : rcfType).

Definition orthogonal := [qualify M : 'M[R]_n | M *m M^T == 1%:M].
Fact orthogonal_key : pred_key orthogonal. Proof. by []. Qed.
Canonical orthogonal_keyed := KeyedQualifier orthogonal_key.

Definition rotation := [qualify M : 'M[R]_n | (M \is orthogonal) && (\det M == 1)].
Fact rotation_key : pred_key rotation. Proof. by []. Qed.
Canonical rotation_keyed := KeyedQualifier rotation_key.

End orthogonal_def.

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

Lemma orthogonalP R M : 
  reflect (forall i j, row i M *d row j M = (i == j)%:R) (M \is 'O_3[R]).
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

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Ltac simp_ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=].
Ltac simpr := rewrite ?(mulr0,mul0r,mul1r,mulr1,addr0,add0r).

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

(* find a better name *)
Definition triple_product_mat (u v w : vector) :=
  \matrix_(i < 3) [eta \0 with 0 |-> u, 1 |-> v, 2%:R |-> w] i.

Lemma triple_prod_matE (a b c : vector) : 
  triple_product_mat a b c = col_mx a (col_mx b c).
Proof.
apply/matrixP => i j; rewrite !mxE /SimplFunDelta /=.
case: ifPn => i0.
  case: splitP => [j0|k ik]; first by rewrite (ord1 j0).
  exfalso. move/negP: i0; apply; apply/negP; by rewrite -val_eqE /= ik.
case: ifPn => i1.
  rewrite (eqP i1); case: splitP => [j0|]; first by rewrite (ord1 j0).
  case => -[|k Hk] //= zerotwo _; rewrite mxE.
  case: splitP => k; by rewrite (ord1 k).
case: ifPn => i2.
  rewrite (eqP i2); case: splitP => [j0|]; first by rewrite (ord1 j0).
  case => -[|[|k Hk]] //= onetwo _; rewrite mxE.
  case: splitP => k; by rewrite (ord1 k).
by rewrite ifnot0 (negbTE i1) (negbTE i2) in i0.
Qed.

Lemma triple_prod_mat_mulmx (v : vector) a b c : 
  v *m (triple_product_mat a b c)^T = 
  row_mx (v *d a)%:M (row_mx (v *d b)%:M (v *d c)%:M).
Proof.
rewrite triple_prod_matE (tr_col_mx a) (tr_col_mx b) (mul_mx_row v a^T). 
by rewrite (mul_mx_row v b^T) /dotmul -!mx11_scalar.
Qed.

Lemma row'_triple_product_mat (i : 'I_3) (u v w : vector) :
  row' i (triple_product_mat u v w) = [eta \0 with
  0 |-> \matrix_(k < 2) [eta \0 with 0 |-> v, 1 |-> w] k,
  1 |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> w] k,
  2%:R |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> v] k] i.
Proof.
case: i => [[|[|[|?]]]] ?; apply/matrixP=> [] [[|[|[|?]]]] ? j;
by rewrite !mxE /=.
Qed.

(* Definition mixed_product_mat n (u : 'I_n -> 'rV[R]_n) :=  *)
(*   \matrix_(i < n, j < n) u i ord0 j. *)

(* Definition crossmul (u : 'rV[R]_n.+1) (v : 'I_n -> 'rV[R]_n.+1) : 'rV[R]_n.+1 := *)
(*   \row_(k < n) \det (mixed_product_mat (delta_mx 0 k)). *)

Definition crossmul (u v : vector) : vector :=
  \row_(k < 3) \det (triple_product_mat (delta_mx 0 k) u v).

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
  u *d (v *v w) = \det (triple_product_mat u v w).
Proof.
pose M (k : 'I_3) : 'M_3 := triple_product_mat (delta_mx 0 k) v w.
pose Mu12 := triple_product_mat (u 0 1 *: delta_mx 0 1 + u 0 2%:R *: delta_mx 0 2%:R) v w.
rewrite (@determinant_multilinear _ _ _ (M 0) Mu12 0 (u 0 0) 1) ?mul1r
        ?row'_triple_product_mat //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx /tnth /=.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
rewrite [\det Mu12](@determinant_multilinear _ _ _
  (M 1) (M 2%:R) 0 (u 0 1) (u 0 2%:R)) ?row'_triple_product_mat //; last first.
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
pose M w := triple_product_mat (delta_mx 0 k) u w.
rewrite (@determinant_multilinear _ _ (M _) (M v) (M w) 2%:R a 1);
  rewrite ?row'_triple_product_mat ?mul1r ?scale1r ?mxE //=.
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

Lemma det_mx11 (A : 'M[R]_1) : \det A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar det_scalar. Qed.

Lemma cofactor_mx22 (A : 'M[R]_2) i j :
  cofactor A i j = (-1) ^+ (i + j) * A (i + 1) (j + 1).
Proof.
rewrite /cofactor det_mx11 !mxE; congr (_ * A _ _);
by apply/val_inj; move: i j => [[|[|?]]?] [[|[|?]]?].
Qed.

Lemma det_mx22 (A : 'M[R]_2) : \det A = A 0 0 * A 1 1 -  A 0 1 * A 1 0.
Proof.
rewrite (expand_det_row _ ord0) !(mxE, big_ord_recl, big_ord0).
rewrite !(mul0r, mul1r, addr0) !cofactor_mx22 !(mul1r, mulNr, mulrN).
by rewrite !(lift0E, add0r) /= addrr_char2.
Qed.

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

Lemma crossmulD (a b c : vector) : a *v (b + c) = a *v b + a *v c.
Proof.
apply/rowP => i.
rewrite !crossmulE !mxE /=.
do 3 (case: ifP => [/eqP|] ?;
  first by rewrite 2!mulrDr -!addrA; congr (_ + _); by rewrite addrCA opprD).
by rewrite addr0.
Qed.

Lemma crossmulNv (u v : vector) : - u *v v = - (u *v v).
Proof.
rewrite 2!crossmulE; apply/rowP => i; rewrite !mxE /=.
do 3 (case: ifP => ?; first by rewrite opprB addrC mulNr opprK mulNr).
by rewrite oppr0.
Qed.

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
  clear -k0 k1 k2; exfalso.
  by case: k k0 k1 k2 => -[? | [? | [? |]]].
move/forallP => /= H; apply/eqP/rowP => i.
rewrite crossmulE /SimplFunDelta /= !mxE; apply/eqP.
case: ifPn => [_|i0].
  move: (H 1) => /forallP/(_ 2%:R) /= /eqP <-; by rewrite subr_eq0 mulrC.
case: ifPn => [_|i1].
  move: (H 0) => /forallP/(_ 2%:R) /= /eqP <-; by rewrite subr_eq0 mulrC.
case: ifPn => [_|//]; move: (H 0) => /forallP/(_ 1) /= /eqP <-.
by rewrite subr_eq0 mulrC.
Qed.

(* rewrite linear_sum. *)

Lemma crossmulvv (u : vector) : u *v u = 0.
Proof.
rewrite crossmulE; apply/rowP => i.
rewrite !mxE; do 3 rewrite mulrC subrr.
rewrite /SimplFunDelta /=.
case: ifP => [//|_]; case: ifP => [//|_]; by case: ifP.
Qed.

Lemma mulmxl_crossmulr M u v : M *m (u *v v) = u *v (M *m v).
Proof.
by rewrite -(mul_rV_lin1 [linear of crossmul u]) mulmxA mul_rV_lin1.
Qed.

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

Lemma triple_prod_mat_perm_12 a b c :
  xrow 1 2%:R (triple_product_mat a b c) = triple_product_mat a c b.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma triple_prod_mat_perm_01 a b c :
  xrow 0 1 (triple_product_mat a b c) = triple_product_mat b a c.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma triple_prod_mat_perm_02 a b c :
 xrow 0 2%:R (triple_product_mat a b c) = triple_product_mat c b a.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma scalar_triple_prod_circ_shift a b c : a *d (b *v c) = c *d (a *v b).
Proof. 
rewrite crossmul_triple.
rewrite -triple_prod_mat_perm_12 xrowE det_mulmx det_perm /= odd_tperm /=.
rewrite -triple_prod_mat_perm_01 xrowE det_mulmx det_perm /= odd_tperm /=.
by rewrite expr1 mulrA mulrNN 2!mul1r -crossmul_triple.
Qed.

Lemma dotmul_crossmul u v x : u *d (v *v x) = (u *v v) *d x.
Proof. by rewrite scalar_triple_prod_circ_shift dotmulC. Qed.

Lemma crossmul_dotmul u v (x : vector) : 
  \det (triple_product_mat u v x) = (u *v v) *d x.
Proof. by rewrite -crossmul_triple dotmul_crossmul. Qed.

Lemma mulmx_triple_prod_mat M a b c : 
  triple_product_mat a b c *m M = triple_product_mat (a *m M) (b *m M) (c *m M).
Proof.
apply/matrixP => i j.
move: i => -[[|[|[] // ]] ?]; rewrite !mxE; apply eq_bigr => /= ? _; by rewrite mxE.
Qed.

Lemma det_crossmul_dotmul M a b (x : vector) : 
  ((\det M) *: (a *v b)) *d x = (((a *m M) *v (b *m M)) *m M^T) *d x.
Proof.
transitivity (\det M * \det (triple_product_mat a b x)).
  by rewrite dotmulC dotmulZ dotmulC -crossmul_triple dotmul_crossmul.
transitivity (\det (triple_product_mat (a *m M) (b *m M) (x *m M))).
  by rewrite mulrC -det_mulmx mulmx_triple_prod_mat.
transitivity (((a *m M) *v (b *m M)) *d (x *m M)).
  by rewrite crossmul_dotmul.
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
by rewrite double_crossmul (dotmulC _ a) dotmul_crossmul crossmulvv dotmul0v 
  scale0r subr0 -dotmul_crossmul.
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

Variable R : rcfType.
Implicit Types u : 'rV[R]_3.

Definition norm u := Num.sqrt (u *d u).

Lemma normN a : norm (- a) = norm a.
Proof. by rewrite /norm dotmulNv dotmulvN opprK. Qed.

Lemma norm2 (k : R) : `| k | ^+ 2 = k ^+ 2.
Proof.
case: (ltrP 0 k) => [k0|]; first by rewrite gtr0_norm.
rewrite ler_eqVlt; case/orP => [/eqP ->|k0].
by rewrite normr0.
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
rewrite /norm dotmulZ dotmulC dotmulZ mulrA. 
by rewrite sqrtrM -expr2 ?sqrtr_sqr // sqr_ge0.
Qed.

Lemma dotmulvv u : u *d u = norm u ^+ 2.
Proof.
rewrite /norm [_ ^+ _]sqr_sqrtr // dotmulE sumr_ge0 //.
by move=> i _; rewrite sqr_ge0.
Qed.

Lemma sqr_norm u : norm u ^+ 2 = u 0 0 ^+ 2 + u 0 1 ^+ 2 + u 0 2%:R ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum3E !expr2. Qed.

Lemma norm_crossmul' u v : (norm (u *v v))^+2 = (norm u * norm v)^+2 - (u *d v)^+2 .
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

Lemma orth_preserves_dotmulvv v M : M \is 'O_3[R] -> (v *m M) *d (v *m M) = v *d v.
Proof.
move=> HM.
rewrite dotmul_trmx -mulmxA (_ : M *m _ = 1) ?mulmx1 //.
by move: HM; rewrite orthogonalE => /eqP.
Qed.

Lemma orth_preserves_norm u M : M \is 'O_3[R] -> norm (u *m M) = norm u.
Proof. move=> HM; by rewrite /norm orth_preserves_dotmulvv. Qed.

Lemma orth_preserves_dotmul M u v : M \is 'O_3[R] -> (u *m M) *d (v *m M) = u *d v.
Proof.
move=> HM.
have := orth_preserves_dotmulvv (u + v) HM.
rewrite mulmxDl dotmulD.
rewrite dotmulD.
rewrite orth_preserves_dotmulvv // (orth_preserves_dotmulvv v HM) //.
move/(congr1 (fun x => x - v *d v)).
rewrite -!addrA subrr 2!addr0.
move/(congr1 (fun x => - (u *d u) + x)).
rewrite !addrA (addrC (- (u *d u))) subrr 2!add0r.
rewrite -2!mulr2n => /eqP.
by rewrite eqr_pmuln2r // => /eqP.
Qed.

Lemma orth_preserves_norm_crossmul M u v : M \is 'O_3[R] ->
  norm (u *v v) = norm ((u *m M) *v (v *m M)).
Proof.
move=> MO.
by rewrite -(orth_preserves_norm (u *v v) MO) (mulmxr_crossmulr u v MO) 
  normZ (orthogonal_det MO) mul1r.
Qed.

Lemma norm_crossmul_normal u v : u *d v = 0 ->
  norm u = 1 -> norm v = 1 -> norm (u *v v) = 1.
Proof.
move=> uv0 u1 v1; apply/eqP.
rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 //.
by rewrite norm_crossmul' u1 v1 uv0 expr0n /= subr0 mulr1 // norm_ge0.
Qed.

End norm.

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
rewrite -norm_eq0 -(@eqr_expn2 _ 2) // ?norm_ge0 // exprnP expr0n.
rewrite -exprnP norm_crossmul' (eqP uv0) expr0n subr0.
rewrite -expr0n eqr_expn2 //.
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

Lemma cos_max (a : angle) : `| cos a | <= 1.
Proof. rewrite -lecR (ler_trans (normc_ge_Re _)) //; by case: a => ? /= /eqP ->. Qed. 

Lemma cos2Dsin2 a : (cos a)^2 + (sin a)^2 = 1.
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
by rewrite -exprnP sqrtr_sqr /= ger0_norm // -expi_cos_sin expiK.
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
move=> k0; by rewrite /vec_angle dotmulZ linearZ /= normZ ger0_norm ?ltrW // complexZ argZ.
Qed.

Lemma vec_angleZ_neg (u v : 'rV[R]_3) k : k < 0 ->
  vec_angle u (k *: v) = vec_angle (- u) v.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite oppr0 !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite scaler0 !vec_angle0.
move=> k0.
rewrite /vec_angle dotmulZ linearZ /= normZ ltr0_norm //.
by rewrite mulNr complexZ argZ_neg // opp_conjc dotmulNv crossmulNv normN.
Qed.

Lemma vec_anglevv u : u != 0 -> vec_angle u u = 0.
Proof.
move=> u0.
rewrite /vec_angle /= crossmulvv norm0 complexr0 dotmulvv arg_Re ?arg1 //.
by rewrite ltr_neqAle sqr_ge0 andbT eq_sym sqrf_eq0 norm_eq0.
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

Lemma polarization_identity (a b : 'rV[R]_3) : 
  a *d b = 1 / 4%:R * (norm (a + b) ^+ 2 - norm (a - b) ^+ 2).
Proof.
apply: (@mulrI _ 4%:R); first by rewrite unitfE pnatr_eq0.
rewrite [in RHS]mulrA div1r divrr ?mul1r; last by rewrite unitfE pnatr_eq0.
rewrite -2!dotmulvv dotmulD dotmulD mulr_natl (addrC (a *d a)).
rewrite (_ : 4 = 2 + 2)%N // mulrnDr -3![in RHS]addrA; congr (_ + _).
rewrite opprD addrCA 2!addrA -(addrC (a *d a)) subrr add0r.
rewrite addrC opprD 2!dotmulvN dotmulNv opprK subrK.
by rewrite -mulNrn opprK.
Qed.

Lemma cosine_law a b c :
  norm (b - c) ^+ 2 = norm (c - a) ^+ 2 + norm (b - a) ^+ 2 -
  norm (c - a) * norm (b - a) * cos (vec_angle (b - a) (c - a)) *+ 2.
Proof.
rewrite -[in LHS]dotmulvv (_ : b - c = b - a - (c - a)); last first.
  by rewrite -!addrA opprB (addrC (- a)) (addrC a) addrK.
rewrite dotmulD dotmulvv [in X in _ + _ + X = _]dotmulvN dotmulNv opprK dotmulvv dotmulvN.
rewrite addrAC (addrC (norm (b - a) ^+ _)); congr (_ + _).
by rewrite dotmul_cos mulNrn (mulrC (norm (b - a))).
Qed.

Lemma cosine_law2 a b c : norm (c - a) != 0 -> norm (b - a) != 0 ->
  cos (vec_angle (b - a) (c - a)) = 
  (norm (b - c) ^+ 2 - norm (c - a) ^+ 2 - norm (b - a) ^+ 2) /
  (norm (c - a) * norm (b - a) *- 2).
Proof.
move=> H0 H1.
rewrite (cosine_law a b c) -2!addrA addrCA -opprD subrr addr0.
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

Lemma cos_vec_angle a b : norm a != 0 -> norm b != 0 -> 
  `| cos (vec_angle a b) | = Num.sqrt (1 - (norm (a *v b) / (norm a * norm b)) ^+ 2).
Proof.
move=> Ha Hb.
rewrite norm_crossmul mulrAC divrr // ?mul1r; last by rewrite unitfE mulf_neq0.
rewrite norm2.
move: (cos2Dsin2 (vec_angle a b)) => /eqP; rewrite eq_sym -subr_eq => /eqP ->.
by rewrite -exprnP sqrtr_sqr.
Qed.

Lemma orth_preserves_vec_angle M v w : M \is 'O_3[R] ->
  vec_angle v w = vec_angle (v *m M) (w *m M).
Proof.
move=> HM.
rewrite /vec_angle orth_preserves_dotmul; last by assumption.
by rewrite -orth_preserves_norm_crossmul.
Qed.

End angle.

(* rotation around the y axis *)
Definition Ry (R : rcfType) (a : angle R) := triple_product_mat
  (\row_k [eta \0 with 0 |-> cos a, 1 |-> 0, 2%:R |-> sin a] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> 1, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> - sin a, 1 |-> 0, 2%:R |-> cos a] k).

Lemma Ry_is_SO R a : Ry a \is 'O_3[R].
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

Definition Rx R (a : angle R) := triple_product_mat
  (\row_k [eta \0 with 0 |-> 1, 1 |-> 0, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> cos a, 2%:R |-> - sin a] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> sin a, 2%:R |-> cos a] k).

Definition Rz R (a : angle R) := triple_product_mat
  (\row_k [eta \0 with 0 |-> cos a, 1 |-> - sin a, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> sin a, 1 |-> cos a, 2%:R |-> 0] k)
  (\row_k [eta \0 with 0 |-> 0, 1 |-> 0, 2%:R |-> 1] k).

Section triad.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.

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
rewrite -{1}(norm_scale_normalize u) dotmulC dotmulZ dotmulvv norm_normalize //.
by rewrite expr1n mulr1.
Qed.

Definition orthogonalize (u v : vector) : vector := 
  v - (v *d normalize u) *: normalize u.

Lemma orthogonalizeP u v : u *d orthogonalize u v = 0.
Proof.
rewrite dotmulDr dotmulvN dotmulZ dotmul_normalize mulrC -dotmulZ.
by rewrite norm_scale_normalize dotmulC subrr.
Qed.

Lemma orthogonalize_neq0 u v : ~~ colinear u v -> orthogonalize u v != 0.
Proof.
move=> uv.
rewrite /orthogonalize subr_eq0; apply: contra uv => /eqP ->.
by rewrite colinear_sym /normalize scalerA scale_colinear.
Qed.

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
Proof. by rewrite /= /xtriad /ytriad {2}/normalize dotmulZ orthogonalizeP mulr0. Qed.

Definition ztriad := xtriad *v ytriad.

Lemma ztriad_norm : norm ztriad = 1.
Proof. by rewrite norm_crossmul_normal // ?xtriad_norm // ?ytriad_norm // xytriad_ortho. Qed.

Lemma ztriad_neq0 : ztriad != 0.
Proof. by rewrite -norm_eq0 ztriad_norm oner_neq0. Qed.

Lemma triad_is_ortho : triple_product_mat xtriad ytriad ztriad \is 'O_3[R].
Proof.
apply/orthogonalP.
case=> -[i0|[i1|[i2|//]]]; case=> -[j0|[j1|[j2|//]]] /=; rewrite !rowK /SimplFunDelta /=.
- by rewrite dotmulvv xtriad_norm // expr1n.
  by rewrite xytriad_ortho.
  by rewrite dotmul_crossmul crossmulvv dotmul0v.
- by rewrite dotmulC xytriad_ortho.
  by rewrite dotmulvv ytriad_norm // expr1n.
  by rewrite dotmulC -dotmul_crossmul crossmulvv dotmulv0.
- by rewrite dotmulC dotmul_crossmul crossmulvv dotmul0v.
  by rewrite -dotmul_crossmul crossmulvv dotmulv0.
  by rewrite dotmulvv ztriad_norm // expr1n.
Qed.

Lemma triad_is_orthonormal : triple_product_mat xtriad ytriad ztriad \is 'SO_3[R].
Proof.
rewrite rotationE triad_is_ortho /= -crossmul_triple dotmul_crossmul -/ztriad.
by rewrite dotmul_cos ztriad_norm !mul1r vec_anglevv ?cos0 // -norm_eq0 ztriad_norm ?oner_neq0.
Qed.

End triad.

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
rewrite (tr_row_mx a) (mul_row_col (col_mx (rot T) 0)) trmxD trmx_mul.
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
rewrite (tr_row_mx a) trmx1 (mul_row_col (col_mx (rot T) 0)) trmxD.
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
  (triple_product_mat Xl Yl Zl,
   triple_product_mat Xr Yr Zr).

Lemma rots1_is_SO : rots.1 \is 'SO_3[R]. Proof. exact: triad_is_orthonormal. Qed.
Lemma rots2_is_SO : rots.2 \is 'SO_3[R]. Proof. exact: triad_is_orthonormal. Qed.

Definition rot3 := rots.1^T *m rots.2.

Lemma rot3_is_SO : rot3 \is 'SO_3[R].
Proof. by rewrite rpredM // ?rots2_is_SO // rotationV rots1_is_SO. Qed.

Definition trans3 : vector := r1 - l1 *m rot3.

Lemma xtriad_l_r : xtriad l1 l2 *m rot3 = xtriad r1 r2.
Proof.
rewrite /rot3 /rots /= mulmxA triple_prod_mat_mulmx xytriad_ortho.
rewrite dotmul_crossmul crossmulvv dotmul0v dotmulvv xtriad_norm //.
rewrite expr1n triple_prod_matE (mul_row_col 1%:M) mul1mx (mul_row_col 0%:M).
do 2 rewrite mul_scalar_mx scale0r; by do 2 rewrite addr0.
Qed.

Lemma ytriad_l_r : ytriad l1 l2 l3 *m rot3 = ytriad r1 r2 r3.
Proof.
rewrite /rot3 /rots /= mulmxA triple_prod_mat_mulmx dotmulC xytriad_ortho.
rewrite dotmulvv ytriad_norm // expr1n dotmulC -dotmul_crossmul.
rewrite crossmulvv dotmulv0 triple_prod_matE.
rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
rewrite (mul_row_col 1%:M) mul_scalar_mx scale1r.
by rewrite mul_scalar_mx scale0r addr0.
Qed.

Lemma ztriad_l_r : ztriad l1 l2 l3 *m rot3 = ztriad r1 r2 r3.
Proof.
rewrite /rot3 /rots /= mulmxA triple_prod_mat_mulmx.
rewrite {1}/ztriad dotmulC dotmul_crossmul crossmulvv dotmul0v.
rewrite {1}/ztriad -dotmul_crossmul crossmulvv dotmulv0.
rewrite dotmulvv ztriad_norm // expr1n triple_prod_matE.
do 2 rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite mul_scalar_mx scale1r.
Qed.

End transformation_given_three_points.

Section technical_properties_of_rigid_transformations.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Section two_vectors.

Variables a b a' b' : vector.
Hypotheses (aa' : norm a = norm a') (bb' : norm b = norm b').
Hypotheses (ab : cos (vec_angle a b) = cos (vec_angle a' b')).

Lemma preserve_vec_angle_L k : vec_angle (k *: a) b = vec_angle (k *: a') b'.
Proof.
case/boolP : (k == 0) => [/eqP ->{k}|k0]; first by rewrite 2!scale0r !vec_angle0.
rewrite /vec_angle dotmulC dotmulZ dotmulC [in RHS]dotmulC dotmulZ [in RHS]dotmulC.
rewrite (_ : _ *v _ = k *: (a *v b)); last by rewrite crossmulC linearZ /= -scalerN -crossmulC.
rewrite (_ : (k *: _) *v _ = k *: (a' *v b')); last first.
  by rewrite crossmulC linearZ /= -scalerN -crossmulC.
rewrite 2!normZ -(_ : a *d b = a' *d b'); last by rewrite 2!dotmul_cos -aa' -bb' [in LHS]ab.
rewrite -(_ : norm (a *v b) = norm (a' *v b')); first by reflexivity.
by rewrite 2!norm_crossmul -aa' -bb' [in LHS]abs_sin ab -abs_sin.
Qed.

Lemma preserve_vec_angle_R k : vec_angle a (k *: b) = vec_angle a' (k *: b').
Proof.
case: (lerP 0 k) => [|k0]; last first.
  by rewrite 2!(vec_angleZ_neg _ _ k0) -(scale1r a) -(scale1r a') -2!scaleNr preserve_vec_angle_L.
rewrite ler_eqVlt; case/orP => [/eqP <-{k}|k0]; first by rewrite 2!scale0r 2!vec_angle0.
by rewrite 2!(vec_angleZ _ _ k0) -(scale1r a) -(scale1r a') preserve_vec_angle_L.
Qed.

End two_vectors.

Section three_vectors.

Variables a b c a' b' c' : vector.
Hypotheses (aa' : norm a = norm a') (bb' : norm b = norm b') (cc' : norm c = norm c').
Hypotheses (bc : cos (vec_angle b c) = cos (vec_angle b' c'))
  (ab : cos (vec_angle a b) = cos (vec_angle a' b'))
  (ac : cos (vec_angle a c) = cos (vec_angle a' c')).

Lemma preserve_norm_double_crossmul : norm (a *v (b *v c)) = norm (a' *v (b' *v c')).
Proof.
rewrite 2!double_crossmul 2!normD.
have <- : a *d c = a' *d c' by rewrite 2!dotmul_cos cc' aa' [in LHS]ac.
have <- : a *d b = a' *d b' by rewrite 2!dotmul_cos bb' aa' [in LHS]ab.
rewrite -!scaleNr !normZ (_ : vec_angle _ _ = vec_angle ((a *d c) *: b') (- (a *d b) *: c')).
  by rewrite bb' cc'.
apply (preserve_vec_angle_L bb'); first by rewrite 2!normZ cc'.
rewrite (@preserve_vec_angle_R b c b' c' bb' cc' bc); reflexivity.
Qed.

Lemma preserve_cos_vec_angle_crossmul : norm a != 0 -> norm (b *v c) != 0 ->
  `|cos (vec_angle a (b *v c))| = `|cos (vec_angle a' (b' *v c'))|.
Proof.
move=> a0 bvc.
rewrite [in LHS](cos_vec_angle a0 bvc) [in RHS]cos_vec_angle; last 2 first.
  by rewrite -aa'.
  by rewrite norm_crossmul -bb' -cc' abs_sin -bc -abs_sin -norm_crossmul.
rewrite -aa' -(_ : norm (b *v c) = norm (b' *v c')); last first.
  by rewrite norm_crossmul norm_crossmul cc' bb' [in LHS]abs_sin bc -abs_sin.
by rewrite [in LHS]preserve_norm_double_crossmul.
Qed.

Lemma preserve_norm_double_crossmul2 :
  norm ((a *v b) *v (a *v c)) = norm ((a' *v b') *v (a' *v c')).
Proof.
rewrite [in LHS]dotmul_crossmul2 [in RHS]dotmul_crossmul2 2!normZ aa'.
suff Htmp : `| a *d (b *v c) | = `| a' *d (b' *v c') | by rewrite [in LHS]Htmp.
rewrite dotmul_cos dotmul_cos -aa' -(_ : norm (b *v c) = norm (b' *v c')); last first.
  by rewrite norm_crossmul norm_crossmul bb' cc' [in LHS]abs_sin bc -abs_sin.
case/boolP : (norm a == 0) => [/eqP|]a0; first by rewrite a0 mul0r [in LHS]mul0r mul0r.
case/boolP : (norm (b *v c) == 0) => [/eqP|]bvc; first by rewrite bvc mulr0 [in LHS]mul0r mul0r.
suff Htmp : `| cos (vec_angle a (b *v c)) | = `| cos (vec_angle a' (b' *v c')) |.
  by rewrite [in LHS]normrM [in RHS]normrM [in LHS]Htmp.
by apply preserve_cos_vec_angle_crossmul.
Qed.

Lemma preserve_vec_angle_crossmul2 :
  vec_angle (a *v b) (a *v c) = vec_angle (a' *v b') (a' *v c').
Proof.
rewrite /vec_angle -[in LHS]dotmul_crossmul [in LHS]double_crossmul.
rewrite -[in RHS]dotmul_crossmul [in RHS]double_crossmul.
rewrite [in LHS]dotmulDr [in RHS]dotmulDr 2!dotmulvN !dotmulZ.
have -> : b *d c = b' *d c' by rewrite 2!dotmul_cos bb' cc' [in LHS]bc.
have -> : b *d a = b' *d a'.
  by rewrite 2!dotmul_cos bb' aa' vec_angle_switch [in LHS]ab vec_angle_switch.
have -> : a *d c = a' *d c' by rewrite 2!dotmul_cos cc' aa' [in LHS]ac.
by rewrite 2!dotmulvv aa' [in LHS]preserve_norm_double_crossmul2.
Qed.

End three_vectors.

Let coordinate := 'rV[R]_3.
Variable n : nat.
Variables from to : coordinate ^ n.

Definition preserves_norm n (from to : coordinate ^ n) :=
  forall i j, norm (from i - from j) = norm (to i - to j).

Definition preserves_cos_angle n (from to : coordinate ^ n) := forall i j k, 
  cos (vec_angle (from j - from i) (from k - from i)) =
  cos (vec_angle (to j - to i) (to k - to i)).

Lemma preserves_norm_cos_angle : preserves_norm from to -> preserves_cos_angle from to.
Proof.
move=> H i j k; case/boolP : (norm (from k - from i) == 0) => [H0|H0].
  rewrite norm_eq0 in H0; rewrite (eqP H0); move: H0.
  rewrite -norm_eq0 H norm_eq0 => /eqP ->; by rewrite /vec_angle 2!dotmulv0 2!crossmulv0.
case/boolP : (norm (from j - from i) == 0) => H1.
  rewrite norm_eq0 in H1; rewrite (eqP H1); move: H1.
  rewrite -norm_eq0 H norm_eq0 => /eqP ->; by rewrite /vec_angle 2!dotmul0v 2!crossmul0v.
rewrite [in LHS](cosine_law2 H0 H1); apply/esym; by rewrite [in LHS]cosine_law2 -?H.
Qed.

Lemma preserves_dotmul : preserves_norm from to -> 
  forall p q r, (to p - to q) *d (to r - to q) = (from p - from q) *d (from r - from q).
Proof.
move=> pnorm p q r.
by rewrite !dotmul_cos -!pnorm -[in LHS](preserves_norm_cos_angle pnorm).
Qed.

Definition preserves_sin_angle n (from to : coordinate ^ n) := forall i j k, 
  `| sin (vec_angle (from j - from i) (from k - from i)) | =
  `| sin (vec_angle (to j - to i) (to k - to i)) |.

Lemma preserves_cos_sin_angle : preserves_cos_angle from to -> preserves_sin_angle from to.
Proof.
move=> H i j k; apply/eqP.
rewrite -(@eqr_expn2 _ 2 _ _ erefl) ?normr_ge0; try reflexivity.
apply/eqP; rewrite -[in LHS]normrX -[in RHS]normrX.
set a := (X in `| sin X ^+ _ | = _). set b := (X in _ = `| sin X ^+ _| ).
move: (cos2Dsin2 a) => /esym/eqP.
rewrite addrC -subr_eq -!exprnP => /eqP Ha.
move: (cos2Dsin2 b) => /esym/eqP.
rewrite addrC -subr_eq -!exprnP => /eqP Hb.
rewrite [in LHS]ger0_norm; last by rewrite sqr_ge0.
rewrite [in RHS]ger0_norm; last by rewrite sqr_ge0.
by rewrite -[in LHS]Ha -Hb [in LHS]H.
Qed.

Lemma rigid_preserves_cos_vec_angleD : preserves_norm from to -> forall i j k l cst, 
  cos (vec_angle (to j - to i) ((to k - to i) - cst *: (to l - to i))) =
  cos (vec_angle (from j - from i) ((from k - from i) - cst *: (from l - from i))).
Proof.
move=> pnorm /= i0 j k l cst.
case/boolP : (cst == 0) => [/eqP ->{cst}|cst0]. 
  by rewrite 2!scale0r 2!subr0 [in RHS](preserves_norm_cos_angle pnorm).
rewrite /vec_angle.
set rhs := RHS. set a := _ +i* _. rewrite {}/rhs.
set lhs := LHS. set b := _ +i* _. rewrite {}/lhs.
suff : a = b by move=> ->.
rewrite {}/a {}/b.
apply/eqP; rewrite eq_complex /=.
apply/andP; split; apply/eqP.
  rewrite [in LHS]dotmulDr [RHS]dotmulDr [in LHS]dotmul_cos [in RHS]dotmul_cos.
  rewrite [in RHS](pnorm j i0) -[in LHS](pnorm k i0) [in RHS](preserves_norm_cos_angle pnorm).
  rewrite -2!scaleNr dotmulZ dotmulZ 2!dotmul_cos -(pnorm j i0) -(pnorm l i0).
  rewrite -[in X in X + _ = _](preserves_norm_cos_angle pnorm). 
  rewrite -[in X in _ + X = _](preserves_norm_cos_angle pnorm). 
  by rewrite -[in X in _ = X + _](preserves_norm_cos_angle pnorm). 
set a := to j - to i0. set b := to k - to i0. set c := to l - to i0.
set a' := from j - from i0. set b' := from k - from i0. set c' := from l - from i0.
rewrite 2!crossmulD -2!scaleNr 2!linearZ /= [in LHS](normD (a *v b) (- cst *: (a *v c))).
rewrite [in RHS](normD (a' *v b') (- cst *: (a' *v c'))).
rewrite -[in RHS](_ : norm (a *v b) = norm (a' *v b')); last first.
  rewrite [in LHS]norm_crossmul [in RHS]norm_crossmul /a /b /a' /b' 2!pnorm.
    by rewrite [in RHS](preserves_cos_sin_angle (preserves_norm_cos_angle pnorm)).
rewrite -[in RHS](_ : norm (- cst *: (a *v c)) = norm (- cst *: (a' *v c'))); last first.
  rewrite [in RHS]normZ [in LHS]normZ.
  rewrite [in RHS]norm_crossmul [in LHS]norm_crossmul /a /c /a' /c' 2!pnorm.
  by rewrite [in RHS](preserves_cos_sin_angle (preserves_norm_cos_angle pnorm)).
case: (ltrP cst 0) => cst0'.
  rewrite (_ : - cst = `| cst |); last by rewrite ltr0_norm.
  rewrite [in LHS]vec_angleZ; last by rewrite normr_gt0 ltr0_neq0.
  rewrite [in RHS]vec_angleZ; last by rewrite normr_gt0 ltr0_neq0.
  rewrite [in LHS](_ : vec_angle _ _ = vec_angle (a' *v b') (a' *v c')); first by reflexivity.
  apply preserve_vec_angle_crossmul2; try by rewrite pnorm ||
    (by rewrite -[in LHS](preserves_norm_cos_angle pnorm)).
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
      rewrite [in LHS]norm_crossmul [in RHS]norm_crossmul /a /b /a' /b' 2!pnorm.
      by rewrite [in RHS](preserves_cos_sin_angle (preserves_norm_cos_angle pnorm)).
    by rewrite ab'0 norm0.
  by rewrite [in LHS]mul0r 3!mul0r.
case/boolP : (a' *v c' == 0) => [/eqP|] ac'0.
  rewrite normZ (_ : norm (a *v c) = 0); last first.
    rewrite norm_crossmul -2!pnorm.
    rewrite -[in LHS](preserves_cos_sin_angle (preserves_norm_cos_angle pnorm)) -norm_crossmul.
    by apply/eqP; rewrite norm_eq0; apply/eqP.
  by rewrite [in LHS]mulr0 [in LHS]mulr0 mul0r mulr0 mulr0 mul0r.
rewrite [in RHS](cos_vec_angleNv ab'0 ac'0).
rewrite [in LHS](_ : vec_angle _ _ = vec_angle (a' *v b') (a' *v c')); first by reflexivity.
apply preserve_vec_angle_crossmul2; try 
  (by rewrite pnorm) || by rewrite -[in LHS](preserves_norm_cos_angle pnorm).
Qed.

Definition preserves_orientation n (from to : coordinate ^ n) := forall i j k l,
  let a := from i - from j in let b := from k - from j in let c := from l - from j in
  let a' := to i - to j in let b' := to k - to j in let c' := to l - to j in
  (0 <= cos (vec_angle a (b *v c))) =
  (0 <= cos (vec_angle a' (b' *v c'))).

Lemma rigid_preserves_cos_vec_angle_crossmul : 
  preserves_norm from to -> preserves_orientation from to -> forall i j k l, 
  cos (vec_angle (to i - to j) ((to k - to j) *v (to l - to j))) =
  cos (vec_angle (from i - from j) ((from k - from j) *v (from l - from j))).
Proof.
move=> pnorm porientation /= i0 j k l.
rewrite /vec_angle.
set a := to i0 - to j. set b := to k - to j. set c := to l - to j.
set a' := from i0 - from j. set b' := from k - from j. set c' := from l - from j.
rewrite [in LHS](_ : norm (a *v (b *v c)) = norm (a' *v (b' *v c'))); last first.
   apply preserve_norm_double_crossmul; try 
     (by rewrite pnorm) || (by rewrite -[in LHS](preserves_norm_cos_angle pnorm)).
suff : a *d (b *v c) = a' *d (b' *v c') by move=> Htmp; rewrite [in LHS]Htmp.
rewrite [in LHS]dotmul_cos [in RHS]dotmul_cos.
rewrite [in LHS](_ : norm a = norm a'); last by rewrite pnorm.
rewrite [in LHS](_ : norm (b *v c) = norm (b' *v c')); last first.
  rewrite [in LHS]norm_crossmul [in RHS]norm_crossmul 2!pnorm.
  by rewrite [in RHS](preserves_cos_sin_angle (preserves_norm_cos_angle pnorm)).
case/boolP : (norm a == 0) => a0.
  rewrite -pnorm in a0; by rewrite (eqP a0) mul0r [in LHS]mul0r mul0r.
case/boolP : (norm (b *v c) == 0) => bc0.
  have -> : norm (b' *v c') = 0.
    rewrite [in LHS]norm_crossmul 2!pnorm.
    move/eqP in bc0; rewrite [in LHS]norm_crossmul in bc0.
    by rewrite abs_sin (preserves_norm_cos_angle pnorm) -abs_sin.
  by rewrite mulr0 [in LHS]mul0r [in RHS]mul0r.
have : `| cos (vec_angle a (b *v c)) | = `| cos (vec_angle a' (b' *v c')) |.
  apply preserve_cos_vec_angle_crossmul; try (by rewrite pnorm) || 
    (by rewrite -[in LHS](preserves_norm_cos_angle pnorm)) || assumption.
case: (lerP 0 (cos (vec_angle a (b *v c)))) => H1.
- rewrite [in X in X = _ -> _](ger0_norm H1) => H2.
  rewrite [in LHS]H2 ger0_norm; first by reflexivity.
  by rewrite porientation.
- rewrite [in X in X = _ -> _](ltr0_norm H1) => H2.
  rewrite (ltr0_norm) in H2; last  by rewrite ltrNge porientation -ltrNge.
  move/eqP : H2; rewrite eqr_opp => /eqP Htmp; by rewrite [in LHS]Htmp.
Qed.

End technical_properties_of_rigid_transformations.

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
  by rewrite /xtriad /normalize 2!dotmulZ -from0 -from1 -to0 -to1 pnorm (preserves_dotmul pnorm).
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
  rewrite /normalize 2!dotmulZ xtriad_norm //; last by rewrite to0 to1.
  rewrite 2!dotmulZ xtriad_norm; last by rewrite from0 from1.
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
  by rewrite /normalize 2!dotmulZ pnorm -(preserves_dotmul pnorm).
rewrite linearD /= [in RHS]linearD /= 2!crossmulvN linearZ /= crossmulvv [in LHS]scaler0 subr0.
rewrite linearZ /= crossmulvv scaler0 subr0.
by rewrite [in LHS](rigid_preserves_cos_vec_angle_crossmul pnorm porientation).
Qed.

End rigid_transformation_is_homogenous_transformation.

Section chains.

Variable R : rcfType.
Definition coordinate := 'rV[R]_3.
Definition vector := 'rV[R]_3.
Definition basisType := 'M[R]_3.
Definition x_ax : basisType -> 'rV[R]_3 := row 0.
Definition y_ax : basisType -> 'rV[R]_3 := row 1%R.
Definition z_ax : basisType -> 'rV[R]_3 := row 2%:R.

Record frame := mkFrame {
  origin : coordinate ;
  basis :> basisType ;
  _ : unitmx basis }.

Lemma frame_unit (f : frame) : basis f \in GRing.unit. Proof. by case: f. Qed.

Hint Resolve frame_unit.

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
  (z_ax (frames i.-1)) _|_ (z_ax (frames i)), (x_ax (frames i.-1)).

(* coordinate in frame f *)
Inductive coor (f : frame) : Type := Coor of 'rV[R]_3.

Definition absolute_coor f (x : coor f) : 'rV[R]_3 :=
  match x with Coor v => origin f + v *m basis f end.

Definition relative_coor f (x : coordinate) : coor f :=
  Coor _ ((x - origin f) *m (basis f)^-1).

Lemma absolute_coorK f (x : coor f) : relative_coor f (absolute_coor x) = x.
Proof.
case: x => /= v.
by rewrite /relative_coor addrC addKr -mulmxA mulmxV // mulmx1.
Qed.

Lemma relative_coorK f (x : coordinate) : absolute_coor (relative_coor f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // mulmx1 addrC addrNK. Qed.

(* vector in frame f *)
Inductive vec (f : frame) : Type := Vec of 'rV[R]_3.

Definition absolute_vec f (x : vec f) : 'rV[R]_3 :=
  match x with Vec v => v *m basis f end.

Definition relative_vec f (x : vector) : vec f :=
  Vec _ (x *m (basis f)^-1).

Lemma absolute_vecK f (x : vec f) : relative_vec f (absolute_vec x) = x.
Proof. case: x => /= v. by rewrite /relative_vec -mulmxA mulmxV // mulmx1. Qed.

Lemma relative_vecK f (x : vector) : absolute_vec (relative_vec f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // mulmx1. Qed.

End chains.

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

Fact norm_e1_subproof : norm (@delta_mx R _ _ 0 0) == 1.
Proof. by rewrite norm_delta_mx. Qed.

Definition angle_axis_of (a : angle R) (v : vector) :=
  insubd (@AngleAxis (a,_) norm_e1_subproof) (a, (norm v)^-1 *: v).

Lemma aaxis_of (a : angle R) (v : vector) : v != 0 ->
  aaxis (angle_axis_of a v) = (norm v)^-1 *: v.
Proof.
move=> v_neq0 /=; rewrite /angle_axis_of /aaxis val_insubd /=.
by rewrite normZ normfV normr_norm mulVf ?norm_eq0 // eqxx.
Qed.

Lemma aangle_of (a : angle R) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

Definition symp {n} (A : 'M[R]_n) := 1/2%:R *: (A + A^T).
Definition antip {n} (A : 'M[R]_n) := 1/2%:R *: (A - A^T).

Lemma symp_antip {n} (A : 'M[R]_n) : A = symp A + antip A.
Proof.
rewrite /symp /antip -scalerDr addrCA addrK -mulr2n- scaler_nat.
by rewrite scalerA div1r mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Definition anti {n} (M : 'M[R]_n) := M = - M^T.

Definition sym {n} (M : 'M[R]_n) := M = M^T.

Lemma anti_diag {n} M (i : 'I_n) : anti M -> M i i = 0.
Proof.
rewrite /anti => /eqP; rewrite -addr_eq0 => /eqP/matrixP/(_ i i); rewrite !mxE.
by rewrite -mulr2n -mulr_natr => /eqP; rewrite mulf_eq0 pnatr_eq0 orbF => /eqP.
Qed.

Lemma trace_anti {n} (M : 'M[R]_n) : anti M -> \tr M = 0.
Proof.
move/anti_diag => m; by rewrite /mxtrace (eq_bigr (fun=> 0)) // sumr_const mul0rn.
Qed.

Definition skew_mx (w : vector) : 'M[R]_3 := - \matrix_i (w *v delta_mx 0 i).

Lemma anti_skew u : anti (skew_mx u).
Proof.
rewrite /anti; apply/matrixP => i j; rewrite !mxE -triple_prod_mat_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma skew01 u : skew_mx u 0 1 = - u 0 2%:R.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, addr0, subr0). Qed.

Lemma skew02 u : skew_mx u 0 2%:R = u 0 1%:R.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, add0r, opprK). Qed.

Lemma skew10 u : skew_mx u 1 0 = u 0 2%:R.
Proof. move: (anti_skew u) => ->; by rewrite 2!mxE skew01 opprK. Qed.

Lemma skew12 u : skew_mx u 1 2%:R = - u 0 0.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, subr0). Qed.

Lemma skew20 u : skew_mx u 2%:R 0 = - u 0 1%:R.
Proof. move: (anti_skew u) => ->; by rewrite 2!mxE skew02. Qed.

Lemma skew21 u : skew_mx u 2%:R 1 = u 0 0.
Proof. move: (anti_skew u) => ->; by rewrite 2!mxE skew12 opprK. Qed.

Definition skewij := (skew01, skew10, skew02, skew20, skew21, skew12).

Lemma skew_mxE (u w : vector) : u *m (skew_mx w) = u *v w.
Proof.
rewrite [RHS]crossmulC -crossmulvN [u]row_sum_delta -/(mulmxr _ _) !linear_sum.
apply: eq_bigr=> i _; by rewrite !linearZ /= -rowE linearN /= rowK crossmulvN.
Qed.

Definition exp_mx (phi : angle R) (w : 'M[R]_3) : 'M_3 :=
  1 + sin phi *: w + (1 - cos phi) *: w ^+ 2.

Lemma tr_exp_mx phi M : (exp_mx phi M)^T = exp_mx phi M^T.
Proof.
by rewrite /exp_mx !trmxD !linearZ /= trmx1 expr2 trmx_mul expr2.
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
move: (cos2Dsin2 phi).
rewrite -2!exprnP => /eqP; rewrite eq_sym addrC -subr_eq => /eqP <-.
rewrite -{2}(expr1n _ 2) subr_sqr -{1 3}(mulr1 (1 - cos phi)) -mulrBr -mulrDr.
rewrite opprD addrA subrr add0r -(addrC 1) -expr2 -scalerDr.
apply/eqP; rewrite scaler_eq0 sqrf_eq0 subr_eq0 eq_sym (negbTE cphi) /=.
by rewrite aM subrr.
Qed.

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

Ltac skewE := rewrite !skewij !(anti_diag _ (anti_skew _)).
Ltac simp := rewrite ?Monoid.simpm ?(mulNr,mulrN,opprK).

Lemma sqr_skew (u : 'rV[R]_3) : let a := skew_mx u in 
  a ^+ 2 = \matrix_i [eta \0 with 0 |-> (\row_j [eta \0 with 
0 |-> - u 0 2%:R ^+ 2 - u 0 1 ^+ 2, 1 |-> u 0 0 * u 0 1, 2%:R |-> u 0 0 * u 0 2%:R] j),
 1 |-> (\row_j [eta \0 with 
0 |-> u 0 0 * u 0 1, 1 |-> - u 0 2%:R ^+ 2 - u 0 0 ^+ 2, 2%:R |-> u 0 1 * u 0 2%:R] j), 
 2%:R |-> (\row_j [eta \0 with 
0 |-> u 0 0 * u 0 2%:R, 1 |-> u 0 1 * u 0 2%:R, 2%:R |-> - u 0 1%:R ^+ 2 - u 0 0 ^+ 2] j)] i.
Proof.
move=> a; apply/matrixP => i j.
rewrite !mxE /= sum3E /a.
case: ifPn => [/eqP ->|]; first rewrite [in RHS]mxE.
  case: ifPn => [/eqP ->|]; first by skewE; simp.
  rewrite ifnot0 => /orP [] /eqP -> /=; skewE; simp => //=; by rewrite mulrC.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite mxE.
  case: ifPn => [/eqP ->|]; first by skewE; simp.
  rewrite ifnot0 => /orP [] /eqP -> /=.
  by skewE; simp.
  skewE; simp => //=; by rewrite mulrC.
case: ifPn => [/eqP ->|]; first by skewE; simp.
rewrite ifnot0 => /orP [] /eqP -> /=; by skewE; simp. 
Qed.

Lemma sym_sqr_skew u : sym (skew_mx u ^+ 2).
Proof.
rewrite sqr_skew /sym; apply/matrixP => i j; rewrite !mxE /=.
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

Lemma cube_skew (u : 'rV[R]_3) : let a := skew_mx u in a ^+ 3 = - (norm u) ^+ 2 *: a.
Proof.
move=> a.
rewrite exprS sqr_skew.
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
    rewrite /a; skewE; simp => /=.
    by rewrite addrC !mulNr mulrAC -mulrA mulrC subrr.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a; skewE; simp => /=.
    rewrite -expr2 -mulrN mulrC -mulrDl; congr (_ * _).
    by rewrite opprD opprK subrK.
  rewrite -(mulrC (u 0 1)) -mulrA -mulrDr -mulNr mulrC; congr (_ * _).
  by rewrite addrC mulNr addrK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case: ifPn => [/eqP ->|].
    rewrite /a; skewE; simp => /=.
    rewrite mulrC -mulrDl -[in RHS]mulNr; congr (_ * _).
    by rewrite mulNr -expr2 addrK.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a; skewE; simp => /=.
    by rewrite -mulrA mulrC 2!mulNr -mulrBl subrr mul0r.
  rewrite -mulrA mulrC -mulrA -mulrBr mulrC; congr (_ * _).
  by rewrite opprD opprK addrCA -expr2 subrr addr0.
case: ifPn => [/eqP ->|].
  rewrite /a; skewE; simp => /=.
  rewrite -mulrN mulrC -mulrDl; congr (_ * _).
  by rewrite opprD opprK -expr2 subrK.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a; skewE; simp => /=.
  rewrite -mulrA mulrCA -mulrDr -[in RHS]mulNr [in RHS]mulrC; congr (_ * _).
  by rewrite addrC mulNr -expr2 addrK.
by rewrite -mulrA mulrCA -mulrA -mulrDr addrC mulNr subrr mulr0.
Qed.

Lemma skew_mx_non_diag (u : vector) i j (ij : i != j) : 
  skew_mx u i j = (-1)^+(odd ((i + j)%N + (i < j)%N)) * u 0 (3%:R - (i + j)).
Proof.
(*case/boolP : (i == 0) => [/eqP >|].
rewrite mxE crossmulE mxE /=.
case: ifPn => [/eqP j0|j0].
  rewrite j0 ifnot0 in ij; case/orP : ij => /eqP ->;
  by rewrite {}j0 !mxE /= !(mulr0,mulr1,mul1r,add0r,addr0,subr0,mulN1r,normrN).
case: ifPn => [/eqP j1|j1].
  rewrite j1 ifnot1 in ij; case/orP : ij => /eqP ->;
  rewrite {}j1 !mxE /= !(mulr0,mulr1,mul1r,add0r,addr0,subr0,mulN1r,normrN) //.
  congr (- u 0 _); by apply val_inj.
case: ifPn => [/eqP j2|j2].
  rewrite j2 ifnot2 in ij; case/orP : ij => /eqP ->; 
  rewrite {}j2 !mxE /= !(mulr0,mulr1,mul1r,add0r,addr0,subr0,mulN1r,normrN) //.
  congr (u 0 _); by apply val_inj.
move: (ifnot0 j); by rewrite j0 (negbTE j1) (negbTE j2).
Qed.*) Abort.

Lemma mxtrace_sqr_skew_mx u : \tr ((skew_mx u) ^+ 2) = - (2%:R * (norm u) ^+ 2).
Proof.
rewrite /mxtrace sum3E sqr_skew.
do 6 rewrite mxE /=.
rewrite -opprB opprK !addrA addrC !addrA -2!addrA.
rewrite [in RHS]mulr2n [in RHS]mulrDl [in RHS]opprD mul1r; congr (_ + _).
  rewrite -opprB opprK; congr (- _).
  by rewrite addrC addrA -dotmulvv dotmulE sum3E -!expr2.
rewrite -opprB -opprD opprK; congr (- _).
by rewrite addrC -addrA addrCA addrA  -dotmulvv dotmulE sum3E -!expr2.
Qed.

Lemma tr_rodrigues r : \tr (rodrigues_mx r) = 1 + 2%:R * cos (aangle r).
Proof.
rewrite 2!mxtraceD !mxtraceZ /= mxtrace1.
rewrite (trace_anti (anti_skew _)) mulr0 addr0 mxtrace_sqr_skew_mx norm_axis.
rewrite (_ : - _ = - 2%:R); last by rewrite expr1n mulr1.
by rewrite mulrDl addrA mul1r -natrB // mulrC mulrN -mulNr opprK.
Qed.

Lemma rodrigues_mx_is_O r : norm (aaxis r) = 1 -> rodrigues_mx r \in 'O_3[R].
Proof.
move=> axis1.
rewrite /rodrigues_mx orthogonalE tr_exp_mx {2}anti_skew linearN /= trmxK inv_exp_mx //.
by rewrite exprS cube_skew -scalerCA -scalerAl -expr2 axis1 expr1n scaleN1r.
Qed.

Lemma det_exp_mx phi w : \det (exp_mx phi w) = 1.
Proof.
rewrite /exp_mx.
Admitted.

Lemma det_rodrigues_mx r : \det (rodrigues_mx r) = 1.
Proof.
by rewrite /rodrigues_mx det_exp_mx.
Qed.

Lemma rodrigues_mx_diag r (i : 'I_3) : 
  rodrigues_mx r i i = (aaxis r) 0 i ^+ 2 * (1 - cos (aangle r)) + cos (aangle r).
Admitted.

Lemma rodrigues_mx_non_diag r (i j : 'I_3) (ij : i != j) : 
  rodrigues_mx r i j - rodrigues_mx r j i = 
  2%:R * (aaxis r) 0 (3%:R - (i + j)) * sin (aangle r).
Admitted.

(* see table 1.2 of handbook of robotics *)
Definition angle_of_rotation (M : 'M[R]_3) := acos ((\tr M - 1) / 2%:R).
Definition axis_of_rotation (M : 'M[R]_3) : 'rV[R]_3 := 
  let phi := angle_of_rotation M in 
  (1 / (2%:R * sin phi) *: \row_i [eta \0 with 
    0 |-> M 2%:R 1 - M 1 2%:R, 1 |-> M 0 2%:R - M 2%:R 0, 2%:R |-> M 1 0 - M 0 1] i).
Definition angle_axis_of_rotation (M : 'M[R]_3) :=
  angle_axis_of (angle_of_rotation M) (axis_of_rotation M).

Lemma rodriguesE M u (HM : M \in 'SO_3[R]) :
  rodrigues u (angle_axis_of_rotation M) =
  (*(norm (axis_of_rotation M)) ^-1 *:*) homogeneous_ap u (Transform 0 HM).
Proof.
transitivity ((*(norm (axis_of_rotation M))^-1 *:*) u *m M^T); last first.
  (* TODO: lemma? *)
  rewrite homogeneous_apE.
  rewrite /htrans_of_coordinate trmx_mul trmxK.
  rewrite (_ : (Transform 0 HM)^T = (hrot_of_transform (Transform 0 HM))^T); last first.
    by rewrite /hrot_of_transform /= /hmx /= trmx0.
  rewrite hcoor_hrot_of_transform /=.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  rewrite (@cast_row_mx _ _ _ _ _ _ (u *m M^T)) //.
  by rewrite row_mxKl /= castmx_id.
(*  by rewrite scalemxAl.*)
rewrite rodriguesP.
congr (_ *m _).
have axis_M_neq0 : axis_of_rotation M != 0.
  admit.
rewrite /rodrigues_mx.
set phi := aangle _.
set w := aaxis _.
rewrite (symp_antip M^T).
suff : symp M^T = 1 + (1 - cos phi) *: skew_mx w ^ 2 /\ 
       antip M^T = sin phi *: skew_mx w.
  case=> H1 H2.
(*  by rewrite -{1}H2 addrAC H1.
split; last first.
  rewrite /anti trmxK.
  apply: (@scaler_injl _ _ 2%:R); first by rewrite unitfE pnatr_eq0.
  rewrite scalerA mul1r mulrV ?scale1r; last by rewrite unitfE pnatr_eq0.
  rewrite scalerA; apply/matrixP => i j.
  rewrite 3![in LHS]mxE [in RHS]mxE.
  case/boolP : (i == 0) => i0.
    case/boolP : (j == 0) => j0.
      by rewrite (eqP i0) (eqP j0) subrr skew_mx_diag mulr0.
    case/boolP : (j == 1) => j1.
      rewrite (eqP i0) (eqP j1) skew_mx_non_diag //= expr0 [in RHS]mul1r.
      rewrite /w.
      admit.
    case/boolP : (j == 2%:R) => j2.
      admit.
    admit.
  admit.
rewrite /sym trmxK.
apply: (@scaler_injl _ _ 2%:R); first by rewrite unitfE pnatr_eq0.
rewrite scalerA mul1r mulrV ?scale1r; last by rewrite unitfE pnatr_eq0.
rewrite scalerDr scalerA.
apply/matrixP => i j.
rewrite 2![in LHS]mxE.
rewrite [in RHS]mxE.
rewrite 2![in X in _ = X + _]mxE.
rewrite [in X in _ = _ + X]mxE.
case/boolP : (i == 0) => i0.
  case/boolP : (j == 0) => j0.
    rewrite (eqP i0) (eqP j0) skew_mx2_diag0 mulr1.
    rewrite /w {2}/axis_of_rotation -/phi.
    rewrite !mxE /= -/phi.

    admit.
  admit.
admit.*)
Abort.

End Rodrigues.

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