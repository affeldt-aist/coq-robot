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

End extra.

Section dot_product.

Variable R : rcfType.
Implicit Types u v : 'rV[R]_3.

Definition dotmul u v : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE u v : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma dotmulE2 u v : 
  u *d v = u 0 0 * v 0 0 + u 0 1 * v 0 1 + u 0 2%:R * v 0 2%:R.
Proof.
apply/esym.
rewrite dotmulE (bigD1 ord0) //= -addrA; congr (_ + _).
rewrite (bigD1 (1 : 'I_3)) //=; congr (_ + _).
rewrite (bigD1 (inord 2)) //= (_ : inord 2 = 2%:R); last 3 first.
  by apply/eqP; rewrite -val_eqE /= inordK.
  by rewrite -val_eqE.
  by apply/eqP; rewrite -val_eqE /= inordK.
rewrite big_pred0 ?addr0 //; by case=> -[|[|[|]]].
Qed.

Lemma dotmulC u v : u *d v = v *d u.
Proof. by rewrite /dotmul -[_ *m _]trmxK trmx_mul !trmxK mxE. Qed.

Lemma dotmul0v v : 0 *d v = 0.
Proof. by rewrite [LHS]mxE big1 // => i; rewrite mxE mul0r. Qed.

Lemma dotmulv0 v : v *d 0 = 0.
Proof. by rewrite dotmulC dotmul0v. Qed.

Lemma dotmulD u v : (u + v) *d (u + v) = u *d u + (u *d v) *+ 2 + v *d v.
Proof.
rewrite {1}/dotmul trmxD mulmxDl 2!mulmxDr -!addrA mxE ; congr (_ + _).
rewrite 2!addrA mxE; congr (_ + _); by rewrite mxE {2}dotmulC.
Qed.

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

Lemma scale_dotmul (k : R) u v : (k *: u) *d v = k * (u *d v).
Proof. by rewrite /dotmul -scalemxAl !mxE. Qed.

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
  by rewrite scale_dotmul -crossmul_triple dotmul_crossmul.
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
rewrite /norm scale_dotmul dotmulC scale_dotmul mulrA. 
by rewrite sqrtrM -expr2 ?sqrtr_sqr // sqr_ge0.
Qed.

Lemma dotmulvv u : u *d u = norm u ^ 2.
Proof.
rewrite /norm [_ ^ _]sqr_sqrtr // dotmulE sumr_ge0 //.
by move=> i _; rewrite sqr_ge0.
Qed.

Lemma sqr_norm u : norm u ^+ 2 = u 0 0 ^+ 2 + u 0 1 ^+ 2 + u 0 2%:R ^+ 2.
Proof. apply/esym; by rewrite 3!expr2 /norm sqr_sqrtr ?le0dotmul // dotmulE2. Qed.

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
by rewrite -dotmulE2.
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

(* TODO: move to "extra" *)
Lemma Re_scale (x : R[i]) (k : R) : k != 0 -> Re (x / k%:C) = (Re x) / k.
Proof. 
move=> k0; case: x => a b /=.
rewrite expr0n /= addr0 mul0r -mulrN opprK mulr0 addr0.
by rewrite expr2 invrM // ?unitfE // (mulrA k) divff // mul1r.
Qed.

Fact angle0_subproof : `| 1 / `| 1 | | == 1 :> R[i].
Proof. by rewrite normr1 divr1 normr1. Qed.

Canonical angle_subType := [subType for expi].

Lemma normr_expi a : `|expi a| = 1.
Proof. by case: a => x /= /eqP. Qed.

Lemma expi_eq0 a : (expi a == 0) = false.
Proof. case: a => /= a /eqP Ha; apply/negbTE; by rewrite -normr_gt0 Ha. Qed.

Definition arg (x : R[i]) : angle :=
  insubd (Angle angle0_subproof) (x / `| x |). 

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

Lemma mul_norm_arg x : x = `|x| * expi (arg x).
Proof. 
have [x0|x_neq0] := boolP (x == 0); first by rewrite (eqP x0) normr0 mul0r.
by rewrite expi_arg // mulrC mulfVK // normr_eq0. 
Qed.

Lemma argK x : `|x| = 1 -> expi (arg x) = x.
Proof. by move=> Nx1; rewrite expi_arg ?Nx1 ?divr1 // -normr_gt0 Nx1. Qed.

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

Lemma add_Nangle x : add_angle (opp_angle x) x = (arg 1).
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

Lemma cos2Dsin2 a : (cos a)^2 + (sin a)^2 = 1.
Proof.
move: (add_Re2_Im2 (expi a)).
by rewrite normr_expi expr1n => /(congr1 (fun x => Re x)) => /= <-.
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

Lemma expipi : expi pi = -1. Proof. by rewrite argK ?normrN1. Qed.

Lemma arg1 : arg 1 = 0.
Proof. apply val_inj => /=; by rewrite argK // normr1. Qed.

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

Lemma dotmul_cos u v : u *d v = norm u * norm v * cos (vec_angle u v).
Proof.
wlog /andP[u0 v0] : u v / (u != 0) && (v != 0).
  case/boolP : (u == 0) => u0; first by rewrite (eqP u0) dotmul0v norm0 2!mul0r.
  case/boolP : (v == 0) => v0; first by rewrite (eqP v0) dotmulv0 norm0 !(mulr0,mul0r).
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

Lemma orth_preserves_vec_angle M v w : M \is 'O_3[R] ->
  vec_angle v w = vec_angle (v *m M) (w *m M).
Proof.
move=> HM.
rewrite /vec_angle orth_preserves_dotmul; last by assumption.
by rewrite -orth_preserves_norm_crossmul.
Qed.

End angle.

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

Section homogeneous.

Definition ht := 'rV[R]_4.

Definition hvect (x : vector) : ht := row_mx x 0. 

Definition hcoor (x : coordinate) : ht := row_mx x 1.

Definition coord_of_ht (x : ht) : coordinate := 
  lsubmx (castmx (erefl, esym (addn1 3)) x).

Lemma coord_of_htB a b : coord_of_ht (a - b) = coord_of_ht a - coord_of_ht b.
Proof. apply/rowP => i; by rewrite !mxE !castmxE /= esymK !cast_ord_id !mxE. Qed.

Lemma coord_of_htE (x : ht) : coord_of_ht x = \row_(i < 3) x 0 (inord i).
Proof.
apply/rowP => i; rewrite !mxE castmxE /= esymK !cast_ord_id; congr (x 0 _).
apply val_inj => /=; by rewrite inordK // (ltn_trans (ltn_ord i)).
Qed.

Record htrans : Type := HomogeneousTrans {
  translation : vector;
  rot : 'M[R]_3 ;
  _ : rot \in 'SO_3[R]
 }.

Definition rot_of_htrans (T : htrans) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx 0 1).

Definition trans_of_htrans (T : htrans) : 'M[R]_4 :=
  row_mx (col_mx 1 0) (col_mx (translation T)^T 1).

Coercion hmx (T : htrans) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx (translation T)^T 1).

Lemma hmxE (T : htrans) : T = trans_of_htrans T *m rot_of_htrans T :> 'M_4.
Proof.
rewrite /hmx /trans_of_htrans /rot_of_htrans.
rewrite (mul_mx_row (row_mx (col_mx 1 0) (col_mx (translation T)^T 1)) (col_mx (rot T) 0)).
rewrite mul_row_col mulmx0 addr0 mul_row_col mulmx0 add0r mulmx1.
by rewrite mul_col_mx mul1mx mul0mx.
Qed.

Definition htrans_of_vector (x : vector) (T : htrans) : ht :=
  (T *m (hvect x)^T)^T.

Lemma htrans_of_vectorE a T : htrans_of_vector a T = a *m row_mx (rot T)^T 0.
Proof.
rewrite /htrans_of_vector /hmx /hvect.
rewrite (tr_row_mx a) (mul_row_col (col_mx (rot T) 0)) trmxD trmx_mul.
by rewrite (tr_col_mx (rot T)) trmx_mul !trmx0 !trmxK mul0mx addr0.
Qed.

Lemma linear_htrans_of_vector T : linear (htrans_of_vector^~ T).
Proof. move=> ? ? ?; by rewrite 3!htrans_of_vectorE mulmxDl -scalemxAl. Qed.

Definition htrans_of_coordinate (x : coordinate) (T : htrans) : ht :=
  (T *m (hcoor x)^T)^T.

Lemma htrans_of_coordinateB a b T :
  htrans_of_coordinate a T - htrans_of_coordinate b T = htrans_of_vector (a - b) T.
Proof.
rewrite {1}/htrans_of_coordinate {1}/hmx {1}/hcoor.
rewrite (tr_row_mx a) trmx1 (mul_row_col (col_mx (rot T) 0)) trmxD.
rewrite mulmx1 trmx_mul trmxK (tr_col_mx (rot T)) trmx0.
rewrite (tr_col_mx (translation T)^T) trmxK trmx1.
rewrite {1}/htrans_of_coordinate {1}/hmx {1}/hcoor.
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

End homogeneous.

Section chasles.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Definition homogeneous_ap (x : coordinate) (T : htrans) : coordinate :=
  (*\row_(i < 3) (homogeneous_mx T *m col_mx  x^T 1 (* 0 for vectors? *) )^T 0 (inord i).*)
  coord_of_ht (htrans_of_coordinate x T).

Lemma homogeneous_apE x T : homogeneous_ap x T = 
  lsubmx (castmx (erefl, esym (addn1 3)) (htrans_of_coordinate x T)).
Proof.
rewrite /homogeneous_ap.
apply/rowP => i; rewrite !mxE.
by rewrite castmxE /= esymK cast_ord_id /htrans_of_coordinate !mxE.
Qed.

Lemma htrans_of_vector_preserves_norm a T :
  norm (coord_of_ht (htrans_of_vector a T)) = norm a.
Proof.
rewrite htrans_of_vectorE.
rewrite /coord_of_ht.
rewrite mul_mx_row mulmx0.
rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
rewrite (cast_row_mx _ (a *m (rot T)^T)).
rewrite row_mxKl.
rewrite castmx_id.
rewrite orth_preserves_norm // orthogonalV rotation_sub //; by case: T.
Qed.

Definition displacement n (from to : coordinate ^ n) :=
  (forall i j, norm (from i - from j) = norm (to i - to j)) /\
  (forall i j k, vec_angle (from j - from i) (from k - from i) =
                 vec_angle (to j - to i) (to k - to i)).

Lemma coord_of_ht_htrans_of_vectorE u T :
  coord_of_ht (htrans_of_vector u T) = u *m (rot T)^T.
Proof.
rewrite htrans_of_vectorE.
apply/rowP => i.
rewrite mxE castmxE /= esymK cast_ord_id mul_mx_row mulmx0.
rewrite (_ : cast_ord (addn1 3) _ = lshift 1 i); last by apply val_inj.
by rewrite (row_mxEl (u *m (rot T)^T)).
Qed.

Lemma dotmul0_scale (u v : vector) k (Hk : k != 0) : 
  (u *d (k *: v) == 0) = (u *d v == 0).
Proof.
rewrite dotmulC scale_dotmul dotmulC.
apply/idP/idP => [|/eqP ->]; last by rewrite mulr0.
rewrite mulrI_eq0 //; by apply/GRing.lregP.
Qed.

Definition normalize (v : vector) := 1 / norm v *: v.

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

Definition xtriad (a b : coordinate) := normalize (b - a).

Definition ytriad (a b c : coordinate) :=
  let X := xtriad a b in
  let y := (c - a) - ((c - a) *d X) *: X in
  normalize y.

Definition triad (a b c : coordinate) :=
  let x := xtriad a b in
  let y := ytriad a b c in
  (x, y, x *v y).

Section homo_trans_given_three_points.

Variable l1 l2 l3 r1 r2 r3 : coordinate.
Hypothesis l1l2 : l1 != l2.
Hypothesis l1l2l3 : ~~ colinear (l2 - l1) (l3 - l1).

Fact l1l3 : l1 != l3.
Proof.
by apply: contra l1l2l3 => /eqP ->; rewrite subrr /colinear crossmulv0.
Qed.

Lemma xtriad_norm : norm (xtriad l1 l2) = 1.
Proof. by rewrite /xtriad norm_normalize // subr_eq0 eq_sym. Qed.

Lemma ytriad_norm : norm (ytriad l1 l2 l3) = 1.
Proof. 
rewrite /xtriad norm_normalize // subr_eq0; apply: contra l1l2l3 => /eqP ->.
by rewrite colinear_sym {2}/xtriad /normalize scalerA scale_colinear.
Qed.

Definition angle0 := @Angle R _ (introT eqP (@normr1 _)).

Lemma angle0_arg1 : angle0 = arg 1.
Proof. apply val_inj => /=; by rewrite argK // ger0_norm // ler01. Qed.

Lemma sin_vec_angle_ge0 (u v : vector) : 0 <= sin (vec_angle u v).
Proof.
rewrite /sin.
case : (vec_angle u v) => e He.
simpl.
Admitted.

Lemma norm_crossmul (u v : vector) : norm (u *v v) = norm u * norm v * sin (vec_angle u v).
Proof.
suff /eqP : (norm (u *v v))^+2 = (norm u * norm v * sin (vec_angle u v))^+2.
  rewrite -eqr_sqrt ?sqr_ge0 // 2!sqrtr_sqr ger0_norm; last by rewrite norm_ge0.
  rewrite ger0_norm; last first.
    rewrite -mulrA mulr_ge0 // ?norm_ge0 // mulr_ge0 // ? norm_ge0 //.
    by apply sin_vec_angle_ge0.
  by move/eqP.
rewrite norm_crossmul' dotmul_cos !exprMn.
apply/eqP.
by rewrite subr_eq -mulrDr addrC cos2Dsin2 mulr1.
Admitted.

Lemma ztriad_norm : norm (xtriad l1 l2 *v ytriad l1 l2 l3) = 1.
Proof.
rewrite norm_crossmul xtriad_norm ytriad_norm 2!mul1r.
Admitted.

Lemma xytriad_ortho : xtriad l1 l2 *d ytriad l1 l2 l3 = 0.
Proof.
rewrite /= /xtriad /ytriad.
apply/eqP; rewrite dotmulC {1}/normalize dotmul0_scale; last first.
  by rewrite div1r invr_neq0 // -(normalize_eq0 _) xtriad_norm oner_neq0.
rewrite dotmulC dotmul0_scale; last first.
  by rewrite div1r invr_neq0 // -(normalize_eq0 _) ytriad_norm oner_neq0.
admit.
Admitted.

Definition rot3 : 'M_3 * 'M_3 :=
  let: (Xl, Yl, Zl) := triad l1 l2 l3 in
  let: (Xr, Yr, Zr) := triad r1 r2 r3 in
  (triple_product_mat Xl Yl Zl,
   triple_product_mat Xr Yr Zr).

Let Ml := rot3.1.
Let Mr := rot3.2.

Lemma Ml_is_ortho : Ml \is 'O_3[R].
Proof.
apply/orthogonalP.
case=> -[i0|[i1|[i2|//]]]; case=> -[j0|[j1|[j2|//]]] /=; rewrite !rowK /SimplFunDelta /=.
- by rewrite dotmulvv xtriad_norm exp1rz.
  by rewrite xytriad_ortho.
  by rewrite dotmul_crossmul crossmulvv dotmul0v.
- by rewrite dotmulC xytriad_ortho.
  by rewrite dotmulvv ytriad_norm exp1rz.
  by rewrite dotmulC -dotmul_crossmul crossmulvv dotmulv0.
- by rewrite dotmulC dotmul_crossmul crossmulvv dotmul0v.
  by rewrite -dotmul_crossmul crossmulvv dotmulv0.
  by rewrite dotmulvv ztriad_norm exp1rz.
Admitted.

Lemma Mr_is_ortho : Mr \is 'O_3[R].
Admitted.

Lemma rot3_is_ortho : Ml *m Mr^T \is 'O_3[R].
Proof. by rewrite rpredM // ?Ml_is_ortho // orthogonalV Mr_is_ortho. Qed.

Lemma rot3_is_SO : Ml *m Mr^T \is 'SO_3[R].
Proof.
rewrite rotationE rot3_is_ortho /=.
Admitted.

Definition trans3 (R : 'M_3) : vector := r1 - l1 *m R.

End homo_trans_given_three_points.

Lemma displacementP m (from to : coordinate ^ m) :
  displacement from to <->
  exists T : htrans, 
    forall i, to i = homogeneous_ap (from i) T.
Proof.
split => [|[T /= HT]]; last first.
- split => [/= m0 m1|/= m0 m1 m2].
  + rewrite 2!HT -(htrans_of_vector_preserves_norm (from m0 - from m1) T).
    by rewrite -htrans_of_coordinateB coord_of_htB.
  + rewrite 3!HT.
    rewrite /homogeneous_ap -2!coord_of_htB 2!htrans_of_coordinateB.
    rewrite 2!coord_of_ht_htrans_of_vectorE.
    rewrite -orth_preserves_vec_angle //.
    rewrite orthogonalV; apply rotation_sub; by case: T HT.
- case=> Hnorm Hangle /=.
  have m0 : 'I_m by admit.
  have m1 : 'I_m by admit.
  have m2 : 'I_m by admit.
  pose l1 := from m0. pose l2 := from m0. pose l3 := from m0.
  pose r1 := to m0. pose r2 := to m0. pose r3 := to m0.
  have l1l2 : l1 != l2 by admit.
  have l1l2l3 : ~~ colinear (l2 - l1) (l3 - l1) by admit.
  exists (let r := rot3 l1 l2 l3 r1 r2 r3 in
    HomogeneousTrans (trans3 l1 r1 r.1) (rot3_is_SO l1 l2 l3 l1l2 l1l2l3)).
  move=> m3 /=.
  admit.
Abort.

End chasles.

Section Rodrigues.

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

Definition skew_mx (w : vector) : 'M[R]_3 := \matrix_i (w *v delta_mx 0 i).

Lemma skew_mxE (u w : vector) : u *m (skew_mx w) = w *v u.
Proof.
rewrite [u]row_sum_delta -/(mulmxr _ _) !linear_sum; apply: eq_bigr=> i _.
by rewrite !linearZ /= -rowE rowK.
Qed.

Coercion rodrigues_mx r : 'M_3 :=
  let (phi, w) := (aangle r, aaxis r) in
  1 + sin phi *: skew_mx w + (1 - cos phi) *: (skew_mx w) ^ 2.

Definition rodrigues (u : vector) r := 
  let (phi, w) := (aangle r, aaxis r) in
  cos phi *: u + (1 - cos phi) * (u *d w) *: w + sin phi *: (w *v u).

Lemma rodriguesP u r : rodrigues u r = u *m r.
Proof.
rewrite /rodrigues /rodrigues_mx; set phi := aangle _; set w := aaxis _.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE.
rewrite double_crossmul dotmulvv norm_axis [_ ^ _]expr1n scale1r.
rewrite scalerBr -opprB opprD opprK -scaleNr opprB addrACA addrA.
rewrite -[u as X in X + _]scale1r -scalerDl addrCA subrr addr0.
by rewrite dotmulC scalerA.
Qed.

(* see table 1.2 of handbook of robotics *)
Definition angle_axis_of_rotation (M : 'M[R]_3) :=
  let phi := acos ((mxtrace M - 1) / 2%:R) in
  let w := 1 / (2%:R * sin phi) *: \row_i [eta \0 with 
    0 |-> M 2%:R 1 - M 1 2%:R, 1 |-> M 0 2%:R - M 2%:R 0, 2%:R |-> M 1 0 - M 0 1] i in
  angle_axis_of phi w.

Lemma rodriguesE M u (HM : M \in 'SO_3[R]) :
  rodrigues u (angle_axis_of_rotation M) =
  homogeneous_ap u (HomogeneousTrans 0 HM).
Proof.
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


End chains.
