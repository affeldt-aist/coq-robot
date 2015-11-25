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

End extra.

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

(* Lemma orthogonal_col_base M : *)
(*   (M \is 'O_n[R]) = *)
(*   [forall j, forall k, \sum_i M i j * M i k == (j == k)%:R]. *)
(* Proof. *)
(* apply/idP/'forall_'forall_eqP. *)

(* apply/idP/idP; rewrite orthogonal_alt. *)
(*   move=> HM; apply/forallP => /= j; apply/forallP => /= k. *)
(*   move: HM => /eqP/(congr1 (fun x : 'M__=> x j k)). *)
(*   rewrite !mxE => <-; apply/eqP/eq_bigr => ? _; by rewrite mxE. *)
(* move/forallP => H; apply/eqP/matrixP => a b; rewrite !mxE. *)
(* move: (H a) => /forallP /(_ b) /eqP <-. *)
(* apply/eq_bigr=> // ? _; by rewrite !mxE. *)
(* Qed. *)

(* Lemma orthogonal_col_base M : (M \is 'O_n[R]) = *)
(*   [forall j, forall k, \sum_i M i j * M i k == (j == k)%:R]. *)
(* Proof. *)
(* apply/idP/idP; rewrite orthogonal_alt. *)
(*   move=> HM; apply/forallP => /= j; apply/forallP => /= k. *)
(*   move: HM => /eqP/(congr1 (fun x : 'M__=> x j k)). *)
(*   rewrite !mxE => <-; apply/eqP/eq_bigr => ? _; by rewrite mxE. *)
(* move/forallP => H; apply/eqP/matrixP => a b; rewrite !mxE. *)
(* move: (H a) => /forallP /(_ b) /eqP <-. *)
(* apply/eq_bigr=> // ? _; by rewrite !mxE. *)
(* Qed. *)

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

Definition dotmul (u v : 'rV[R]_3) : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE (u v : 'rV[R]_3) : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma dotmulC (u v : 'rV[R]_3) : u *d v = v *d u.
Proof. by rewrite /dotmul -[_ *m _]trmxK trmx_mul !trmxK mxE. Qed.

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

Lemma crossmulC u v : crossmul u v = - crossmul v u.
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

Lemma dotmul0v u : 0 *d u = 0.
Proof. by rewrite [LHS]mxE big1 // => i; rewrite mxE mul0r. Qed.

Lemma dotmulv0 u : u *d 0 = 0.
Proof. by rewrite dotmulC dotmul0v. Qed.

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Ltac simp_ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=].
Ltac simpr := rewrite ?(mulr0,mul0r,mul1r,mulr1,addr0,add0r).

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

(* rewrite linear_sum. *)

Lemma mulmxl_crossmulr M u v : M *m (u *v v) = (u *v (M *m v)).
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

Lemma mulmxr_crossmulr r u v : r \is 'SO_3[R] ->
  (u *v v) *m r = ((u *m r) *v (v *m r)).
Proof.
Admitted.

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
  move : (_ * (_ * _)) => a.
  move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c.
  move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB.
  rewrite -addrA.
  rewrite (addrC (- b)).
  rewrite 2!addrA.
  rewrite -addrA.
  rewrite -opprB.
  rewrite opprK.
  move: (a + d) => f.
  move: (b + c) => g.
  rewrite [in RHS](addrC e).
  rewrite opprD.
  rewrite addrA.
  by rewrite addrK.
rewrite inE; case/orP => [/eqP ->|].
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite /tnth /=.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  move : (_ * (_ * _)) => a.
  move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c.
  move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB.
  rewrite -addrA.
  rewrite (addrC (- b)).
  rewrite 2!addrA.
  rewrite -addrA.
  rewrite -opprB.
  rewrite opprK.
  rewrite [in RHS](addrC e).
  rewrite [in RHS]addrA.
  rewrite (addrC d).
  move: (a + d) => f.
  rewrite [in RHS](addrC e).
  rewrite [in RHS]addrA.
  rewrite (addrC c).
  move: (b + c) => g.
  rewrite (addrC g).
  rewrite opprD.
  rewrite addrA.
  by rewrite addrK.
rewrite inE => /eqP ->.
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite /tnth /=.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  move : (_ * (_ * _)) => a.
  move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c.
  move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB.
  rewrite -addrA.
  rewrite (addrC (- b)).
  rewrite 2!addrA.
  rewrite -addrA.
  rewrite -opprB.
  rewrite opprK.
  rewrite [in RHS]addrA.
  move: (a + d) => f.
  rewrite [in RHS]addrA.
  move: (b + c) => g.
  rewrite (addrC g).
  rewrite opprD.
  rewrite addrA.
  by rewrite addrK.
Qed.

Lemma jacobi u v w : u *v (v *v w) + v *v (w *v u) + w *v (u *v v) = 0.
Proof.
(* consequence of double_crossmul *)
Admitted.

End crossmul.

Notation "*d%R" := (@dotmul _) : ring_scope.
Notation "u *d w" := (dotmul u w) (at level 40) : ring_scope.
Notation "*v%R" := (@crossmul _) : ring_scope.
Notation "u *v w" := (crossmul u w) (at level 40) : ring_scope.

Section chains.

Variable R : rcfType.
Record angle := Angle {
  expi : R[i]; 
  _ : `| expi | == 1
}.
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
  joint_angle : angle }.

Record link := mkLink {
  length : R ;
  twist : angle }.

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

Definition norm (a : coordinate) := Num.sqrt (a *d a).

Section angle.

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

Lemma sinD a b : sin (a + b) = sin a * cos b + cos a * sin b.
Proof.
rewrite {1}/sin.
Admitted.

Lemma cosD a b : cos (a + b) = cos a * cos b - sin a * sin b.
Admitted.

Definition atan (x : R) : angle := arg (x +i* 1) *~ sgz (x).
Definition asin (x : R) : angle := arg (Num.sqrt (1 - x^2) +i* x).
Definition acos (x : R) : angle := arg (x +i* Num.sqrt (1 - x^2)).

Definition pi := arg (-1).

Lemma expipi : expi pi = -1. Proof. by rewrite argK ?normrN1. Qed.

Lemma pi2 : pi *+ 2 = 0.
Proof. Admitted.

(* The following lemmas are true in specific domains only, such as
]-pi/2, pi/2[ = [pred a | cos a > 0] 
]0, pi[ = [pred a | sin a > 0] 
[-pi/2, pi/2[ = [pred a | cos a > 0] 
[0, pi] = [pred a | sin a >= 0] 
[0, pi[ = [pred a | sin a >= 0 && a != pi] 
*)

Lemma cosK : cancel acos cos.
Proof. Admitted.

Lemma acosK : cancel cos acos.
Proof. Admitted.

Lemma sinK : cancel asin sin.  
Proof. Admitted.

Lemma sin_acos x : `|x| <= 1 -> sin (acos x) = Num.sqrt (1 - x ^ 2).
Proof.
move=> Nx_le1; rewrite /sin /acos argK //; simpc; rewrite sqr_sqrtr.
  by rewrite addrC addrNK sqrtr1 //.
by rewrite subr_ge0 -[_ ^ _]real_normK ?num_real // exprn_ile1.
Qed.

Definition vec_angle (v w : vector) : angle := arg (v *d w +i* norm (v *v w)).

End angle.

Section homogeneous.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Definition displacement n (from to : coordinate ^ n) :=
  (forall i j, norm (from i - from j) = norm (to i - to j)) /\
  (forall i j k, vec_angle (from j - from i) (from k - from i) =
                 vec_angle (to j - to i) (to k - to i)).

Definition homogeneous := 'rV[R]_4.

Definition vector_homo (x : vector) := (row_mx x 0 : homogeneous).
Definition coord_homo (x : coordinate) := (row_mx x 1 : homogeneous).

Record homogeneous_trans : Type := HomogeneousTrans {
  translation : vector;
  rot : 'M[R]_3 ;
  _ : rot \in 'SO_3[R]
 }.

Coercion homogeneous_mx (T : homogeneous_trans) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx (translation T)^T 1).

Definition homogeneous_ap  (x : coordinate) (T : homogeneous_trans) : coordinate :=
  \row_(i < 3) (homogeneous_mx T *m col_mx  x^T 1 (* 0 for vectors? *) )^T 0 (inord i).

Lemma displacementP m (from to : coordinate ^ m) :
  displacement from to <->
  exists T : homogeneous_trans, 
    forall i, to i = homogeneous_ap (from i) T.
Abort.

End homogeneous.

Section Rodrigues.

Record angle_axis := AngleAxis {
  angle_axis_val : angle * vector ;
  _ : norm (angle_axis_val.2) == 1
 }.

Canonical angle_axis_subType := [subType for angle_axis_val].

Definition aangle (a : angle_axis) := (val a).1.
Definition aaxis (a : angle_axis) := (val a).2.

Lemma norm_axis a : norm (aaxis a) = 1.
Proof. by case: a => *; apply/eqP. Qed.

Lemma norm_delta_mx i : norm (delta_mx 0 i) = 1.
Proof.
rewrite /norm dotmulE (bigD1 i) ?mxE //= ?eqxx mul1r big1 ?addr0 ?sqrtr1 //.
by move=> j /negPf eq_ij; rewrite mxE eqxx eq_ij mulr0.
Qed.

Lemma norm_ge0 x : norm x >= 0.
Proof. Admitted.
Hint Resolve norm_ge0.

Lemma normr_norm x : `|norm x| = norm x.
Proof. by rewrite ger0_norm. Qed.

Lemma norm_eq0 x : (norm x == 0) = (x == 0).
Proof. rewrite sqrtr_eq0 dotmulE. Admitted.

Lemma normZ a x : norm (a *: x) = `|a| * norm x.
Proof. Admitted.

Fact norm_e1_subproof : norm (delta_mx 0 0) == 1.
Proof. by rewrite norm_delta_mx. Qed.

Definition angle_axis_of (a : angle) (v : vector) :=
  insubd (@AngleAxis (a,_) norm_e1_subproof) (a, (norm v)^-1 *: v).

Lemma aaxis_of (a : angle) (v : vector) : v != 0 ->
  aaxis (angle_axis_of a v) = (norm v)^-1 *: v.
Proof.
move=> v_neq0 /=; rewrite /angle_axis_of /aaxis val_insubd /=.
by rewrite normZ normfV normr_norm mulVf ?norm_eq0 // eqxx.
Qed.

Lemma aangle_of (a : angle) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

(* see table 1.2 of handbook of robotics *)
Definition angle_axis_of_rotation (M : 'M[R]_3) :=
  let phi := acos ((mxtrace M - 1) / 2%:R) in
  let w := 1 / (2%:R * sin phi) *: \row_i [eta \0 with 
    0 |-> M 2%:R 1 - M 1 2%:R, 1 |-> M 0 2%:R - M 2%:R 0, 2%:R |-> M 1 0 - M 0 1] i in
  angle_axis_of phi w.

Definition rodrigues (u : vector) r := let: AngleAxis phi w := r in
  cos phi *: u + (1 - cos phi) * (u *d w) *: w + sin phi *: (w *v u).

Definition skew_mx (w : vector) : 'M[R]_3 := \matrix_i (w *v delta_mx 0 i).

Lemma skew_mxE (u w : vector) : u *m (skew_mx w) = w *v u.
Proof.
rewrite [u]row_sum_delta -/(mulmxr _ _) !linear_sum; apply: eq_bigr=> i _.
by rewrite !linearZ /= -rowE rowK.
Qed.

Coercion rodrigues_mx r : 'M_3 := let: AngleAxis phi w := r in
  1 + sin phi *: skew_mx w + (1 - cos phi) *: (skew_mx w) ^ 2.

Lemma rodriguesP u r : rodrigues u r = u *m r.
Proof.
case: r => r w; rewrite /rodrigues /rodrigues_mx addrAC.
rewrite !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE.
rewrite double_crossmul.



Lemma rodriguesE M u (HM : M \in 'SO_3[R]) :
  rodrigues u (angle_axis_of_rotation M) = homogeneous_ap u (HomogeneousTrans 0 HM).
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

