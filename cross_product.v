(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import all_ssreflect ssralg ssrint rat poly closed_field.
From mathcomp Require Import polyrcf matrix mxalgebra mxpoly zmodp perm path.
From mathcomp Require Import perm path fingroup.
Require Import ssr_ext.

(******************************************************************************)
(* This filw is wip. It contains a generalization of the cross-product.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section Normal.

Variables (F : fieldType) (n : nat).
Local Open Scope ring_scope.

Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS (at level 69).

Lemma normal_sym k m (A : 'M[F]_(k,n)) (B : 'M[F]_(m,n)) :
  A _|_ B = B _|_ A.
Proof.
rewrite !(sameP sub_kermxP eqP) -{1}[A]trmxK -trmx_mul.
by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma normalNm k m (A : 'M[F]_(k,n)) (B : 'M[F]_(m,n)) : (- A) _|_ B = A _|_ B.
Proof. by rewrite eqmx_opp. Qed.

Lemma normalmN k m (A : 'M[F]_(k,n)) (B : 'M[F]_(m,n)) : A _|_ (- B) = A _|_ B.
Proof. by rewrite ![A _|_ _]normal_sym normalNm. Qed.

Lemma normalDm k m p (A : 'M[F]_(k,n)) (B : 'M[F]_(m,n)) (C : 'M[F]_(p,n)) :
  (A + B _|_ C) = (A _|_ C) && (B _|_ C).
Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed.

Lemma normalmD  k m p (A : 'M[F]_(k,n)) (B : 'M[F]_(m,n)) (C : 'M[F]_(p,n)) :
  (A _|_ B + C) = (A _|_ B) && (A _|_ C).
Proof. by rewrite ![A _|_ _]normal_sym normalDm. Qed.

(* TODO: already defined in euclidean3.v! *)
Definition dotmul (u v : 'rV[F]_n) : F := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE (u v : 'rV[F]_n) : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma normalvv (u v : 'rV[F]_n) : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

End Normal.

Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS (at level 69).
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Section Crossproduct.

Variable (F : fieldType) (n' : nat).
Let n := n'.+1.

Definition cross (u : 'M[F]_(n',n)) : 'rV_n  :=
  \row_(k < n) \det (col_mx (@delta_mx _ 1%N _ 0 k) u).

(*Definition crossmul (u v : vector) : vector :=
  \row_(i < n) \det (col_mx (delta_mx (ord0 : 'I_1) i) (col_mx u v)).*)

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Ltac simp_ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=].
Ltac simpr := rewrite ?(mulr0,mul0r,mul1r,mulr1,addr0,add0r).

Lemma cross_multilinear (A B C : 'M_(n',n)) (i0 : 'I_n') (b c : F) :
 row i0 A = b *: row i0 B + c *: row i0 C ->
 row' i0 B = row' i0 A ->
 row' i0 C = row' i0 A -> cross A = b *: cross B + c *: cross C.
Proof.
move=> rABC rBA rCA; apply/rowP=> k; rewrite !mxE.
have bumpD (i k1 : 'I_n') : bump (bump 0 i0) i = (1 + k1)%N -> i0 != k1.
  move=> Bi; apply/eqP => i0Ek1; move: Bi; rewrite -i0Ek1.
  rewrite /bump !add1n; case: ltnP => [u0Li He|iLi0 He].
    by rewrite -He leqNgt ltnS leqnn in u0Li.
  by rewrite -ltnS -He ltnn in iLi0.
apply: (@determinant_multilinear _ _ _ _ _ (fintype.lift 0 i0));
do ?[apply/matrixP => i j; rewrite !mxE; case: splitP => //= l;
     rewrite ?ord1 ?mxE //].
- apply/rowP => i; rewrite !mxE; case: fintype.splitP; first by do 2 case.
  move=> k1 H; rewrite (_ : k1 = i0).
    by move/rowP : rABC => /(_ i); rewrite !mxE.
  apply/val_eqP/eqP=> /=.
  by rewrite /= /bump !add1n in H; case: H.
- apply/matrixP => i j; rewrite !mxE /=; case: fintype.splitP => // k1 /= H1.
  have /unlift_some[k2 k2E _] := bumpD i k1 H1.
  by move/matrixP : rBA => /(_ k2 j); rewrite !mxE k2E.
apply/matrixP => i j; rewrite !mxE /=; case: fintype.splitP => // k1 /= H1.
have /unlift_some[k2 k2E _] := bumpD i k1 H1.
by move/matrixP : rCA => /(_ k2 j); rewrite !mxE k2E.
Qed.

Lemma dot_cross (u : 'rV[F]_n) (V : 'M[F]_(n',n)) :
  u *d (cross V) = \det (col_mx u V).
Proof.
rewrite dotmulE (expand_det_row _ 0); apply: eq_bigr => k _; rewrite !mxE /=.
case: fintype.splitP => j //=; rewrite ?ord1 //= => _ {j}; congr (_ * _).
rewrite (expand_det_row _ 0) (bigD1 k) //= big1 ?addr0; last first.
  move=> i neq_ik; rewrite !mxE; case: fintype.splitP=> //= j.
  by rewrite ord1 mxE (negPf neq_ik) mul0r.
rewrite !mxE; case: fintype.splitP => //= j _; rewrite ord1 !mxE !eqxx mul1r.
rewrite !expand_cofactor; apply: eq_bigr => s s0; congr (_ * _).
apply: eq_bigr => i; rewrite !mxE.
by case: fintype.splitP => //= j'; rewrite ord1 {j'} -val_eqE => /= ->.
Qed.

Lemma dotmulC (u v : 'rV[F]_n) : u *d v = v *d u.
Proof. by rewrite /dotmul -{1}[u]trmxK -trmx_mul mxE. Qed.

Lemma crossmul_normal (A : 'M[F]_(n',n)) : A _|_ cross A.
Proof.
apply/rV_subP => v /submxP [M ->]; rewrite normalvv dot_cross; apply/det0P.
exists (row_mx (- 1) M); rewrite ?row_mx_eq0 ?oppr_eq0 ?oner_eq0 //.
by rewrite mul_row_col mulNmx mul1mx addNr.
Qed.

(* u /\ (v + w) = u /\ v + u /\ w *)
(* Lemma crossmul_linear u : linear (crossmul u). *)
(* Proof. *)
(* move=> a v w; apply/rowP => k; rewrite !mxE. *)
(* pose M w := triple_product_mat (delta_mx 0 k) u w. *)
(* rewrite (@determinant_multilinear _ _ (M _) (M v) (M w) 2%:R a 1); *)
(*   rewrite ?row'_triple_product_mat ?mul1r ?scale1r ?mxE //=. *)
(* by apply/rowP => j; rewrite !mxE. *)
(* Qed. *)

(* Canonical crossmul_is_additive u := Additive (crossmul_linear u). *)
(* Canonical crossmul_is_linear u := AddLinear (crossmul_linear u). *)

(* Definition crossmulr u := crossmul^~ u. *)

(* Lemma crossmulr_linear u : linear (crossmulr u). *)
(* Proof. *)
(* move=> a v w; rewrite /crossmulr crossmulC linearD linearZ /=. *)
(* by rewrite opprD -scalerN -!crossmulC. *)
(* Qed. *)

(* Canonical crossmulr_is_additive u := Additive (crossmulr_linear u). *)
(* Canonical crossmulr_is_linear u := AddLinear (crossmulr_linear u). *)

Lemma det_mx11 (A : 'M[F]_1) : \det A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar det_scalar. Qed.

Lemma cofactor_mx22 (A : 'M[F]_2) i j :
  cofactor A i j = (-1) ^+ (i + j) * A (i + 1) (j + 1).
Proof.
rewrite /cofactor det_mx11 !mxE; congr (_ * A _ _);
by apply/val_inj; move: i j => [[|[|?]]?] [[|[|?]]?].
Qed.

Lemma det_mx22 (A : 'M[F]_2) : \det A = A 0 0 * A 1 1 -  A 0 1 * A 1 0.
Proof.
rewrite (expand_det_row _ ord0) !(mxE, big_ord_recl, big_ord0).
rewrite !(mul0r, mul1r, addr0) !cofactor_mx22 !(mul1r, mulNr, mulrN).
by rewrite !(lift0E, add0r) /= addrr_char2.
Qed.

(* Lemma crossmulE u v : (u *v v) = \row_j [eta \0 with *)
(*   0 |-> u 0 1 * v 0 2%:R - u 0 2%:R * v 0 1, *)
(*   1 |-> u 0 2%:R * v 0 0 - u 0 0 * v 0 2%:R, *)
(*   2%:R |-> u 0 0 * v 0 1 - u 0 1 * v 0 0] j. *)
(* Proof. *)
(* apply/rowP => i; rewrite !mxE (expand_det_row _ ord0). *)
(* rewrite !(mxE, big_ord_recl, big_ord0) !(mul0r, mul1r, addr0). *)
(* rewrite /cofactor !det_mx22 !mxE /= mul1r mulN1r opprB -signr_odd mul1r. *)
(* by simp_ord; case: i => [[|[|[]]]] //= ?; rewrite ?(mul1r,mul0r,add0r,addr0). *)
(* Qed. *)

(* Lemma lin_mulmx m p p' M N (f : {linear 'M[R]_(m,p) -> 'M_(m,p')}) : *)
(*   f (M *m N) = M *m f N. *)
(* Proof. *)
(* rewrite [M]matrix_sum_delta !mulmx_suml linear_sum /=; apply: eq_bigr => i _. *)
(* rewrite !mulmx_suml linear_sum /=; apply: eq_bigr => j _. *)
(* rewrite -mul_scalar_mx -!mulmxA !mul_scalar_mx linearZ /=; congr (_ *: _). *)
(* apply/matrixP => k l; rewrite !mxE. *)


(* rewrite linear_sum. *)


(* Lemma mulmxl_crossmulr M u v : M *m (u *v v) = (u *v (M *m v)). *)
(* Proof. *)
(* by rewrite -(mul_rV_lin1 [linear of crossmul u]) mulmxA mul_rV_lin1. *)
(* Qed. *)

(* Lemma mulmxl_crossmull M u v : M *m (u *v v) = ((M *m u) *v v). *)
(* Proof. by rewrite crossmulC mulmxN mulmxl_crossmulr -crossmulC. Qed. *)

(* Lemma mulmxr_crossmulr M u v : (u *v v) *m M = (u *v (v *m M)). *)
(* Proof. *)
(* rewrite -[M]trmxK [M^T]matrix_sum_delta. *)
(* rewrite !linear_sum /=; apply: eq_bigr=> i _. *)
(* rewrite !linear_sum /=; apply: eq_bigr=> j _. *)
(* rewrite !mxE !linearZ /= trmx_delta. *)
(* rewr *)
(* rewrite -[in RHS]/(crossmulr _ _). *)
(* rewrite linear_sum /= /crossmu. *)
(* rewrite  *)

(* apply/rowP => k; rewrite !mxE. *)
(* rewrite -![_ *v _](mul_rV_lin1 [linear of crossmulr _]). *)
(* rewrite -!mulmxA. *)
(* rewrite mul_rV_lin. *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr (v * M)]). *)

(* rewrite -/(mulmxr _ _) -!(mul_rV_lin1 [linear of mulmxr M]). *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr v]). *)

(* rewrite -!/(crossmulr _ _). *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr v]). *)

(*  /mulmxr. mul_rV_lin1. *)
(* Qed. *)


(* Lemma crossmul0v u : 0 *v u = 0. *)
(* Proof. *)
(* apply/rowP=> k; rewrite !mxE; apply/eqP/det0P. *)
(* exists (delta_mx 0 1). *)
(*   apply/negP=> /eqP /(congr1 (fun f : 'M__ => f 0 1)) /eqP. *)
(*   by rewrite !mxE /= oner_eq0. *)
(* by rewrite -rowE; apply/rowP=> j; rewrite !mxE. *)
(* Qed. *)

(* Lemma crossmulv0 u : u *v 0 = 0. *)
(* Proof. by rewrite crossmulC crossmul0v oppr0. Qed. *)

(* Lemma dotmul0v u : 0 *d u = 0. *)
(* Proof. by rewrite [LHS]mxE big1 // => i; rewrite mxE mul0r. Qed. *)

(* Lemma dotmulv0 u : u *d 0 = 0. *)
(* Proof. by rewrite dotmulC dotmul0v. Qed. *)

(* Lemma double_crossmul (u v w : 'rV[R]_n) : *)
(*  u *v (v *v w) = (u *d w) *: v - (u *d v) *: w. *)
(* Proof. *)
(* have [->|u_neq0] := eqVneq u 0. *)
(*   by rewrite crossmul0v !dotmul0v !scale0r subr0. *)
(* have : exists M : 'M_n, u *m M = delta_mx 0 0. *)

(* rewrite !crossmulE; apply/rowP => i. *)
(* rewrite !dotmulE !(big_ord_recl, big_ord0, addr0) !mxE /=. *)
(* simpr; rewrite oppr0 opprB addr0. *)
(* by case: i => [[|[|[|?]]]] ? //=; simp_ord => //=; rewrite mulrC ?subrr. *)
(* Qed. *)

(* rewrite !mulrDl !mulrBr !mulrA ?opprB. *)
(* apply/rowP => i. *)
(* have : i \in [:: ord0 ; 1 ; 2%:R]. *)
(*   have : i \in enum 'I_n by rewrite mem_enum. *)
(*   rewrite n!enum_ordS (_ : enum 'I_0 = nil) // -enum0. *)
(*   apply eq_enum => i'; by move: (ltn_ord i'). *)
(* rewrite inE; case/orP => [/eqP ->|]. *)
(*   rewrite !crossmulE /dotmul !mxE. *)
(*   do 2 rewrite n!big_ord_recl big_ord0 !mxE. *)
(*   rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr. *)
(*   simp_ord. *)
(*   rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)). *)
(*   rewrite /tnth /=. *)
(*   move : (_ * (_ * _)) => a. *)
(*   move : (_ * (_ * _)) => b. *)
(*   move : (_ * (_ * _)) => c. *)
(*   move : (_ * (_ * _)) => d. *)
(*   move : (_ * (_ * _)) => e. *)
(*   rewrite opprB. *)
(*   rewrite -addrA. *)
(*   rewrite (addrC (- b)). *)
(*   rewrite 2!addrA. *)
(*   rewrite -addrA. *)
(*   rewrite -opprB. *)
(*   rewrite opprK. *)
(*   move: (a + d) => f. *)
(*   move: (b + c) => g. *)
(*   rewrite [in RHS](addrC e). *)
(*   rewrite opprD. *)
(*   rewrite addrA. *)
(*   by rewrite addrK. *)
(* rewrite inE; case/orP => [/eqP ->|]. *)
(*   rewrite !crossmulE /dotmul !mxE. *)
(*   do 2 rewrite n!big_ord_recl big_ord0 !mxE. *)
(*   rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr. *)
(*   simp_ord. *)
(*   rewrite /tnth /=. *)
(*   rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)). *)
(*   move : (_ * (_ * _)) => a. *)
(*   move : (_ * (_ * _)) => b. *)
(*   move : (_ * (_ * _)) => c. *)
(*   move : (_ * (_ * _)) => d. *)
(*   move : (_ * (_ * _)) => e. *)
(*   rewrite opprB. *)
(*   rewrite -addrA. *)
(*   rewrite (addrC (- b)). *)
(*   rewrite 2!addrA. *)
(*   rewrite -addrA. *)
(*   rewrite -opprB. *)
(*   rewrite opprK. *)
(*   rewrite [in RHS](addrC e). *)
(*   rewrite [in RHS]addrA. *)
(*   rewrite (addrC d). *)
(*   move: (a + d) => f. *)
(*   rewrite [in RHS](addrC e). *)
(*   rewrite [in RHS]addrA. *)
(*   rewrite (addrC c). *)
(*   move: (b + c) => g. *)
(*   rewrite (addrC g). *)
(*   rewrite opprD. *)
(*   rewrite addrA. *)
(*   by rewrite addrK. *)
(* rewrite inE => /eqP ->. *)
(*   rewrite !crossmulE /dotmul !mxE. *)
(*   do 2 rewrite n!big_ord_recl big_ord0 !mxE. *)
(*   rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr. *)
(*   simp_ord. *)
(*   rewrite /tnth /=. *)
(*   rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)). *)
(*   move : (_ * (_ * _)) => a. *)
(*   move : (_ * (_ * _)) => b. *)
(*   move : (_ * (_ * _)) => c. *)
(*   move : (_ * (_ * _)) => d. *)
(*   move : (_ * (_ * _)) => e. *)
(*   rewrite opprB. *)
(*   rewrite -addrA. *)
(*   rewrite (addrC (- b)). *)
(*   rewrite 2!addrA. *)
(*   rewrite -addrA. *)
(*   rewrite -opprB. *)
(*   rewrite opprK. *)
(*   rewrite [in RHS]addrA. *)
(*   move: (a + d) => f. *)
(*   rewrite [in RHS]addrA. *)
(*   move: (b + c) => g. *)
(*   rewrite (addrC g). *)
(*   rewrite opprD. *)
(*   rewrite addrA. *)
(*   by rewrite addrK. *)
(* Qed. *)

(* Lemma jacobi u v w : u *v (v *v w) + v *v (w *v u) + w *v (u *v v) = 0. *)
(* Proof. *)
(* (* consequence of double_crossmul *) *)
(* Admitted. *)

(* Record homogeneous_spec (A B : frame) : Type := { *)
(*   rotation : 'M[R]_n ; *)
(*   position : vec A }. *)

(* Definition homogeneous_mx A B (T : homogeneous_spec A B) : 'M[R]_4 := *)
(*   row_mx (col_mx (rotation T) 0) (col_mx (let: Vec x := position T in x^T) 1). *)

(* Definition homogeneous_trans A B (T : homogeneous_spec A B) (x : vec B) : vec A := *)
(*   Vec _ (\row_(i < n) (homogeneous_mx T *m col_mx (let: Vec x' := x in x'^T) 1)^T 0 (inord i)). *)


(*



  option ('rV[R]_n (* point *) * 'rV[R]_n (* vec *) ).
Admitted.

Definition intersection (o o' : 'rV[R]_n) (v v' : 'rV[R]_n) : option 'rV[R]_n.
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



(* find a better name *)
Definition cross_product_mat (u : vector ^ n) :=
  \matrix_(i < n, j < n) u i 0 j.


(* Definition triple_product_mat (u v w : vector) := *)
(*   \matrix_(i < n, j < n) if i == 0 then u 0 j *)
(*                          else if i == 1 then v 0 j *)
(*                          else w 0 j. *)

(* Definition mixed_product_mat n (u : 'I_n -> 'rV[R]_n) :=  *)
(*   \matrix_(i < n, j < n) u i ord0 j. *)

(* Definition cross_product (u : 'rV[R]_n.+1) (v : 'I_n -> 'rV[R]_n.+1) : 'rV[R]_n.+1 := *)
(*   \row_(k < n) \det (mixed_product_mat (delta_mx 0 k)). *)

Definition cross_product (u v : vector) : vector :=
  \row_(k < n) \det
   (cross_product_mat (finfun [eta delta_mx 0 with 1%:R |-> u, 2%:R |-> v])).

(*Definition cross_product (u v : vector) : vector :=
  \row_(i < n) \det (col_mx (delta_mx (ord0 : 'I_1) i) (col_mx u v)).*)

Lemma cross_productC u v : cross_product u v = - cross_product v u.
Proof.
rewrite /cross_product; apply/rowP => i; rewrite !mxE.
set M := (X in - \det X).
transitivity (\det (row_perm (tperm (1 : 'I__) 2%:R) M)); last first.
  by rewrite row_permE detM det_perm odd_tperm /= expr1 mulN1r.
congr (\det _); apply/matrixP => a b; rewrite !mxE !ffunE /=.
rewrite -![tperm _ _ a == _](inj_eq (@perm_inj _ (tperm (1 : 'I__) 2%:R))).
by rewrite !tpermK !permE; move: a; do !case=> //.
Qed.
 *)

End Crossproduct.
