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
Require Import perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Section chains.

Variable R : rcfType.
Definition ang := {c : R[i] | `| c | = 1}.
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
  angle : ang }.

Record link := mkLink {
  length : R ;
  twist : ang }.

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

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat) (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Definition dotmul (u v : 'rV[R]_3) : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE (u v : 'rV[R]_3) : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma normalvv (u v : 'rV[R]_3) : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

Lemma normalv2E m p (u : 'rV[R]_3) (A : 'M[R]_(m,3)) (B : 'M[R]_(p,3)) :
  (u _|_ A, B) = (u _|_ A) && (u _|_ B).
Proof. by rewrite !(sameP sub_kermxP eqP) tr_col_mx mul_mx_row row_mx_eq0. Qed.

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

(* find a better name *)
Definition triple_product_mat (u v w : vector) :=
  \matrix_(i < 3, j < 3) tnth [tuple u 0 j; v 0 j; w 0 j] i.

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
congr (\det _); apply/matrixP => i j; rewrite !mxE eqxx /=.
by case: i => [[|[|[]]]] ? //=; rewrite permE.
Qed.

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Ltac simp_ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=].
Ltac simpr := rewrite ?(mulr0,mul0r,mul1r,mulr1,addr0,add0r).

(* Lemma lift1E m (i : 'I_m.+2) : fintype.lift 1 i = i.+1%:R. *)
(* Proof. apply/val_inj; rewrite Zp_nat /= !modn_small 1?ltnS //. Qed. *)

Lemma crossmul_triple (u v w : 'rV[R]_3) :
  u *d (v *v w) = \det (triple_product_mat u v w).
Proof.
pose M (k : 'I_3) : 'M_3 := triple_product_mat (delta_mx 0 k) v w.
pose Mu12 := triple_product_mat (u 0 1 *: delta_mx 0 1 + u 0 2%:R *: delta_mx 0 2%:R) v w.
rewrite (@determinant_multilinear _ _ _ (M 0) Mu12 0 (u 0 0) 1) ?mul1r; last 3 first.
- apply/matrixP => i j; rewrite !mxE !eqxx /tnth /=.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
- by apply/matrixP => i j; rewrite !mxE; apply: tnth_nth.
- by apply/matrixP => i j; rewrite !mxE; apply: tnth_nth.
rewrite [\det Mu12](@determinant_multilinear _ _ _
  (M 1) (M 2%:R) 0 (u 0 1) (u 0 2%:R)); last 3 first.
- apply/matrixP => i j; rewrite !mxE !eqxx /tnth /=.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
- by apply/matrixP => i j; rewrite !mxE; apply: tnth_nth.
- by apply/matrixP => i j; rewrite !mxE; apply: tnth_nth.
by rewrite dotmulE !big_ord_recl big_ord0 addr0 /= !mxE; simp_ord.
Qed.

Lemma crossmul_normal (u v : 'rV[R]_3) : u _|_ (u *v v).
Proof.
rewrite normalvv crossmul_triple.
rewrite (determinant_alternate (oner_neq0 _)) => [|i] //.
by rewrite !mxE.
Qed.

Lemma dotmulC (u v : vector) : u *d v = v *d u.
Proof. by rewrite /dotmul -{1}[u]trmxK -trmx_mul mxE. Qed.

Lemma normal_sym (u v : vector) : u _|_ v = v _|_ u.
Proof.
rewrite !(sameP sub_kermxP eqP) -{1}[u]trmxK -trmx_mul.
by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma normalNv (u v : vector) : (- u) _|_ v = u _|_ v.
Proof. by rewrite !(sameP sub_kermxP eqP) mulNmx oppr_eq0. Qed.

Lemma normalvN (u v : vector) : u _|_ (- v) = u _|_ v.
Proof. by rewrite [LHS]normal_sym normalNv normal_sym. Qed.


Lemma common_normal_crossmul u v : (crossmul u v) _|_ u, v.
Proof.
rewrite normalv2E ![(_ *v _) _|_ _]normal_sym crossmul_normal.
by rewrite crossmulC normalvN crossmul_normal.
Qed.

(* u /\ (v + w) = u /\ v + u /\ w *)
Lemma crossmulDl : left_distributive crossmul +%R.
Proof.
move=> u v w; apply/rowP => k; rewrite 2!mxE.
pose M u := triple_product_mat (delta_mx 0 k) u w.
rewrite (@determinant_multilinear _ _ (triple_product_mat _ _ _)
        (M u) (M v) 1 1 1); first by rewrite !mul1r 2!mxE.
- by apply/rowP => j; rewrite !mxE /= !mul1r.
- by apply/matrixP=> i j; rewrite !mxE /= [_ == 1]eq_sym (negPf (neq_lift _ _)). 
- by apply/matrixP=> i j; rewrite !mxE /= [_ == 1]eq_sym (negPf (neq_lift _ _)). 
Qed.

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

Lemma crossmulE u v : (u *v v) = \row_j tnth [tuple
  u 0 1 * v 0 2%:R - u 0 2%:R * v 0 1 ;
  u 0 2%:R * v 0 0 - u 0 0 * v 0 2%:R ;
  u 0 0 * v 0 1 - u 0 1 * v 0 0] j.
Proof.
apply/rowP => i; rewrite !mxE (expand_det_row _ ord0).
rewrite !(mxE, big_ord_recl, big_ord0) !(mul0r, mul1r, addr0).
rewrite /cofactor !det_mx22 !mxE /= mul1r mulN1r opprB -signr_odd mul1r.
do !rewrite -[fintype.lift _ _]natr_Zp /=.
by case: i => [[|[|[]]]] //= ?; rewrite ?(mul1r,mul0r,add0r,addr0).
Qed.

Definition dotmul (u v : 'rV[R]_3) : R := (u *m v^T) 0 0.

Lemma double_crossmul (u v w : 'rV[R]_3) : u *v (v *v w) = (dotmul u w) *: v - (dotmul u v) *: w.
Proof.
apply/rowP => i.
have : i \in [:: ord0 ; 1 ; 2%:R].
  have : i \in enum 'I_3 by rewrite mem_enum.
  rewrite 3!enum_ordS (_ : enum 'I_0 = nil) // -enum0.
  apply eq_enum => i'; by move: (ltn_ord i').
rewrite inE; case/orP => [/eqP ->|].
  rewrite crossmul_0 crossmul_1 crossmul_2 /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 /= !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
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
  move: (a + d) => f.
  move: (b + c) => g.
  rewrite [in RHS](addrC e).
  rewrite opprD.
  rewrite addrA.
  by rewrite addrK.
rewrite inE; case/orP => [/eqP ->|].
  rewrite crossmul_1 crossmul_0 crossmul_2 /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 /= !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
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
  rewrite crossmul_2 crossmul_0 crossmul_1 /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 /= !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
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

Record homogeneous_spec (A B : frame) : Type := {
  rotation : 'M[R]_3 ;
  position : vec A }.

Definition homogeneous_mx A B (T : homogeneous_spec A B) : 'M[R]_4 :=
  row_mx (col_mx (rotation T) 0) (col_mx (let: Vec x := position T in x^T) 1).

Definition homogeneous_trans A B (T : homogeneous_spec A B) (x : vec B) : vec A :=
  Vec _ (\row_(i < 3) (homogeneous_mx T *m col_mx (let: Vec x' := x in x'^T) 1)^T 0 (inord i)).


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