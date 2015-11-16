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

Definition common_normal (u v : vector) :=
  fun w : vector => (w <= kermx (col_mx u v)^T)%MS.

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat) (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma common_normalE (u v w : vector) :
  common_normal u v w = (w *m u^T == 0) && (w *m v^T == 0).
Proof.
by rewrite /common_normal (sameP sub_kermxP eqP) tr_col_mx mul_mx_row row_mx_eq0.
Qed.

Definition common_normal_xz (i : 'I_n) :=
  common_normal (z_ax (frames i.-1)) (z_ax (frames i))(x_ax (frames i.-1)).

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
  \matrix_(i < 3, j < 3) if i == 0 then u 0 j
                         else if i == 1 then v 0 j
                         else w 0 j.

(* Definition mixed_product_mat n (u : 'I_n -> 'rV[R]_n) :=  *)
(*   \matrix_(i < n, j < n) u i ord0 j. *)

(* Definition cross_product (u : 'rV[R]_n.+1) (v : 'I_n -> 'rV[R]_n.+1) : 'rV[R]_n.+1 := *)
(*   \row_(k < n) \det (mixed_product_mat (delta_mx 0 k)). *)

Definition cross_product (u v : vector) : vector :=
  \row_(k < 3) \det (triple_product_mat (delta_mx 0 k) u v).

(*Definition cross_product (u v : vector) : vector :=
  \row_(i < 3) \det (col_mx (delta_mx (ord0 : 'I_1) i) (col_mx u v)).*)

Lemma cross_productC u v : cross_product u v = - cross_product v u.
Proof.
rewrite /cross_product; apply/rowP => i; rewrite !mxE.
set M := (X in - \det X).
transitivity (\det (row_perm (tperm (1 : 'I__) 2%:R) M)); last first.
  by rewrite row_permE detM det_perm odd_tperm /= expr1 mulN1r.
congr (\det _); apply/matrixP => a b; rewrite !mxE.
rewrite -![tperm _ _ a == _](inj_eq (@perm_inj _ (tperm (1 : 'I__) 2%:R))).
by rewrite !tpermK !permE; move: a; do !case=> //.
Qed.

Lemma cross_product_triple (u v w : 'rV[R]_3) :
  u *m (cross_product v w)^T = (\det (triple_product_mat u v w))%:M.
Proof.
pose M (k : 'I_3) : 'M_3 := triple_product_mat (delta_mx 0 k) v w.
pose o1 : 'I_3 := fintype.lift 0 0; pose o2 : 'I_3 := fintype.lift 0 (fintype.lift 0 0).
pose Mu12 := triple_product_mat (u 0 o1 *: delta_mx 0 o1 + u 0 o2 *: delta_mx 0 o2) v w.
rewrite (@determinant_multilinear _ _ _ (M 0) Mu12 0 (u 0 0) 1) ?mul1r; last 3 first.
- rewrite -!linearZ -!linearD /= scale1r.
  apply/rowP => j; rewrite !mxE !eqxx.
  by rewrite {1}[u]row_sum_delta !big_ord_recl big_ord0 !mxE !addrA addr0 -!val_eqE.
- by apply/matrixP => i j; rewrite !mxE.
- by apply/matrixP => i j; rewrite !mxE.
rewrite [\det Mu12](@determinant_multilinear _ _ _
  (M o1) (M o2) 0 (u 0 o1) (u 0 o2)); last 3 first.
- rewrite -!linearZ -!linearD /=.
  by apply/rowP => j; rewrite !mxE !eqxx.
- by apply/matrixP => i j; rewrite !mxE.
- by apply/matrixP => i j; rewrite !mxE.
rewrite mulmx_sum_row !big_ord_recl big_ord0 /=.
rewrite -!tr_col addr0 !addrA !rmorphD /=.
by congr (_ + _ + _); apply/rowP=> j0; rewrite !ord1 !mxE ?mulr1n.
Qed.

Lemma cross_product_orthogonal (u v : 'rV[R]_3) :
  u *m (cross_product u v)^T = 0.
Proof.
rewrite cross_product_triple (determinant_alternate (oner_neq0 _)) => [|i].
  by rewrite [RHS]mx11_scalar mxE.
by rewrite !mxE.
Qed.

Lemma common_normal_cross_product u v : common_normal u v (cross_product u v).
Proof.
rewrite common_normalE -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx_mul !trmxK trmx0.
rewrite andbC {1}cross_productC linearN mulmxN !cross_product_orthogonal.
by rewrite oppr0 eqxx.
Qed.

Let o1 : 'I_3 := fintype.lift 0 0.
Let o2 : 'I_3 := fintype.lift 0 (fintype.lift 0 0).

(* u /\ (v + w) = u /\ v + u /\ w *)
Lemma cross_productDl : left_distributive cross_product (fun x y => x + y).
Proof.
move=> u v w; apply/rowP => i; rewrite 2!mxE.
pose B := triple_product_mat (delta_mx 0 i) u w.
pose C := triple_product_mat (delta_mx 0 i) v w.
rewrite (@determinant_multilinear _ _ (triple_product_mat _ _ _) B C o1 1 1); last 3 first.
- apply/rowP => i'; rewrite mxE /triple_product_mat mxE /= mxE mxE.
  congr GRing.add; by rewrite mxE {}/B /triple_product_mat !mxE /= mul1r.
- apply/matrixP => i' j; rewrite !mxE /=.
  by move: (neq_lift o1 i') => /negbTE; rewrite eq_sym (val_inj o1 1) // => ->.
- apply/matrixP => i' j; rewrite !mxE /=.
  by move: (neq_lift o1 i') => /negbTE; rewrite eq_sym (val_inj o1 1) // => ->.
by rewrite 2!mul1r /cross_product 2!mxE.
Qed.

Local Notation "u ./\ w" := (cross_product u w) (at level 9).

Lemma cross_product_0 u v : (u ./\ v) 0 0 = u 0 o1 * v 0 o2 - u 0 o2 * v 0 o1.
Proof.
rewrite /cross_product !mxE (expand_det_row _ ord0) 3!big_ord_recl /= big_ord0.
rewrite !mxE /= !(mul1r, mul0r, add0r, addr0) /cofactor expr0 mul1r.
rewrite (_ : row' ord0 _ = \matrix_(i, j)
  if i == 0 then u 0 (fintype.lift 0 j) else v 0 (fintype.lift 0 j)); last first.
  apply/matrixP => i j; rewrite !mxE /=; by case: ifP.
rewrite (expand_det_row _ ord0) 2!big_ord_recl /= big_ord0 /=.
rewrite !mxE /= /cofactor /= expr0 mul1r /bump expr1 mulN1r.
rewrite (_ : row' ord0 _ = (v 0 o2)%:M); last first.
  apply/matrixP => i j; by rewrite (ord1 i) (ord1 j) !mxE /= mulr1n.
rewrite (_ : row' ord0 _ = (v 0 o1)%:M); last first.
  apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE /= mulr1n.
  congr (v 0); by apply val_inj.
by rewrite mulrN 2!det_scalar expr1 addr0 expr1.
Qed.

Lemma I20false (i : 'I_2) : i != 0 -> i = fintype.lift 0 0.
Proof.
move=> i0.
have : i \in enum 'I_2 by rewrite mem_enum.
rewrite 2!enum_ordS (_ : enum 'I_0 = nil) // -enum0; last first.
  apply eq_enum => i'; by move: (ltn_ord i').
rewrite inE (negbTE i0) /= inE; case/orP => [/eqP // |].
by rewrite enum0.
Qed.

Lemma cross_product_1 u v : (u ./\ v) 0 o1 = u 0 o2 * v 0 0 - u 0 0 * v 0 o2.
Proof.
rewrite /cross_product !mxE (expand_det_row _ ord0) 3!big_ord_recl /= big_ord0.
rewrite !mxE /= !(mul1r, mul0r, add0r, addr0) /cofactor expr1 mulN1r.
rewrite (_ : row' ord0 _ = \matrix_(i, j)
  if i == 0 then if j == 0 then u 0 0 else u 0 o2
  else if j == 0 then v 0 0 else v 0 o2); last first.
  apply/matrixP => i j; rewrite !mxE /=.
  case: ifP.
    case: ifP => [/eqP -> _| /negbT/I20false -> //].
    case: ifP => [/eqP -> | /negbT/I20false ->]; congr (u 0); by apply val_inj.
  case: ifP => [/eqP -> // | /negbT/I20false -> ].
  case: ifP => [/eqP -> _ | /negbT/I20false -> _]; congr (v 0); by apply val_inj.
rewrite (expand_det_row _ ord0) 2!big_ord_recl /= big_ord0 /=.
rewrite !mxE /= /cofactor /= expr0 mul1r /bump expr1 mulN1r.
rewrite (_ : row' ord0 _ = (v 0 o2)%:M); last first.
  apply/matrixP => i j; by rewrite (ord1 i) (ord1 j) !mxE /= mulr1n.
rewrite (_ : row' ord0 _ = (v 0 0)%:M); last first.
  apply/matrixP => i j; by rewrite (ord1 i) (ord1 j) !mxE /= mulr1n.
by rewrite mulrN 2!det_scalar expr1 addr0 expr1 opprB.
Qed.

Lemma cross_product_2 u v : (u ./\ v) 0 o2 = u 0 0 * v 0 o1 - u 0 o1 * v 0 0.
Proof.
rewrite /cross_product !mxE (expand_det_row _ ord0) 3!big_ord_recl /= big_ord0.
rewrite !mxE /= !(mul1r, mul0r, add0r, addr0) /cofactor /= expr2 mulrN1 opprK mul1r.
rewrite (_ : row' ord0 _ = \matrix_(i, j) if i == 0 then u 0 (inord j) else v 0 (inord j)); last first.
  apply/matrixP => i j; rewrite !mxE /=.
  case: ifP.
    case: ifP => [/eqP -> _| /negbT/I20false -> //].
    congr (u 0); apply val_inj => /=.
    by rewrite /bump /= addn0 add1n ltnNge -ltnS (ltn_ord j) /= add0n inordK // (ltn_trans (ltn_ord j)).
  case: ifP => [/eqP -> // | /negbT/I20false -> _].
  congr (v 0); apply val_inj => /=.
  by rewrite /bump /= addn0 add1n ltnNge -ltnS (ltn_ord j) /= add0n inordK // (ltn_trans (ltn_ord j)).
rewrite (expand_det_row _ ord0) 2!big_ord_recl /= big_ord0 /=.
rewrite !mxE /= /cofactor /= expr0 mul1r /bump expr1 mulN1r.
rewrite (_ : row' ord0 _ = (v 0 o1)%:M); last first.
  apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE /= mulr1n.
  congr (v 0); apply val_inj => /=; by rewrite inordK.
rewrite (_ : row' ord0 _ = (v 0 0)%:M); last first.
  apply/matrixP => i j; rewrite (ord1 i) (ord1 j) !mxE /= mulr1n.
  congr (v 0); apply val_inj => /=; by rewrite inordK.
rewrite mulrN 2!det_scalar expr1 addr0 expr1 leqnn addn0 /=.
congr (u 0 _ * _ - u 0 _ * _); apply val_inj => /=; by rewrite inordK.
Qed.

Definition dotmul (u v : 'rV[R]_3) : R := (u *m v^T) 0 0.

Lemma double_cross_product (u v w : 'rV[R]_3) : u ./\ (v ./\ w) = (dotmul u w) *: v - (dotmul u v) *: w.
Proof.
apply/rowP => i.
have : i \in [:: ord0 ; o1 ; o2].
  have : i \in enum 'I_3 by rewrite mem_enum.
  rewrite 3!enum_ordS (_ : enum 'I_0 = nil) // -enum0.
  apply eq_enum => i'; by move: (ltn_ord i').
rewrite inE; case/orP => [/eqP ->|].
  rewrite cross_product_0 cross_product_1 cross_product_2 /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 /= !mxE.
  rewrite -/o1 -/o2 !addr0 !mulrDl !mulrDr.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 o1)) (mulrC (w 0 o2)).
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
  rewrite cross_product_1 cross_product_0 cross_product_2 /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 /= !mxE.
  rewrite -/o1 -/o2 !addr0 !mulrDl !mulrDr.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 o1)) (mulrC (w 0 o2)).
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
  rewrite cross_product_2 cross_product_0 cross_product_1 /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 /= !mxE.
  rewrite -/o1 -/o2 !addr0 !mulrDl !mulrDr.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 o1)) (mulrC (w 0 o2)).
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