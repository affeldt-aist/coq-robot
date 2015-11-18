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

Section crossmul.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition dotmul (u v : 'rV[R]_3) : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

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

Lemma dotmulE (u v : 'rV[R]_3) : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

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

Local Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Local Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Lemma normalvv (u v : 'rV[R]_3) : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat) (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma normalv2E m p (u : 'rV[R]_3) (A : 'M[R]_(m,3)) (B : 'M[R]_(p,3)) :
  (u _|_ A, B) = (u _|_ A) && (u _|_ B).
Proof. by rewrite !(sameP sub_kermxP eqP) tr_col_mx mul_mx_row row_mx_eq0. Qed.

Lemma crossmul_normal (u v : 'rV[R]_3) : u _|_ (u *v v).
Proof.
rewrite normalvv crossmul_triple.
rewrite (determinant_alternate (oner_neq0 _)) => [|i] //.
by rewrite !mxE.
Qed.

Lemma dotmulC (u v : vector) : u *d v = v *d u.
Proof. by rewrite /dotmul -{1}[u]trmxK -trmx_mul mxE. Qed.

Lemma normal_sym m (u v : 'M[R]_(m,3)) : u _|_ v = v _|_ u.
Proof.
rewrite !(sameP sub_kermxP eqP) -{1}[u]trmxK -trmx_mul.
by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma normalNv m (u v : 'M[R]_(m,3)) : (- u) _|_ v = u _|_ v.
Proof. by rewrite !(sameP sub_kermxP eqP) mulNmx oppr_eq0. Qed.

Lemma normalvN m (u v : 'M[R]_(m,3)) : u _|_ (- v) = u _|_ v.
Proof. by rewrite [LHS]normal_sym normalNv normal_sym. Qed.

Lemma common_normal_crossmul u v : (u *v v) _|_ u, v.
Proof.
rewrite normalv2E ![(_ *v _) _|_ _]normal_sym crossmul_normal.
by rewrite crossmulC normalvN crossmul_normal.
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

(* first tentative definition of the generalized kronecker symbol *) 
(*Definition delta (i k : seq nat) : R :=
  if (perm_eq i (in_tuple k) =P true) isn't ReflectT ik then 0
  else let s := sval (sig_eqW (tuple_perm_eqP ik)) in (-1) ^+ s *+ uniq i.

Lemma deltaC i k : delta i k = delta k i.
Proof. 
have [pik|pik] := boolP (perm_eq i k); last first.
  rewrite /delta.
  case: eqP => p; first by rewrite p in pik.
  case: eqP => p0 //; by rewrite perm_eq_sym p0 in pik.
move: (pik); rewrite -[ i]/(val (in_tuple i)) -[k]/(val (in_tuple k)).
move: (in_tuple _) (in_tuple _); rewrite (perm_eq_size pik).
move: (size k) => m {i k pik} i k. 
rewrite /delta.
rewrite !tvalK.
case: _ / (esym (size_tuple k)); case: _ / (esym (size_tuple i)) => /=.
  case: eqP => // p.
  case: eqP => // [p' pik|]; last by rewrite {1}perm_eq_sym.
case: sig_eqW => /= s k_eq.
case: sig_eqW => /= s' i_eq.
rewrite -odd_permV.
rewrite (perm_eq_uniq p).
have [i_uniq|] := boolP (uniq (val i)); last by rewrite !mulr0n.
congr (_ ^+ _ *+ _).
congr (odd_perm _).
(* apply: (mulgI s); rewrite mulgV; symmetry. *)
apply/permP => /= j.
apply/val_inj/eqP=> /=.
rewrite -(@nth_uniq _ 0%N (val k)) //=. 
Abort.
*)

Definition perm_of_2seq (T : eqType) n (si : seq T) (so : n.-tuple T) : 'S_n :=
  if (perm_eq si so =P true) isn't ReflectT ik then 1%g
  else sval (sig_eqW (tuple_perm_eqP ik)).

Lemma perm_of_2seqE n (T : eqType) (si so : n.-tuple T) (j : 'I_n) : 
  perm_eq si so -> tnth so (perm_of_2seq si so j) = tnth si j.
Proof.
rewrite /perm_of_2seq; case: eqP => // H1 H2.
case: sig_eqW => /= s; rewrite /tnth => -> /=.
by rewrite (nth_map j) ?size_enum_ord // nth_ord_enum.
Qed.

Lemma perm_of_2seqV n (T : eqType) (x0 : T) (si so : n.-tuple T) : uniq si ->
  (perm_of_2seq si so)^-1%g = perm_of_2seq so si.
Proof.
move=> uniq_si.
apply/permP => /= j.
apply/val_inj/eqP => /=.
rewrite -(@nth_uniq _ x0 (val si)) //=; last 2 first.
- by rewrite size_tuple.
- by rewrite size_tuple.
rewrite /perm_of_2seq; case: eqP => p; last first.
  case: eqP => // p0; by [rewrite perm_eq_sym p0 in p | rewrite invg1].
case: eqP => [p'|]; last by rewrite perm_eq_sym {1}p.
case: sig_eqW => /= x Hx; case: sig_eqW => /= y Hy.
rewrite {1}Hx (nth_map j); last by rewrite size_enum_ord.
rewrite nth_ord_enum permE f_iinv /tnth Hy (nth_map j); last by rewrite size_enum_ord.
rewrite nth_ord_enum /tnth; apply/eqP/set_nth_default;  by rewrite size_tuple.
Qed.

Definition delta (i k : seq nat) : R :=
  if perm_eq i k then
    let s := perm_of_2seq i (in_tuple k) in (-1) ^+ s *+ uniq i
  else 0.

Lemma deltaC i k : delta i k = delta k i.
Proof. 
have [pik|pik] := boolP (perm_eq i k); last first.
  by rewrite /delta (negPf pik) perm_eq_sym (negPf pik).
move: (pik); rewrite -[ i]/(val (in_tuple i)) -[k]/(val (in_tuple k)).
move: (in_tuple _) (in_tuple _); rewrite (perm_eq_size pik).
move: (size k) => m {i k pik} i k pik. 
rewrite /delta pik perm_eq_sym pik -odd_permV !tvalK.
case: _ / (esym (size_tuple k)); case: _ / (esym (size_tuple i)) => /=.
case/boolP : (uniq k) => uk.
  by rewrite (perm_of_2seqV O) // -(perm_eq_uniq pik) uk.
by rewrite mulr0n -(perm_eq_uniq pik) (negPf uk) mulr0n.
Qed.
  
(* Lemma lin_mulmx m p p' M N (f : {linear 'M[R]_(m,p) -> 'M_(m,p')}) : *)
(*   f (M *m N) = M *m f N. *)
(* Proof. *)
(* rewrite [M]matrix_sum_delta !mulmx_suml linear_sum /=; apply: eq_bigr => i _. *)
(* rewrite !mulmx_suml linear_sum /=; apply: eq_bigr => j _. *)
(* rewrite -mul_scalar_mx -!mulmxA !mul_scalar_mx linearZ /=; congr (_ *: _). *)
(* apply/matrixP => k l; rewrite !mxE. *)


(* rewrite linear_sum. *)


Lemma mulmxl_crossmulr M u v : M *m (u *v v) = (u *v (M *m v)).
Proof.
by rewrite -(mul_rV_lin1 [linear of crossmul u]) mulmxA mul_rV_lin1.
Qed.

Lemma mulmxl_crossmull M u v : M *m (u *v v) = ((M *m u) *v v).
Proof. by rewrite crossmulC mulmxN mulmxl_crossmulr -crossmulC. Qed.

Lemma mulmxr_crossmulr M u v : (u *v v) *m M = (u *v (v *m M)).
Proof.
rewrite -!/(crossmulr _ _).
rewrite -!(mul_rV_lin1 [linear of crossmulr v]). 
Abort.

(*
/mulmxr. mul_rV_lin1.
Qed.
*)

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
