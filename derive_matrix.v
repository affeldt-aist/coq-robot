(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import realalg complex fingroup perm.
From mathcomp Require Import boolp reals Rstruct classical_sets signed.
From mathcomp Require Import topology normedtype landau forms derive.
From mathcomp Require Import functions.
Require Import ssr_ext euclidean rigid skew.

(******************************************************************************)
(*                  Derivatives of time-varying matrices                      *)
(*                                                                            *)
(*    derive1mx M(t) == the derivative matrix of M(t)                         *)
(*      ang_vel_mx M == angular velocity matrix of M(t) 　　　　　　　　　　　　  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Lemma mx_lin1N (R : ringType) n (M : 'M[R]_n) :
  mx_lin1 (- M) = -1 \*: mx_lin1 M :> ( _ -> _).
Proof. by rewrite funeqE => v /=; rewrite scaleN1r mulmxN. Qed.

Lemma mxE_funeqE (R : realFieldType) (V W : normedModType R)
    n m (f : V -> 'I_n -> 'I_m -> W) i j :
  (fun x => (\matrix_(i < n, j < m) (f x i j)) i j) =
  (fun x => f x i j).
Proof. by rewrite funeqE => ?; rewrite mxE. Qed.

Section derive_mx.

Variable (R : realFieldType) (V W : normedModType R).

Definition derivable_mx m n (M : R -> 'M[W]_(m, n)) t v :=
  forall i j, derivable (fun x : R^o => (M x) i j) t v.

Definition derive1mx m n (M : R -> 'M[W]_(m, n)) := fun t =>
  \matrix_(i < m, j < n) (derive1 (fun x => M x i j) t : W).

Lemma derive1mxE m n t (f : 'I_m -> 'I_n -> R -> W) :
  derive1mx (fun x => \matrix_(i, j) f i j x) t =
  \matrix_(i, j) (derive1 (f i j) t : W).
Proof.
rewrite /derive1mx; apply/matrixP => ? ?; rewrite !mxE; congr (derive1 _ t).
rewrite funeqE => ?; by rewrite mxE.
Qed.

Variables m n : nat.
Implicit Types M N : R -> 'M[W]_(m, n).

Lemma derivable_mxD M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derivable_mx (fun x => M x + N x) t 1.
Proof.
move=> Hf Hg a b. evar (f1 : R -> W). evar (f2 : R -> W).
rewrite (_ : (fun x => _) = f1 + f2); last first.
  rewrite funeqE => x; rewrite -[RHS]/(f1 x + f2 x) mxE /f1 /f2; reflexivity.
rewrite {}/f1 {}/f2; exact: derivableD.
Qed.

Lemma derivable_mxN M t : derivable_mx M t 1 ->
  derivable_mx (fun x => - M x) t 1.
Proof.
move=> HM a b.
rewrite (_ : (fun x => _) = (fun x => - (M x a b))); first exact: derivableN.
by rewrite funeqE => ?; rewrite mxE.
Qed.

Lemma derivable_mxB M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derivable_mx (fun x => M x - N x) t 1.
Proof. move=> Hf Hg; apply derivable_mxD => //; exact: derivable_mxN. Qed.

Lemma trmx_derivable M t v :
  derivable_mx M t v = derivable_mx (fun x => (M x)^T) t v.
Proof.
rewrite propeqE; split => [H j i|H i j].
by rewrite (_ : (fun _ => _) = (fun x => M x i j)) // funeqE => z; rewrite mxE.
by rewrite (_ : (fun _ => _) = (fun x => (M x)^T j i)) // funeqE => z; rewrite mxE.
Qed.

Lemma derivable_mx_row M t i :
  derivable_mx M t 1 -> derivable_mx (row i \o M) t 1.
Proof.
move=> H a b.
by rewrite (_ : (fun _ => _) = (fun x => (M x) i b)) // funeqE => z; rewrite mxE.
Qed.

Lemma derivable_mx_col M t i :
  derivable_mx M t 1 -> derivable_mx (trmx \o col i \o M) t 1.
Proof.
move=> H a b.
by rewrite (_ : (fun _ => _) = (fun x => (M x) b i)) // funeqE => z; rewrite 2!mxE.
Qed.

Lemma derivable_mx_cst (P : 'M[W]_(m, n)) t : derivable_mx (cst P) t 1.
Proof. move=> a b; by rewrite (_ : (fun x : R => _) = cst (P a b)). Qed.

Lemma derive1mx_cst (P : 'M[W]_(m, n)) : derive1mx (cst P) = cst 0.
Proof.
rewrite /derive1mx funeqE => t; apply/matrixP => i j; rewrite !mxE.
by rewrite (_ : (fun x : R => _) = (cst (P i j))) // derive1_cst.
Qed.

Lemma derive1mx_tr M t : derive1mx (trmx \o M) t = (derive1mx M t)^T.
Proof.
apply/matrixP => i j; rewrite !mxE.
by rewrite (_ : (fun _ => _) = (fun t => M t j i)) // funeqE => ?; rewrite mxE.
Qed.

Lemma derive1mxD M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derive1mx (M + N) t = derive1mx M t + derive1mx N t.
Proof.
move=> Hf Hg; apply/matrixP => a b; rewrite /derive1mx !mxE.
rewrite (_ : (fun _ => _) = (fun x => M x a b) \+ fun x => N x a b); last first.
  by rewrite funeqE => ?; rewrite mxE.
by rewrite derive1E deriveD 2?{1}derive1E.
Qed.

Lemma derive1mxN M t : derivable_mx M t 1 -> derive1mx (- M) t = - derive1mx M t.
Proof.
move=> Hf; apply/matrixP => a b.
rewrite !mxE [in RHS]derive1E -deriveN; last by [].
by rewrite -derive1E; f_equal; rewrite funeqE => x; rewrite mxE.
Qed.

Lemma derive1mxB M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derive1mx (M - N) t = derive1mx M t - derive1mx N t.
Proof.
by move=> Hf Hg; rewrite derive1mxD ?derive1mxN; last by exact: derivable_mxN.
Qed.

End derive_mx.

Section derive_mx_R.

Variables (R : realFieldType) (m n k : nat).

Lemma derivable_mxM (f : R -> 'M[R^o]_(m, k)) (g : R -> 'M[R^o]_(k, n)) t :
  derivable_mx f t 1 -> derivable_mx g t 1 -> derivable_mx (fun x => f x *m g x) t 1.
Proof.
move=> Hf Hg a b. evar (f1 : 'I_k -> R^o -> R^o).
rewrite (_ : (fun x => _) = (\sum_i f1 i)); last first.
  rewrite funeqE => t'; rewrite mxE fct_sumE; apply: eq_bigr => k0 _.
  rewrite /f1; reflexivity.
rewrite {}/f1; apply: derivable_sum => k0.
evar (f1 : R^o -> R). evar (f2 : R -> R).
rewrite (_ : (fun t' => _) = f1 * f2); last first.
  rewrite funeqE => t'; rewrite -[RHS]/(f1 t' * f2 t') /f1 /f2; reflexivity.
rewrite {}/f1 {}/f2; exact: derivableM.
Qed.

End derive_mx_R.

Section derive_mx_SE.

Variables (R : rcfType) (M : R -> 'M[R^o]_4).

Lemma derivable_rot_of_hom : (forall t, derivable_mx M t 1) ->
  forall x, derivable_mx (@rot_of_hom _ \o M) x 1.
Proof.
move=> H x i j.
rewrite (_ : (fun _ => _) = (fun y => (M y) (lshift 1 i) (lshift 1 j))); last first.
  rewrite funeqE => y; by rewrite !mxE.
exact: H.
Qed.

Lemma derive1mx_SE : (forall t, M t \in 'SE3[R]) ->
  forall t, derive1mx M t = block_mx
    (derive1mx (@rot_of_hom [rcfType of R^o] \o M) t) 0
    (derive1mx (@trans_of_hom [rcfType of R^o] \o M) t) 0.
Proof.
move=> MSE t.
rewrite block_mxEh.
rewrite {1}(_ : M = (fun x => hom (rot_of_hom (M x)) (trans_of_hom (M x)))); last first.
  rewrite funeqE => x; by rewrite -(SE3E (MSE x)).
apply/matrixP => i j.
rewrite 2!mxE; case: splitP => [j0 jj0|j0 jj0].
  rewrite (_ : j = lshift 1 j0); last exact/val_inj.
  rewrite mxE; case: splitP => [i1 ii1|i1 ii1].
    rewrite (_ : i = lshift 1 i1); last exact/val_inj.
    rewrite mxE; congr (derive1 _ t); rewrite funeqE => x.
    by rewrite /hom (block_mxEul _ _ _ _ i1 j0).
  rewrite (_ : i = rshift 3 i1); last exact/val_inj.
  rewrite mxE; congr (derive1 _ t); rewrite funeqE => x.
  by rewrite /hom (block_mxEdl (rot_of_hom (M x))).
rewrite (_ : j = rshift 3 j0) ?mxE; last exact/val_inj.
rewrite (ord1 j0).
case: (@splitP 3 1 i) => [i0 ii0|i0 ii0].
  rewrite (_ : i = lshift 1 i0); last exact/val_inj.
  rewrite (_ : (fun _ => _) = (fun=> 0)) ?derive1_cst ?mxE //.
  rewrite funeqE => x; by rewrite /hom (block_mxEur (rot_of_hom (M x))) mxE.
rewrite (_ : i = rshift 3 i0); last exact/val_inj.
rewrite (_ : (fun _ => _) = (fun=> 1)) ?derive1_cst // (ord1 i0) ?mxE //.
by rewrite funeqE => x; rewrite /hom (block_mxEdr (rot_of_hom (M x))) mxE.
Qed.

End derive_mx_SE.

Section row_belast.

(* TODO: move? *)
Definition row_belast {R : ringType} n (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \row_(i < n) (v ``_ (widen_ord (leqnSn n) i)).

(* TODO: move? *)
Lemma row_belast_last (R : ringType) n (r : 'rV[R]_n.+1) H :
  r = castmx (erefl, H) (row_mx (row_belast r) (r ``_ ord_max)%:M).
Proof.
apply/rowP => i; rewrite castmxE mxE.
case: fintype.splitP => /= [j Hj|[] [] //= ? ni]; rewrite mxE /=.
  congr (_ ``_ _); exact: val_inj.
rewrite mulr1n; congr (_ ``_ _); apply val_inj; by rewrite /= ni addn0.
Qed.

Lemma derivable_row_belast (R : realFieldType) n (u : R -> 'rV[R^o]_n.+1) (t : R) (v : R):
  derivable_mx u t v -> derivable_mx (fun x => row_belast (u x)) t v.
Proof.
move=> H i j; move: (H ord0 (widen_ord (leqnSn n) j)) => {H}.
set f := fun _ => _. set g := fun _ => _.
by rewrite (_ : f = g) // funeqE => x; rewrite /f /g mxE.
Qed.

Lemma dotmul_belast {R : realFieldType} n (u : 'rV[R]_n.+1) (v1 : 'rV[R]_n) v2 H :
  u *d castmx (erefl 1%nat, H) (row_mx v1 v2) =
    u *d castmx (erefl 1%nat, H) (row_mx v1 0%:M) +
    u *d castmx (erefl 1%nat, H) (row_mx 0 v2).
Proof.
rewrite -dotmulDr; congr dotmul; apply/matrixP => i j; rewrite !(castmxE,mxE) /=.
case: fintype.splitP => [k /= jk|[] [] // ? /= jn]; by rewrite !(mxE,addr0,add0r,mul0rn).
Qed.

Lemma derive1mx_dotmul_belast (R : realFieldType) n (u v : R^o -> 'rV[R^o]_n.+1) t :
  let u' x := row_belast (u x) in let v' x := row_belast (v x) in
  u' t *d derive1mx v' t + (u t)``_ord_max *: derive (fun x => (v x)``_ord_max) t 1 =
  u t *d derive1mx v t.
Proof.
move=> u' v'.
rewrite (row_belast_last (derive1mx v t)) ?addn1 // => ?.
rewrite dotmul_belast; congr (_ + _).
  rewrite 2!dotmulE [in RHS]big_ord_recr /=.
  rewrite castmxE mxE /=; case: fintype.splitP => [j /= /eqP/negPn|j _].
    by rewrite (gtn_eqF (ltn_ord j)).
  rewrite !mxE (_ : _ == _); last by apply/eqP/val_inj => /=; move: j => [[] ?].
  rewrite mulr0 addr0; apply/eq_bigr => i _; rewrite castmxE !mxE; congr (_ * _).
  case: fintype.splitP => [k /= ik|[] [] //= ?]; rewrite !mxE.
    f_equal.
    rewrite funeqE => x; rewrite /v' !mxE; congr ((v _) _ _); by apply/val_inj.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
apply/esym.
rewrite dotmulE big_ord_recr /= (eq_bigr (fun=> 0)); last first.
  move=> i _.
  rewrite !castmxE !mxE; case: fintype.splitP => [j /= ij| [] [] //= ?].
    by rewrite mxE mulr0.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
rewrite sumr_const mul0rn add0r castmxE /=; congr (_ * _); rewrite !mxE.
case: fintype.splitP => [j /= /eqP/negPn | [] [] //= ? Hn].
  by rewrite (gtn_eqF (ltn_ord j)).
by rewrite mxE derive1E (_ : _ == _).
Qed.

End row_belast.

(* TODO: could be derived from more generic lemmas about bilinearity in derive.v? *)
Section product_rules.

Lemma derive1mx_dotmul (R : realFieldType) n (u v : R^o -> 'rV[R^o]_n) (t : R^o) :
  derivable_mx u t 1 -> derivable_mx v t 1 ->
  derive1 (fun x => u x *d v x : R^o) t =
  derive1mx u t *d v t + u t *d derive1mx v t.
Proof.
move=> U V.
evar (f : R -> R); rewrite (_ : (fun x : R => u x *d v x : R^o) = f); last first.
  rewrite funeqE => x /=; exact: dotmulE.
rewrite derive1E {}/f.
set f := fun i : 'I__ => fun x => ((u x) ``_ i * (v x) ``_ i).
rewrite (_ : (fun _ : R => _) = \sum_(k < _) f k); last first.
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite derive_sum; last by move=> ?; exact: derivableM (U _ _) (V _ _).
rewrite {}/f.
elim: n u v => [|n IH] u v in U V *.
  rewrite big_ord0 (_ : v t = 0) ?dotmulv0 ?add0r; last by apply/rowP => [[]].
  rewrite (_ : u t = 0) ?dotmul0v //; by apply/rowP => [[]].
rewrite [LHS]big_ord_recr /=.
set u' := fun x => row_belast (u x). set v' := fun x => row_belast (v x).
transitivity (derive1mx u' t *d v' t + u' t *d derive1mx v' t +
    derive (fun x => (u x)``_ord_max * (v x)``_ord_max) t 1).
  rewrite -(IH _ _ (derivable_row_belast U) (derivable_row_belast V)).
  apply: f_equal2; last by [].
  apply eq_bigr => i _; congr (derive _ t 1).
  by rewrite funeqE => x; rewrite !mxE.
rewrite (deriveM (U _ _) (V _ _)) /= -!addrA addrC addrA.
rewrite -(addrA (_ + _)) [in RHS]addrC derive1mx_dotmul_belast; congr (_ + _).
by rewrite [in RHS]dotmulC -derive1mx_dotmul_belast addrC dotmulC.
Qed.

Lemma derive1mxM (R : realFieldType) n m p (M : R -> 'M[R^o]_(n, m))
  (N : R^o -> 'M[R^o]_(m, p)) (t : R^o) :
  derivable_mx M t 1 -> derivable_mx N t 1 ->
  derive1mx (fun t => M t *m N t) t =
    derive1mx M t *m N t + M t *m (derive1mx N t).
Proof.
move=> HM HN; apply/matrixP => i j; rewrite ![in LHS]mxE.
rewrite (_ : (fun x => _) = fun x => \sum_k (M x) i k * (N x) k j); last first.
  by rewrite funeqE => x; rewrite !mxE.
rewrite (_ : (fun x => _) =
    fun x => (row i (M x)) *d (col j (N x))^T); last first.
  rewrite funeqE => z; rewrite dotmulE; apply eq_bigr => k _.
  by rewrite 3!mxE.
rewrite (derive1mx_dotmul (derivable_mx_row HM) (derivable_mx_col HN)).
by rewrite [in RHS]mxE; congr (_  + _); rewrite [in RHS]mxE dotmulE;
   apply/eq_bigr => /= k _; rewrite !mxE; apply: f_equal2;
   try by congr (@derive1 _ [normedModType R of R^o] _ t);
          rewrite funeqE => z; rewrite !mxE.
Qed.

Lemma derive1mx_crossmul (R : realFieldType) (u v : R -> 'rV[R^o]_3) t :
  derivable_mx u t 1 -> derivable_mx v t 1 ->
  derive1mx (fun x => (u x *v v x) : 'rV[R^o]_3) t =
  derive1mx u t *v v t + u t *v derive1mx v t.
Proof.
move=> U V.
evar (f : R -> 'rV[R]_3); rewrite (_ : (fun x : R => _) = f); last first.
  rewrite funeqE => x; exact: crossmulE.
rewrite {}/f {1}/derive1mx; apply/rowP => i; rewrite mxE derive1E.
rewrite (mxE_funeqE (fun x : R^o => _)) /= mxE 2!crossmulE !{1}[in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=];
  rewrite ?derive1E (deriveD (derivableM (U _ _) (V _ _))
    (derivableN (derivableM (U _ _) (V _ _))));
  rewrite (deriveN (derivableM (U _ _) (V _ _))) 2!(deriveM (U _ _) (V _ _));
  rewrite addrCA -!addrA; congr (_ + (_ + _)); by [ rewrite mulrC |
  rewrite opprD addrC; congr (_ + _); rewrite mulrC ].
Qed.

End product_rules.

Section cross_product_matrix.
Import rv3LieAlgebra.Exports.

Lemma differential_cross_product (R : realFieldType) (v : 'rV[R^o]_3) y :
  'd (crossmul v) y = mx_lin1 \S( v ) :> (_ -> _).
Proof.
rewrite (_ : crossmul v = (fun x => x *m \S( v ))); last first.
  by rewrite funeqE => ?; rewrite -spinE.
rewrite (_ : mulmx^~ \S(v) = mulmxr_linear 1 \S(v)); last by rewrite funeqE.
rewrite diff_lin //= => x.
suff : differentiable (mulmxr \S(v)) (x : 'rV[R^o]_3).
  by move/differentiable_continuous.
rewrite (_ : mulmxr \S(v) = (fun z => \sum_i z``_i *: row i \S(v))); last first.
  rewrite funeqE => z; by rewrite -mulmx_sum_row.
set f := fun (i : 'I_3) (z : 'rV_3) => z``_i *: row i \S(v) : 'rV_3.
rewrite (_ : (fun _ => _) = \sum_i f i); last by rewrite funeqE => ?; by rewrite fct_sumE.
apply: differentiable_sum => i.
exact/differentiableZl/differentiable_coord.
Qed.

Lemma differential_cross_product2 (R : realFieldType) (v y : 'rV[R^o]_3) :
  'd (fun x : 'rV[R^o]_3 => x *v v) y = -1 \*: mx_lin1 \S( v ) :> (_ -> _).
Proof.
transitivity ('d (crossmul (- v)) y); last first.
  by rewrite differential_cross_product spinN mx_lin1N.
congr diff.
by rewrite funeqE => /= u; rewrite lieC linearNl.
Qed.

End cross_product_matrix.

(* [sciavicco] p.80-81 *)
Section derivative_of_a_rotation_matrix.

Variables (R : realFieldType) (M : R -> 'M[R^o]_3).

Definition ang_vel_mx t : 'M_3 := (M t)^T * derive1mx M t.

Definition body_ang_vel_mx t : 'M_3 := derive1mx M t *m (M t)^T.

(* angular velocity (a free vector) *)
Definition ang_vel t := unspin (ang_vel_mx t).

Hypothesis MO : forall t, M t \is 'O[ [ringType of R] ]_3.
Hypothesis derivable_M : forall t, derivable_mx M t 1.

Lemma ang_vel_mx_is_so t : ang_vel_mx t \is 'so[ [ringType of R] ]_3.
Proof.
have : (fun t => (M t)^T * M t) = cst 1.
  rewrite funeqE => x; by rewrite -orthogonal_inv // mulVr // orthogonal_unit.
move/(congr1 (fun f => derive1mx f t)); rewrite derive1mx_cst -[cst 0 _]/(0).
rewrite derive1mxM // -?trmx_derivable // derive1mx_tr.
move=> /eqP; rewrite addr_eq0 => /eqP H.
by rewrite antiE /ang_vel_mx trmx_mul trmxK H opprK.
Qed.

Lemma ang_vel_mxE t : ang_vel_mx t = \S( ang_vel t).
Proof. by rewrite /ang_vel unspinK // ang_vel_mx_is_so. Qed.

(* [sciavicco] eqn 3.7 *)
Lemma derive1mx_ang_vel t : derive1mx M t = M t * ang_vel_mx t.
Proof.
move: (ang_vel_mx_is_so t); rewrite antiE -subr_eq0 opprK => /eqP.
rewrite {1 2}/ang_vel_mx trmx_mul trmxK => /(congr1 (fun x => (M t) * x)).
rewrite mulr0 mulrDr !mulrA -{1}(orthogonal_inv (MO t)).
rewrite divrr ?orthogonal_unit // mul1r.
move=> /eqP; rewrite addr_eq0 => /eqP {1}->.
rewrite -mulrA -mulrN -mulrA; congr (_ * _).
move: (ang_vel_mx_is_so t); rewrite antiE -/(ang_vel_mx t) => /eqP ->.
by rewrite /ang_vel_mx trmx_mul trmxK mulmxE.
Qed.

Lemma derive1mx_rot (p' : 'rV[R^o]_3 (* constant vector *)) :
  let p := fun t => p' *m M t in
  forall t, derive1mx p t = ang_vel t *v p t.
Proof.
move=> p t; rewrite /p derive1mxM; last first.
  exact: derivable_M.
  rewrite /derivable_mx => i j; exact: ex_derive.
rewrite derive1mx_cst mul0mx add0r derive1mx_ang_vel mulmxA.
by rewrite -{1}(unspinK (ang_vel_mx_is_so t)) spinE.
Qed.

End derivative_of_a_rotation_matrix.
