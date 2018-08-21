From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop finset ssralg matrix.
From mathcomp Require Import interval ssrnum.

Require Import Reals.
From mathcomp.analysis Require Import boolp reals Rstruct Rbar classical_sets posnum.
From mathcomp.analysis Require Import topology hierarchy landau forms derive.

Require Import ssr_ext euclidean3 rot skew.

(* WIP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Lemma mx_lin1N (R : ringType) n (M : 'M[R]_n) :
  mx_lin1 (- M) = -1 \*: mx_lin1 M :> ( _ -> _).
Proof. rewrite funeqE => v /=; by rewrite scaleN1r mulmxN. Qed.

Section mx.

Variable (V W : normedModType R).

Lemma mxE_funeqE n m (f : V -> 'I_n -> 'I_m -> W) i j :
  (fun x => (\matrix_(i < n, j < m) (f x i j)) i j) =
  (fun x => f x i j).
Proof. by rewrite funeqE => ?; rewrite mxE. Qed.

End mx.

Lemma derive1_cst (V : normedModType R) (f : V) t : derive1 (cst f) t = 0.
Proof. by rewrite derive1E derive_val. Qed.

Section derive_mx.

Variable (V W : normedModType R).

Definition derivable_mx m n (M : R -> 'M[W]_(m, n)) t v :=
  forall i j, derivable (fun x : R^o => (M x) i j) t v.

Definition derive1mx m n (M : R -> 'M[W]_(m, n)) := fun t =>
  \matrix_(i < m, j < n) (derive1 (fun x => M x i j) t : W).

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
Proof. move=> a b; by rewrite (_ : (fun x : R^o => _) = cst (P a b)). Qed.

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
by rewrite derive1E deriveD // 2!derive1E.
Qed.

Lemma derive1mxN M t : derivable_mx M t 1 -> derive1mx (- M) t = - derive1mx M t.
Proof.
move=> Hf; apply/matrixP => a b; rewrite !mxE [in RHS]derive1E -deriveN //.
rewrite -derive1E; f_equal; rewrite funeqE => x; by rewrite mxE.
Qed.

Lemma derive1mxB M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derive1mx (M - N) t = derive1mx M t - derive1mx N t.
Proof.
move=> Hf Hg; rewrite derive1mxD // ?derive1mxN //; exact: derivable_mxN.
Qed.

End derive_mx.

Section derive_mx_R.

Variables m n k : nat.

Lemma derivable_mxM (f : R -> 'M[R^o]_(m, k)) (g : R -> 'M[R^o]_(k, n)) t :
  derivable_mx f t 1 -> derivable_mx g t 1 -> derivable_mx (fun x => f x *m g x) t 1.
Proof.
move=> Hf Hg a b. evar (f1 : 'I_k -> R^o -> R^o).
rewrite (_ : (fun x => _) = (\sum_i f1 i)); last first.
  rewrite funeqE => t'; rewrite mxE fct_sumE; apply: eq_bigr => k0 _.
  rewrite /f1; reflexivity.
rewrite {}/f1; apply derivable_sum => k0.
evar (f1 : R^o -> R^o). evar (f2 : R^o -> R^o).
rewrite (_ : (fun t' => _) = f1 * f2); last first.
  rewrite funeqE => t'; rewrite -[RHS]/(f1 t' * f2 t') /f1 /f2; reflexivity.
rewrite {}/f1 {}/f2; exact: derivableM.
Qed.

End derive_mx_R.

Section row_belast.

Definition row_belast {R : ringType} n (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \row_(i < n) (v ``_ (widen_ord (leqnSn n) i)).

Lemma row_belast_last (R : ringType) n (r : 'rV[R]_n.+1) H :
  r = castmx (erefl, H) (row_mx (row_belast r) (r ``_ ord_max)%:M).
Proof.
apply/rowP => i; rewrite castmxE mxE.
case: fintype.splitP => /= [j Hj|[] [] //= ? ni]; rewrite mxE /=.
  congr (_ ``_ _); exact: val_inj.
rewrite mulr1n; congr (_ ``_ _); apply val_inj; by rewrite /= ni addn0.
Qed.

Lemma derivable_row_belast n (u : R^o -> 'rV[R^o]_n.+1) (t : R^o) (v : R^o):
  derivable_mx u t v -> derivable_mx (fun x => row_belast (u x)) t v.
Proof.
move=> H i j; move: (H ord0 (widen_ord (leqnSn n) j)) => {H}.
set f := fun _ => _. set g := fun _ => _.
by rewrite (_ : f = g) // funeqE => x; rewrite /f /g mxE.
Qed.

Lemma dotmul_belast {R : rcfType} n (u : 'rV[R]_n.+1) (v1 : 'rV[R]_n) v2 H :
  u *d castmx (erefl 1%nat, H) (row_mx v1 v2) =
    u *d castmx (erefl 1%nat, H) (row_mx v1 0%:M) +
    u *d castmx (erefl 1%nat, H) (row_mx 0 v2).
Proof.
rewrite -dotmulDr; congr dotmul; apply/matrixP => i j; rewrite !(castmxE,mxE) /=.
case: fintype.splitP => [k /= jk|[] [] // ? /= jn]; by rewrite !(mxE,addr0,add0r,mul0rn).
Qed.

Lemma derive1mx_dotmul_belast n (u v : R^o -> 'rV[R^o]_n.+1) t :
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

Lemma derive1mx_dotmul n (u v : R^o -> 'rV[R^o]_n) (t : R^o) :
  derivable_mx u t 1 -> derivable_mx v t 1 ->
  derive1 (fun x => u x *d v x : R^o) t =
  derive1mx u t *d v t + u t *d derive1mx v t.
Proof.
move=> U V.
evar (f : R -> R); rewrite (_ : (fun x : R => _) = f); last first.
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
  congr (_ + _); apply eq_bigr => i _; congr (derive _ t 1).
  by rewrite funeqE => x; rewrite !mxE.
rewrite (deriveM (U _ _) (V _ _)) /= -!addrA addrC addrA.
rewrite -(addrA (_ + _)) [in RHS]addrC derive1mx_dotmul_belast; congr (_ + _).
by rewrite [in RHS]dotmulC -derive1mx_dotmul_belast addrC dotmulC.
Qed.

Lemma derive1mxM n m p (M : R^o -> 'M[R^o]_(n, m))
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
rewrite [in RHS]mxE; congr (_  + _); rewrite [in RHS]mxE dotmulE;
  apply/eq_bigr => /= k _; rewrite !mxE; congr (_ * _); congr (derive1 _ t);
  by rewrite funeqE => z; rewrite !mxE.
Qed.

Lemma derive1mx_crossmul (u v : R -> 'rV[R^o]_3) t :
  derivable_mx u t 1 -> derivable_mx v t 1 ->
  derive1mx (fun x => (u x *v v x) : 'rV[R^o]_3) t =
  derive1mx u t *v v t + u t *v derive1mx v t.
Proof.
move=> U V.
evar (f : R -> 'rV[R]_3); rewrite (_ : (fun x : R => _) = f); last first.
  rewrite funeqE => x; exact: crossmulE.
rewrite {}/f {1}/derive1mx; apply/rowP => i; rewrite mxE derive1E.
rewrite (mxE_funeqE (fun x : R^o => _)) /= mxE 2!crossmulE ![in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=];
  rewrite ?derive1E (deriveD (derivableM (U _ _) (V _ _))
    (derivableN (derivableM (U _ _) (V _ _))));
  rewrite (deriveN (derivableM (U _ _) (V _ _))) 2!(deriveM (U _ _) (V _ _));
  rewrite addrCA -!addrA; congr (_ + (_ + _)); by [ rewrite mulrC |
  rewrite opprD addrC; congr (_ + _); rewrite mulrC ].
Qed.

End product_rules.

Section cross_product_matrix.

Lemma coord_continuous {K : absRingType} m n i j :
  continuous (fun M : 'M[K]_(m, n) => M i j).
Proof.
move=> /= M s /= /locallyP; rewrite locally_E => -[e e0 es].
apply/locallyP; rewrite locally_E; exists e => //= N MN; exact/es/MN.
Qed.

Lemma differentiable_coord m n (M : 'M[R]_(m.+1, n.+1)) i j :
  (differentiable M) (fun N : 'M[R]_(m.+1, n.+1) => N i j : R^o).
Proof.
have @f : {linear 'M[R]_(m.+1, n.+1) -> R^o}.
  by exists (fun N : 'M[R]_(_, _) => N i j); eexists; move=> ? ?; rewrite !mxE.
rewrite (_ : (fun _ => _) = f) //; exact/linear_differentiable/coord_continuous.
Qed.

Lemma differential_cross_product (v : 'rV[R]_3) y :
  'd_y (crossmul v) = mx_lin1 \S( v ) :> (_ -> _).
Proof.
rewrite (_ : crossmul v = (fun x => x *m \S( v ))); last first.
  by rewrite funeqE => ?; rewrite -spinE.
rewrite (_ : mulmx^~ \S(v) = mulmxr_linear 1 \S(v)); last by rewrite funeqE.
rewrite diff_lin //= => x.
suff : differentiable x (mulmxr \S(v)) by move/differentiable_continuous.
rewrite (_ : mulmxr \S(v) = (fun z => \sum_i z``_i *: row i \S(v))); last first.
  rewrite funeqE => z; by rewrite -mulmx_sum_row.
set f := fun (i : 'I_3) (z : 'rV_3) => z``_i *: row i \S(v) : 'rV_3.
rewrite (_ : (fun _ => _) = \sum_i f i); last by rewrite funeqE => ?; by rewrite fct_sumE.
apply: differentiable_sum => i.
exact/differentiableZl/differentiable_coord.
Qed.

Lemma differential_cross_product2 (v y : 'rV[R]_3) :
  'd_y (fun x : 'rV[R^o]_3 => x *v v) = -1 \*: mx_lin1 \S( v ) :> (_ -> _).
Proof.
transitivity ('d_y (crossmul (- v))); last first.
  by rewrite differential_cross_product spinN mx_lin1N.
congr diff.
by rewrite funeqE => /= u; rewrite crossmulC crossmulNv.
Qed.

End cross_product_matrix.

(* [sciavicco] p.80-81 *)
Section derivative_of_a_rotation_matrix.

Variable M : R -> 'M[R^o]_3. (* time-varying matrix *)

(* angular velocity matrix *)
Definition ang_vel_mx t := (M t)^T * derive1mx M t.

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
  forall t, derive1mx p t = ang_vel t *v (p' *m M t).
Proof.
move=> p t; rewrite /p derive1mxM; last first.
  exact: derivable_M.
  rewrite /derivable_mx => i j; exact: ex_derive.
rewrite derive1mx_cst mul0mx add0r derive1mx_ang_vel mulmxA.
by rewrite -{1}(unspinK (ang_vel_mx_is_so t)) spinE.
Qed.

End derivative_of_a_rotation_matrix.

Require Import frame.

Module BoundVect. (* i.e., point of application prescribed *)
Section bound_vector.
Variable T : ringType.
Record t (F : tframe T) := mk { endp : 'rV[T]_3 }.
Definition startp F (v : t F) : 'rV[T]_3 := TFrame.o F.
End bound_vector.
End BoundVect.
Notation bvec := BoundVect.t.
Coercion boundvectendp (T : ringType) (F : tframe T) (v : bvec F) :=
  BoundVect.endp v.

Definition bvec0 T (F : tframe T) : bvec F := BoundVect.mk _ 0.

Reserved Notation "a +bf b" (at level 39).
Reserved Notation "a -b b" (at level 39).

Section about_bound_vectors.

Variables (T : ringType) (F : tframe T).

Definition FramedVect_of_Bound (p : bvec F) : fvec F := `[ BoundVect.endp p $ F ].

Definition BoundVect_add (a b : bvec F) : bvec F :=
  BoundVect.mk F (BoundVect.endp a + BoundVect.endp b).

Definition BoundFramed_add (a : bvec F) (b : fvec F) : bvec F :=
  BoundVect.mk F (BoundVect.endp a + FramedVect.v b).

Local Notation "a +bf b" := (BoundFramed_add a b).

Lemma BoundFramed_addA (a : bvec F) (b c : fvec F) :
  a +bf b +bf c = a +bf (b +fv c).
Proof. by rewrite /BoundFramed_add /= addrA. Qed.

Definition BoundVect_sub (F : tframe T) (a b : bvec F) : fvec F :=
  `[ BoundVect.endp a - BoundVect.endp b $ F ].

Local Notation "a -b b" := (BoundVect_sub a b).

Lemma bv_eq (a b : bvec F) : a = b :> 'rV[T]_3 -> a = b.
Proof. by move: a b => [a] [b] /= ->. Qed.

End about_bound_vectors.

Notation "a +bf b" := (BoundFramed_add a b).
Notation "a -b b" := (BoundVect_sub a b).

Lemma derive1mx_BoundFramed_add (F : tframe [ringType of R^o])
  (Q : R -> bvec F) (Z : R -> fvec F) t :
  derivable_mx (fun x => BoundVect.endp (Q x)) t 1 ->
  derivable_mx (fun x => FramedVect.v (Z x)) t 1 ->
  derive1mx (fun x => BoundVect.endp (Q x +bf Z x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
    derive1mx (fun x => FramedVect.v (Z x)) t.
Proof.
move=> H H'.
rewrite (_ : (fun x : R => _) = (fun x : R => BoundVect.endp (Q x) +
  (FramedVect.v (Z x)))); last by rewrite funeqE.
rewrite derive1mxD.
- by [].
- exact: H.
- exact H'.
Qed.

Module RFrame.
Section rframe.
Variable T : ringType.
Record t (F : tframe T) := mk {
  o : bvec F ;
  i : fvec F ;
  j : fvec F ;
  k : fvec F ;
  f : tframe T ;
  _ : BoundVect.endp o = TFrame.o f ;
  _ : FramedVect.v i = (f|,@Ordinal 3 0 isT) ;
  _ : FramedVect.v j = (f|,@Ordinal 3 1 isT) ;
  _ : FramedVect.v k = (f|,@Ordinal 3 2 isT) ;
}.
End rframe.
End RFrame.
Notation rframe := RFrame.t.
Coercion tframe_of_rframe (R : ringType) (F : tframe R) (f : rframe F) : tframe R :=
  RFrame.f f.

Lemma RFrame_o (T : ringType) (F0 : tframe T) (F1 : rframe F0) :
  BoundVect.endp (RFrame.o F1) = TFrame.o (RFrame.f F1).
Proof. by destruct F1. Qed.

(* lemmas about relative frames *)

Lemma BoundVect0_fixed T (F : tframe T) (F1 : forall t, rframe F) (t : R) :
  BoundVect.endp (bvec0 (F1 t)) = BoundVect.endp (bvec0 (F1 0)).
Proof. by []. Qed.

Section derivable_FromTo.

Lemma derivable_mx_FromTo (F : R -> tframe [ringType of R^o])
  (G : forall t : R, rframe (F t)) t :
  derivable_mx F t 1 -> derivable_mx G t 1 ->
  derivable_mx (fun x => (G x) _R^ (F x)) t 1.
Proof.
move=> HF HG a b.
rewrite (_ : (fun x => _) = (fun x => row a (G x) *d row b (F x))); last first.
  by rewrite funeqE => t'; rewrite !mxE.
evar (f : 'I_3 -> R^o -> R^o).
rewrite (_ : (fun x => _) = \sum_i f i); last first.
  rewrite funeqE => t'; rewrite dotmulE fct_sumE; apply: eq_bigr => /= i _.
  rewrite !mxE /f; reflexivity.
rewrite {}/f.
apply: derivable_sum => i.
apply: derivableM; [exact: HG | exact: HF].
Qed.

Lemma derivable_mx_FromTo' (F : R -> tframe [ringType of R^o])
  (G' : forall t : R, rframe (F t))
  (G : forall t : R, rframe (F t)) t :
  derivable_mx F t 1 -> derivable_mx G t 1 -> derivable_mx G' t 1 ->
  derivable_mx (fun x => (G x) _R^ (G' x)) t 1.
Proof.
move=> HF HG HG' a b.
rewrite (_ : (fun x => _) = (fun x => row a (G x) *d row b (G' x))); last first.
  by rewrite funeqE => t'; rewrite !mxE.
evar (f : 'I_3 -> R^o -> R^o).
rewrite (_ : (fun x => _) = \sum_i f i); last first.
  rewrite funeqE => t'; rewrite dotmulE fct_sumE; apply: eq_bigr => /= i _.
  rewrite !mxE /f; reflexivity.
rewrite {}/f.
apply: derivable_sum => i.
apply: derivableM; [exact: HG | exact: HG'].
Qed.

Lemma derivable_mx_FromTo_fixed
  (F : tframe [ringType of R^o]) (G : R -> rframe F) t :
  derivable_mx G t 1 -> derivable_mx (fun x => (G x) _R^ F) t 1.
Proof.
move=> H; apply derivable_mx_FromTo; [move=> a b; exact: ex_derive | exact H].
Qed.

Lemma derivable_mx_FromTo_tr
  (F : tframe [ringType of R^o]) (G : R -> rframe F) t :
  derivable_mx (fun x => F _R^ (G x)) t 1 = derivable_mx (fun x => F _R^ (G x)) t 1.
Proof. by rewrite trmx_derivable. Qed.

End derivable_FromTo.

(* the coordinate transformation of a point P' from frame F1 to frame F
  (eqn 2.33, 3.10) *)
Definition fmap (F : tframe [ringType of R^o]) (F1 : rframe F)
    (P1 : bvec F1) : bvec F :=
  RFrame.o F1 +bf rmap F (FramedVect_of_Bound P1).

(* motion of P w.r.t. the fixed frame F (eqn B.2) *)
Definition motion (F : tframe [ringType of R^o]) (F1 : R -> rframe F)
  (P1 : forall t, bvec (F1 t)) t : bvec F := fmap (P1 t).

(* [sciavicco] p.351-352  *)
Section kinematics.

Variable F : tframe [ringType of R^o]. (* fixed frame *)
Variable F1 : R -> rframe F. (* time-varying frame (origin and basis in F) *)
Hypothesis derivable_F1 : forall t, derivable_mx F1 t 1.
Hypothesis derivable_F1o : forall t, derivable_mx (@TFrame.o [ringType of R^o] \o F1) t 1.

Variable P1 : forall t, bvec (F1 t). (* point with coordinates in F1 *)
(* NB: compared with [sciavicco] p.351, P1 not necessarily fixed in F1 *)
Hypothesis derivable_mxP1 : forall t, derivable_mx (fun x => BoundVect.endp (P1 x)) t 1.

Let P : R -> bvec F := motion P1.

Variable Q1 : forall t, bvec (F1 t).
Hypothesis Q1_fixed_in_F1 : forall t, BoundVect.endp (Q1 t) = BoundVect.endp (Q1 0).

Let Q : R -> bvec F := motion Q1.

(* eqn B.3 *)
Lemma eqnB3 t : P t = Q t +bf rmap F (P1 t -b Q1 t).
Proof.
rewrite /P /Q /motion /fmap BoundFramed_addA; congr (_ +bf _).
apply fv_eq => /=; rewrite -mulmxDl; congr (_ *m _).
by rewrite addrCA subrr addr0.
Qed.

Lemma derivable_mx_Q t : derivable_mx (fun x => BoundVect.endp (Q x)) t 1.
Proof.
rewrite /Q /=; apply derivable_mxD.
  move=> a b.
  move: (@derivable_F1o t a b).
  rewrite (_ : (fun x => TFrame.o (F1 x) a b) =
    (fun x => BoundVect.endp (RFrame.o (F1 x)) a b)) // funeqE => x.
  destruct (F1 x) => /=; by rewrite e.
apply derivable_mxM; last exact: derivable_mx_FromTo.
rewrite (_ : (fun x => _) = (fun _ => BoundVect.endp (Q1 0))); last first.
  rewrite funeqE => x; by rewrite Q1_fixed_in_F1.
move=> a b; exact: ex_derive.
Qed.

Let Rot := fun t => (F1 t) _R^ F.

(* generalization of B.4  *)
Lemma velocity_composition_rule (t : R) :
  derive1mx (fun x => BoundVect.endp (P x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
  derive1mx P1 t *m Rot t (* rate of change of the coordinates P1 expressed in the frame F *) +
  ang_vel Rot t *v FramedVect.v (P t -b Q t).
Proof.
rewrite {1}(_ : P = fun t => Q t +bf rmap F (P1 t -b Q1 t)); last first.
  by rewrite funeqE => t'; rewrite eqnB3.
rewrite (derive1mx_BoundFramed_add (@derivable_mx_Q t)); last first.
  apply derivable_mxM; last exact: derivable_mx_FromTo.
  rewrite (_ : (fun x => _) = (fun x => FramedVect.v (FramedVect_of_Bound (P1 x)) -
    FramedVect.v (FramedVect_of_Bound (Q1 0)))); last first.
    rewrite funeqE => x; by rewrite /= Q1_fixed_in_F1.
  apply: derivable_mxB => /=.
  exact: derivable_mxP1.
  move=> a b; exact: ex_derive.
rewrite -addrA; congr (_ + _).
rewrite [in LHS]/rmap [in LHS]/= derive1mxM; last 2 first.
  rewrite {1}(_ : (fun x  => _) = (fun x  => BoundVect.endp (P1 x) -
    BoundVect.endp (Q1 0))); last first.
    by rewrite funeqE => ?; rewrite Q1_fixed_in_F1.
  apply: derivable_mxB.
    exact: derivable_mxP1.
    move=> a b; exact: ex_derive.
  exact: derivable_mx_FromTo.
rewrite derive1mxB; last 2 first.
  exact: derivable_mxP1.
  rewrite (_ : (fun x => _) = cst (BoundVect.endp (Q1 0))); last first.
    by rewrite funeqE => x; rewrite Q1_fixed_in_F1.
  exact: derivable_mx_cst.
congr (_*m _  + _).
  rewrite [in X in _ + X = _](_ : (fun x => _) = cst (BoundVect.endp (Q1 0))); last first.
    by rewrite funeqE => x; rewrite Q1_fixed_in_F1.
  by rewrite derive1mx_cst subr0.
rewrite -spinE unspinK; last first.
  rewrite ang_vel_mx_is_so; first by [].
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite /ang_vel_mx mulmxA; congr (_ *m _).
rewrite /P /Q /= opprD addrACA subrr add0r mulmxBl -!mulmxA.
by rewrite orthogonal_mul_tr ?FromTo_is_O // !mulmx1.
Qed.

Hypothesis P1_fixed_in_G : forall t, BoundVect.endp (P1 t) = BoundVect.endp (P1 0).

(* eqn B.4 *)
Lemma velocity_composition_rule_spec (t : R) :
  derive1mx (fun x => BoundVect.endp (P x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
  ang_vel Rot t *v (FramedVect.v (P t -b Q t)).
Proof.
rewrite velocity_composition_rule; congr (_ + _).
suff -> : derive1mx P1 t = 0 by rewrite mul0mx addr0.
apply/matrixP => a b; rewrite !mxE.
rewrite (_ : (fun x => _) = cst (P1 0 a b)); last first.
  rewrite funeqE => x /=; by rewrite /boundvectendp (P1_fixed_in_G x).
by rewrite derive1_cst.
Qed.

End kinematics.

(* [sciavicco] p.81-82 *)
Section derivative_of_a_rotation_matrix_contd.

Variable F : tframe [ringType of R^o].
Variable F1 : R -> rframe F.
Hypothesis derivable_F1 : forall t, derivable_mx F1 t 1.
Variable p1 : forall t, bvec (F1 t).
Hypothesis derivable_mx_p1 : forall t, derivable_mx (fun x => BoundVect.endp (p1 x)) t 1.
Hypothesis derivable_F1o : forall t, derivable_mx (@TFrame.o [ringType of R^o] \o F1) t 1.

Definition p0 := motion p1.

Lemma eqn312 t :
  derive1mx (fun x => BoundVect.endp (motion p1 x)) t =
  derive1mx (fun x => BoundVect.endp (motion (fun=> bvec0 (F1 x)) t)) t +
  derive1mx p1 t *m (F1 t) _R^ F +
  ang_vel (fun t => (F1 t) _R^ F) t *v (p1 t *m (F1 t) _R^ F).
Proof.
rewrite (@velocity_composition_rule F _ derivable_F1 derivable_F1o p1 derivable_mx_p1
  (fun t => bvec0 (F1 t)) (@BoundVect0_fixed _ _ F1)).
congr (_ + _ *v _).
by rewrite /= mul0mx addr0 addrAC subrr add0r.
Qed.

End derivative_of_a_rotation_matrix_contd.

(* [sciavicco] p.83 *)
Section link_velocity.

Variable F : tframe [ringType of R^o].
Variable Fim1 : R -> rframe F.
Variable Fi : R -> rframe F.
Let pim1 t : bvec F := RFrame.o (Fim1 t).
Let pi t : bvec F := RFrame.o (Fi t).

Let rim1i : forall t : R, bvec (Fim1 t) := fun t =>
  BoundVect.mk (Fim1 t)
    (FramedVect.v (rmap (Fim1 t) `[ TFrame.o (Fi t) - TFrame.o (Fim1 t) $ F ])).

Hypothesis derivable_Fim1 : forall t, derivable_mx (fun x => Fim1 x) t 1.
Hypothesis derivable_Fim1o : forall t, derivable_mx (@TFrame.o [ringType of R^o] \o Fim1) t 1.
Hypothesis derivable_rim1i : forall t, derivable_mx (fun x => BoundVect.endp (rim1i x)) t 1.
Hypothesis derivable_Fi : forall t, derivable_mx (fun t0 : R => Fi t0) t 1.

Lemma eqn310' t : pi t = pim1 t +bf rmap F (FramedVect_of_Bound (rim1i t)).
Proof.
rewrite /pi /pim1 /= /rim1i /= /rmap /= /BoundFramed_add /=; apply bv_eq => /=.
rewrite -mulmxA FromTo_comp FromToI mulmx1 /= addrCA RFrame_o /=.
by rewrite subrr addr0 -RFrame_o.
Qed.

Definition wim1 := ang_vel (fun t => (Fim1 t) _R^ F).

(* lin. vel. of Link i as a function of
   the translational and rotational velocities of Link i-1 *)
Lemma eqn314 t : derive1mx pi t = derive1mx pim1 t +
  FramedVect.v (rmap F `[derive1mx rim1i t $ Fim1 t])
    (* velocity of the origin of Frame i w.r.t. the origin of Frame i-1 *) +
  wim1 t *v FramedVect.v (rmap F `[rim1i t $ Fim1 t]).
Proof.
move: (@eqn312 F _ derivable_Fim1 _ derivable_rim1i derivable_Fim1o t).
have -> : derive1mx (fun x : R => BoundVect.endp (motion rim1i x)) t =
  derive1mx (fun t0 : R => pi t0) t.
  rewrite (_ : (fun x : R => BoundVect.endp (motion rim1i x)) = (fun t0 : R => pi t0)) //.
  rewrite funeqE => t' /=; rewrite -mulmxA FromTo_comp FromToI mulmx1.
  rewrite addrCA RFrame_o subrr addr0.
  by rewrite /pi -RFrame_o.
move=> ->.
rewrite -!addrA; congr (_ + _).
rewrite (_ : (fun x : R => BoundVect.endp (motion (fun _ : R => bvec0 (Fim1 x)) t)) =
             (fun t0 : R => pim1 t0)) //.
rewrite funeqE => t'.
by rewrite /motion /= mul0mx addr0 /pim1.
Qed.

Definition wi : R -> 'rV_3 := ang_vel (fun t => (Fi t) _R^ F).
Definition wi' : R -> 'rV_3 := ang_vel (fun t => (Fi t) _R^ (Fim1 t)).

(* ang. vel. of Link i as a function of the ang. vel. of Link i-1 and of Link i w.r.t. Link i-1 *)
Lemma eqn316 t : wi t = wim1 t + wi' t *m ((Fim1 t) _R^ F).
Proof.
have : (fun t => (Fi t) _R^ F) = (fun t => ((Fi t) _R^ (Fim1 t)) *m ((Fim1 t) _R^ F)).
  by rewrite funeqE => ?; rewrite FromTo_comp.
move/(congr1 (fun x => derive1mx x)).
rewrite funeqE.
move/(_ t).
rewrite derive1mxM; last 2 first.
  move=> t'; exact: derivable_mx_FromTo'.
  move=> t'; exact: derivable_mx_FromTo.
rewrite derive1mx_ang_vel; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite derive1mx_ang_vel; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo'.
rewrite derive1mx_ang_vel; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite ang_vel_mxE; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite ang_vel_mxE; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo'.
rewrite ang_vel_mxE; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'; exact: derivable_mx_FromTo.
rewrite mulmxE -[in X in _ = X + _](mulr1 ((Fi t) _R^ (Fim1 t))).
rewrite -(@orthogonal_tr_mul _ _ (F _R^ (Fim1 t))) ?FromTo_is_O //.
rewrite -{2}(trmx_FromTo (Fim1 t) F).
rewrite -!mulrA.
rewrite (mulrA _ _ ((Fim1 t) _R^ F)).
rewrite (@spin_similarity _ ((Fim1 t) _R^ F)) ?FromTo_is_SO //.
rewrite mulrA -mulmxE.
rewrite trmx_FromTo.
rewrite FromTo_comp.
rewrite mulmxA.
rewrite FromTo_comp.
rewrite -mulmxDr.
rewrite -spinD.
rewrite -/wi -/wim1 -/wi'.
rewrite mulmxE.
move/mulrI.
rewrite FromTo_unit => /(_ isT)/eqP.
rewrite spin_inj => /eqP.
by rewrite addrC.
Qed.

End link_velocity.

Require Import rigid scara.

Section scara_jacobian.

Variable scara_joints : R -> 'rV[R^o]_4.
Let scara_joint_velocities : R^o -> 'rV_4 := derive1mx scara_joints.

Variable scara_end_effector : R -> 'M[R]_4. (* see hom scara_rot scara_trans *)
Let scara_lin_vel (t : R) : 'rV[R]_3 := trans_of_hom (scara_end_effector t).
Let scara_ang_vel : R -> 'rV[R]_3 :=
  let r : R -> 'M[R^o]_3 := fun t => rot_of_hom (scara_end_effector t) in
  fun t => unspin ((r t)^T * derive1mx r t).

Variable scara_jacobian : R -> 'M[R]_(4, 6).
(*
z0	z0 *v (o4 - o0)
z1	z1 *v (o4 - o1)
0	z2
z3	0
*)

Lemma scara_jacobianP t :
  scara_joints t *m scara_jacobian t = row_mx (scara_lin_vel t) (scara_ang_vel t).
Abort.

End scara_jacobian.

(* TODO: delete? *)
Section tangent_vectors.

Variable R : realType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.
Implicit Types p : point.

(* tangent vector *)
Record tvec p := TVec {tvec_field :> vector}.
Definition vtvec p (v : tvec p) := let: TVec v := v in v.

Local Notation "p .-vec" := (tvec p) (at level 5).
Local Notation "u :@ p" := (TVec p u) (at level 11).

Definition addt (p : point) (u : p.-vec) (v : vector) : p.-vec :=
  TVec p (tvec_field u + v).

Local Notation "p +@ u" := (addt p u) (at level 41).

End tangent_vectors.

Coercion vtvec_field_coercion := vtvec.
Notation "p .-vec" := (tvec p) (at level 5).
Notation "u :@ p" := (TVec p u) (at level 11).
Notation "p +@ u" := (addt p u) (at level 41).

Require Import angle.

(* TODO *)
Lemma derivative_Rx (a : R -> angle.angle [rcfType of R^o]) t :
  derive1mx (fun x => Rx (a x)) t = \S( row3 1 0 0 ) *m Rx (a t).
Abort.
