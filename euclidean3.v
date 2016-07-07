Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp
Require Import complex.
From mathcomp
Require Import finset fingroup perm.

Require Import aux.

(*
 OUTLINE:
 1. section extra
 2. section dot_product
 3. section triple_prod_mat (specialization of col_mx to row vectors of length 2, 3)
    section crossmul
    (definition of "normal" also)
    (sample lemma: double_crossmul)
 4. section O[R]_n and SO[R]_n
    (many lemmas specialized for dim 3)
    (sample lemma: Euler's theorem,
                   orth_preserves_dotmul)
 5. section norm
    (sample lemma: multiplication by O_3[R] preserves norm)
    (NB: some specialized lemmas for dimension 3 (Section norm3))
*)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Section SpecificsDim2And3.

Definition perm3_def (i j : 'I_3) : 'I_3 ^ 3 :=
  [ffun x : 'I_3 => if i == j then x else
    [fun z : 'I_3 => - (i + j) with 1 |-> i, 2%:R |-> j] x].

Fact perm3_subproof (i j : 'I_3) : injective (perm3_def i j).
Proof.
move=> x y; rewrite ?ffunE; have [//|neq_ij /=] := altP (i =P j).
move => hxy; apply/val_inj; move: x y i j hxy neq_ij.
by do 4![move=> [[|[|[|?]]] ?] //=].
Qed.

Definition perm3 i j : 'S_3 := perm (@perm3_subproof i j).

CoInductive I3_spec i j : bool -> bool -> 'I_3 -> Type :=
  | I3Spec_i : I3_spec i j true false i
  | I3Spec_j : I3_spec i j false true j
  | I3Spec_k : I3_spec i j false false (- (i + j)).

Lemma I3P i j k : i != j -> I3_spec i j (i == k) (j == k) k.
Proof.
move=> neq_ij.
have -> : k = if i == k then i else if j == k then j else - (i + j).
  by apply/val_inj; move: i j k neq_ij; do 3![case=> [[|[|[|?]]] ?]].
by move: i j k neq_ij; do 3![case=> [[|[|[|?]]] ?] //=]; constructor.
Qed.

Lemma odd_perm312 : perm3 1 2%:R = false :> bool.
Proof.
suff ->: perm3 1 2%:R = 1%g by rewrite odd_perm1.
by apply/permP=>-[[|[|[|//]]] ?]; apply/val_inj; rewrite ?permE ?ffunE.
Qed.

Lemma odd_perm310 : perm3 1 0 = true :> bool.
Proof.
suff -> : perm3 1 0 = tperm (0 : 'I__) 2%:R by rewrite odd_tperm.
by apply/permP=>-[[|[|[|//]]] ?]; apply/val_inj; rewrite ?permE ?ffunE.
Qed.

Lemma odd_perm302 : perm3 0 2%:R = true :> bool.
Proof.
suff -> : perm3 0 2%:R = tperm (0 : 'I__) 1%R by rewrite !odd_tperm /=.
by apply/permP=>-[[|[|[|//]]] ?]; apply/val_inj; rewrite ?permE ?ffunE.
Qed.

Lemma odd_perm321 : perm3 2%:R 1 = true :> bool.
Proof.
suff ->: perm3 2%:R 1 = tperm (1%R : 'I__) 2%:R by rewrite !odd_tperm /=.
by apply/permP=>-[[|[|[|//]]] ?]; apply/val_inj; rewrite ?permE ?ffunE.
Qed.

Lemma odd_perm301 : perm3 0 1 = false :> bool.
Proof.
suff -> : perm3 0 1 = (tperm (1 : 'I__) 2%:R * tperm (0 : 'I__) 1%:R)%g.
  by rewrite odd_permM !odd_tperm /=.
by apply/permP => -[[|[|[|?]]] ?]; do !rewrite ?permE ?ffunE //=; Simp.ord.
Qed.

Lemma odd_perm320 : perm3 2%:R 0 = false :> bool.
Proof.
suff -> : perm3 2%:R 0 = (tperm (1 : 'I__) 1%:R * tperm (1 : 'I__) 2%:R)%g.
  by rewrite odd_permM !odd_tperm /=.
by apply/permP => -[[|[|[|?]]] ?]; do !rewrite ?permE ?ffunE //=; Simp.ord.
Qed.

Definition odd_perm3 :=
  (odd_perm301, odd_perm302, odd_perm310, odd_perm312, odd_perm320, odd_perm321).

Lemma thirdI3 (i j : 'I_3) : i != j -> exists k, (k != i) && (k != j).
Proof.
move=> neq_ij; exists (- i - j).
by case: i j neq_ij => -[i0|[i1|[i2|//]]] [[|[|[]]]].
Qed.

Lemma ifnot0 (i : 'I_3) : (i != 0) = (i == 1) || (i == 2%:R).
Proof. by move: i; do !case=>//. Qed.

Lemma ifnot1 (i : 'I_3) : (i != 1) = (i == 0) || (i == 2%:R).
Proof. by move: i; do !case=>//. Qed.

Lemma ifnot2 (i : 'I_3) : (i != 2%:R) = (i == 0) || (i == 1).
Proof. by move: i; do !case=>//. Qed.

Lemma row_mx_col {R : ringType} n (A : 'M[R]_(n, 3)) :
  A = row_mx (col 0 A) (row_mx (col 1 A) (col 2%:R A)).
Proof.
rewrite -[in LHS](@hsubmxK _ n 1 2 A) (_ : lsubmx _ = col 0 A); last first.
  apply/colP => i; rewrite !mxE /= (_ : lshift 2 0 = 0) //; by apply val_inj.
rewrite (_ : rsubmx _ = row_mx (col 1 A) (col 2%:R A)) //.
set a := rsubmx _; rewrite -[in LHS](@hsubmxK _ n 1 1 a); congr row_mx.
  apply/colP => i; rewrite !mxE /= (_ : rshift 1 _ = 1) //; by apply val_inj.
apply/colP => i; rewrite !mxE /= (_ : rshift 1 (rshift 1 0) = 2%:R) //.
by apply val_inj.
Qed.

Definition row2 {R : ringType} (a b : R) : 'rV[R]_2 :=
  \row_p [eta \0 with 0 |-> a, 1 |-> b] p.

Lemma row2_of_row {R : ringType} (M : 'M[R]_2) i : row i M = row2 (M i 0) (M i 1).
Proof.
apply/rowP => j; rewrite !mxE /=; case: ifPn => [/eqP -> //|].
by rewrite ifnot01 => /eqP ->.
Qed.

Lemma matrix2P (T : Type) (A B : 'M[T]_2) :
  A 0 0 = B 0 0 -> A 0 1 = B 0 1-> A 1 0 = B 1 0 -> A 1 1 = B 1 1 -> A = B.
Proof.
move=> *; apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> //|]; first by rewrite ifnot01 => /eqP -> .
rewrite ifnot01 => /eqP ->.
case/boolP : (j == 0) => [/eqP -> //|]; by rewrite ifnot01 => /eqP ->.
Qed.

Definition row3 (R : ringType) (a b c : R) : 'rV[R]_3 :=
  \row_p [eta \0 with 0 |-> a, 1 |-> b, 2%:R |-> c] p.

Lemma row3N (R : ringType) (a b c : R) : - row3 a b c = row3 (- a) (- b) (- c).
Proof.
apply/rowP => i; rewrite !mxE /= ; case: ifPn; rewrite ?opprB // => ?.
by case: ifPn; rewrite ?opprB // => ?; case: ifPn; rewrite ?opprB // oppr0.
Qed.

Lemma row3Z (R : ringType) (a b c : R) k : k *: row3 a b c = row3 (k * a) (k * b) (k * c).
Proof.
apply/rowP => i; rewrite !mxE /=.
case: ifPn => // ?; case: ifPn => // ?; case: ifPn => // ?; by Simp.r.
Qed.

Lemma row30 (R : ringType) : row3 0 0 0 = 0 :> 'rV[R]_3.
Proof. by apply/rowP => a; rewrite !mxE /=; do 3 case: ifPn => //. Qed.

Lemma row3E (R : ringType) (u : 'rV[R]_3) :
  u = row3 (u``_0) 0 0 + row3 0 (u``_1) 0 + row3 0 0 (u``_2%:R).
Proof.
apply/rowP => i; rewrite !mxE /=; case: ifPn => [/eqP ->|]; first by Simp.r.
rewrite ifnot0 => /orP [] /eqP -> /=; by Simp.r.
Qed.

Lemma vec3E (R : ringType) (u : 'rV[R]_3) :
  u = (u``_0) *: 'e_0 + (u``_1) *: 'e_1 + (u``_2%:R) *: 'e_2%:R.
Proof.
by apply/rowP => - [[|[|[|?]]] ?] //; rewrite !mxE /=; Simp.r; Simp.ord.
Qed.

Lemma row3_row_mx (R : ringType) (a b c : R) : row3 a b c = row_mx a%:M (row_mx b%:M c%:M).
Proof.
rewrite (row_mx_col (row3 a b c)) (_ : col _ _ = a%:M); last first.
  by apply/rowP => i; rewrite (ord1 i) !mxE /= mulr1n.
rewrite (_ : col _ _ = b%:M); last first.
  by apply/rowP => i; rewrite (ord1 i) !mxE /= mulr1n.
rewrite (_ : col _ _ = c%:M) //.
by apply/rowP => i; rewrite (ord1 i) !mxE /= mulr1n.
Qed.

Lemma matrix3P (T : Type) (A B : 'M[T]_3) :
  A 0 0 = B 0 0 -> A 0 1 = B 0 1-> A 0 2%:R = B 0 2%:R ->
  A 1 0 = B 1 0 -> A 1 1 = B 1 1-> A 1 2%:R = B 1 2%:R ->
  A 2%:R 0 = B 2%:R 0 -> A 2%:R 1 = B 2%:R 1-> A 2%:R 2%:R = B 2%:R 2%:R ->
  A = B.
Proof.
move=> *; apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> //|]; first by rewrite ifnot0 => /orP [] /eqP ->.
rewrite ifnot0 => /orP [] /eqP ->;
  case/boolP : (j == 0) => [/eqP -> //|]; by rewrite ifnot0 => /orP [] /eqP ->.
Qed.

Lemma det_mx11 (T : comRingType) (A : 'M[T]_1) : \det A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar det_scalar. Qed.

Lemma cofactor_mx22 {T : comRingType} (A : 'M[T]_2) i j :
  cofactor A i j = (-1) ^+ (i + j) * A (i + 1) (j + 1).
Proof.
rewrite /cofactor det_mx11 !mxE; congr (_ * A _ _);
by apply/val_inj; move: i j => [[|[|?]]?] [[|[|?]]?].
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

End SpecificsDim2And3.

Section dot_product.

Variables (R : rcfType) (n : nat).

Definition dotmul (u v : 'rV[R]_n) : R := (u *m v^T)``_0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE u v : u *d v = \sum_k u``_k * v``_k.
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

Lemma dotmulvN u v : u *d -v = - (u *d v).
Proof. by rewrite /dotmul linearN /= mulmxN mxE. Qed.

Lemma dotmulNv u v : - u *d v = - (u *d v).
Proof. by rewrite dotmulC dotmulvN dotmulC. Qed.

Lemma dotmulBr a b c : a *d (b - c) = a *d b - a *d c.
Proof. by rewrite dotmulDr dotmulvN. Qed.

Lemma dotmulBl a b c : (b - c) *d a = b *d a - c *d a.
Proof. by rewrite dotmulDl dotmulNv. Qed.

Lemma dotmulD u v : (u + v) *d (u + v) = u *d u + (u *d v) *+ 2 + v *d v.
Proof. by rewrite dotmulDr 2!dotmulDl mulr2n !addrA ![v *d _]dotmulC. Qed.

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

Lemma dotmul_delta_mx u i : u *d 'e_i = u``_i.
Proof. by rewrite dotmulC /dotmul -rowE !mxE. Qed.

Lemma dote2 i j : 'e_i *d 'e_j = (i == j)%:R.
Proof. by rewrite dotmul_delta_mx mxE eqxx eq_sym. Qed.

(* Lemma dotmul_eq u v : (forall x, u *d x = v *d x) -> u = v. *)
(* Proof. by move=> uv; apply/rowP => i; rewrite -!dotmul_delta_mx uv. Qed. *)

Lemma dotmul_trmx u M v : u *d (v *m M) = (u *m M^T) *d v.
Proof. by rewrite /dotmul trmx_mul mulmxA. Qed.

Lemma diag_sqr (M : 'M_n) i : (M *m M) i i = (row i M) *d (col i M)^T.
Proof. rewrite mxE dotmulE; apply/eq_bigr => /= j _; by rewrite 3!mxE. Qed.

End dot_product.

Notation "*d%R" := (@dotmul _ _) : ring_scope.
Notation "u *d w" := (dotmul u w) (at level 40) : ring_scope.

Lemma mxtrace_sqr {R : rcfType} (M : 'M[R]_3) : \tr (M ^+ 2) =
  \sum_i (M i i ^+2) + M 0 1 * M 1 0 *+ 2 + M 0 2%:R * M 2%:R 0 *+ 2 +
  M 1 2%:R * M 2%:R 1 *+ 2.
Proof.
rewrite sum3E.
transitivity (\sum_(i < 3) (row i M) *d (col i M)^T).
  by apply/eq_bigr => i _; rewrite diag_sqr.
rewrite sum3E !dotmulE !sum3E !mxE -!expr2 -!addrA; congr (_ + _).
do 3 rewrite addrC -!addrA; congr (_ + _).
do 3 rewrite addrC -!addrA; congr (_ + _).
congr (_ + _).
rewrite addrC -!addrA mulrC; congr (_ + _).
rewrite addrC -!addrA mulrC; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite mulrC.
Qed.

Lemma sqr_mxtrace {R : rcfType} (M : 'M[R]_3) : (\tr M) ^+ 2 =
  \sum_i (M i i ^+2) + M 0 0 * M 1 1 *+ 2 + (M 0 0 + M 1 1) * M 2%:R 2%:R *+ 2.
Proof.
rewrite /mxtrace sum3E 2!sqrrD sum3E -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
Qed.

Section triple_prod_mat.

Variable (T : ringType).

Definition col_mx2 (u v : 'rV[T]_2) :=
  \matrix_(i < 2) [eta \0 with 0 |-> u, 1 |-> v] i.

Lemma eq_col_mx2 (a a' b b' c c' d d' : T) :
  col_mx2 (row2 a b) (row2 c d) = col_mx2 (row2 a' b') (row2 c' d') ->
  [/\ a = a', b = b', c = c' & d = d'].
Proof.
move/matrixP => H; split; by [
  move/(_ 0 0) : H; rewrite !mxE | move/(_ 0 1) : H; rewrite !mxE |
  move/(_ 1 0) : H; rewrite !mxE | move/(_ 1 1) : H; rewrite !mxE].
Qed.

Lemma col_mx2_rowE (M : 'M[T]_2) : M = col_mx2 (row 0 M) (row 1 M).
Proof.
apply/row_matrixP => i; rewrite rowK /=; case: ifPn => [/eqP -> //|].
by rewrite ifnot01 => /eqP ->.
Qed.

Implicit Types u v w : 'rV[T]_3.

Definition col_mx3 u v w :=
  \matrix_(i < 3) [eta \0 with 0 |-> u, 1 |-> v, 2%:R |-> w] i.

Lemma mulmx_row3_col3 (a b c : T) u v w :
  row3 a b c *m col_mx3 u v w = a *: u + b *: v + c *: w.
Proof. apply/rowP => n; by rewrite !mxE sum3E !mxE. Qed.

Lemma col_mx3_rowE (M : 'M[T]_3) : M = col_mx3 (row 0 M) (row 1 M) (row 2%:R M).
Proof.
apply/row_matrixP => i; rewrite rowK /=; case: ifPn => [/eqP -> //|].
by rewrite ifnot0 => /orP [] /eqP ->.
Qed.

Lemma col_mx3E u v w : col_mx3 u v w = col_mx u (col_mx v w).
Proof.
rewrite [LHS]col_mx3_rowE; apply/row_matrixP => i; rewrite !rowK /=.
case: ifPn => [/eqP ->|].
  rewrite (_ : 0 = @lshift 1 _ 0) ?(@rowKu _ 1) ?row_id //; by apply val_inj.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite (_ : 1 = @rshift 1 _ 0) ?(@rowKd _ 1); last by apply val_inj.
  rewrite  (_ : 0 = @lshift 1 _ 0) ?(@rowKu _ 1) ?row_id //; by apply val_inj.
rewrite (_ : 2%:R = @rshift 1 _ 1) ?(@rowKd _ 1); last by apply val_inj.
rewrite (_ : 1 = @rshift 1 1 0) ?(@rowKd _ 1) ?row_id //; by apply val_inj.
Qed.

Lemma row'_col_mx3 (i : 'I_3) (u v w : 'rV[T]_3) :
  row' i (col_mx3 u v w) = [eta \0 with
  0 |-> \matrix_(k < 2) [eta \0 with 0 |-> v, 1 |-> w] k,
  1 |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> w] k,
  2%:R |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> v] k] i.
Proof.
case: i => [[|[|[|?]]]] ?; apply/matrixP=> [] [[|[|[|?]]]] ? j;
by rewrite !mxE.
Qed.

Lemma col_mx3_perm_12 u v w : xrow 1 2%:R (col_mx3 u v w) = col_mx3 u w v.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE.
Qed.

Lemma col_mx3_perm_01 u v w : xrow 0 1 (col_mx3 u v w) = col_mx3 v u w.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE.
Qed.

Lemma col_mx3_perm_02 u v w : xrow 0 2%:R (col_mx3 u v w) = col_mx3 w v u.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE.
Qed.

Lemma mulmx_col3 M u v w : col_mx3 u v w *m M = col_mx3 (u *m M) (v *m M) (w *m M).
Proof.
apply/matrixP => i j.
move: i => -[[|[|[] // ]] ?]; rewrite !mxE; apply eq_bigr => /= ? _; by rewrite mxE.
Qed.

End triple_prod_mat.

Lemma col_mx3_mul {R : rcfType} (x : 'rV[R]_3) a b c :
  x *m (col_mx3 a b c)^T = row3 (x *d a) (x *d b) (x *d c).
Proof.
rewrite col_mx3E (tr_col_mx a) (tr_col_mx b) (mul_mx_row x a^T).
by rewrite row3_row_mx (mul_mx_row x b^T) /dotmul -!mx11_scalar.
Qed.

Section crossmul.

Variable R : rcfType.

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

Implicit Types u v w : 'rV[R]_3.

Lemma normalvv u v : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

Definition crossmul u v := \row_(k < 3) \det (col_mx3 'e_k u v).

Local Notation "*v%R" := (@crossmul _).
Local Notation "u *v w" := (crossmul u w) (at level 40).

Lemma crossmulC u v : u *v v = - (v *v u).
Proof.
rewrite /crossmul; apply/rowP => k; rewrite !mxE.
set M := (X in - \det X).
transitivity (\det (row_perm (tperm (1 : 'I__) 2%:R) M)); last first.
  by rewrite row_permE detM det_perm odd_tperm /= expr1 mulN1r.
congr (\det _); apply/matrixP => i j; rewrite !mxE permE /=.
by case: i => [[|[|[]]]] ?.
Qed.

Lemma crossmulvv u : u *v u = 0.
Proof.
apply/rowP=> i; rewrite !mxE (@determinant_alternate _ _ _ 1 2%:R) //.
by move=> j; rewrite !mxE.
Qed.

Lemma crossmul0v u : 0 *v u = 0.
Proof.
apply/rowP=> k; rewrite !mxE; apply/eqP/det0P.
exists 'e_1.
  apply/negP=> /eqP /(congr1 (fun f : 'M__ => f 0 1)) /eqP.
  by rewrite !mxE /= oner_eq0.
by rewrite -rowE; apply/rowP=> j; rewrite !mxE.
Qed.

Lemma crossmulv0 u : u *v 0 = 0.
Proof. by rewrite crossmulC crossmul0v oppr0. Qed.

Lemma crossmul_triple u v w : u *d (v *v w) = \det (col_mx3 u v w).
Proof.
pose M (k : 'I_3) : 'M_3 := col_mx3 ('e_k) v w.
pose Mu12 := col_mx3 (u``_1 *: 'e_1 + u``_2%:R *: 'e_2%:R) v w.
rewrite (@determinant_multilinear _ _ _ (M 0) Mu12 0 (u``_0) 1) ?mul1r
        ?row'_col_mx3 //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx /tnth /=.
  by case: j => [[|[|[]]]] ? //=; Simp.ord; Simp.r.
rewrite [\det Mu12](@determinant_multilinear _ _ _
  (M 1) (M 2%:R) 0 (u``_1) (u``_2%:R)) ?row'_col_mx3 //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx.
  by case: j => [[|[|[]]]] ? //=; Simp.ord; Simp.r.
by rewrite dotmulE !big_ord_recl big_ord0 addr0 /= !mxE; Simp.ord.
Qed.

Lemma crossmul_normal u v : u _|_ (u *v v).
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
pose M w := col_mx3 ('e_k) u w.
rewrite (@determinant_multilinear _ _ (M _) (M v) (M w) 2%:R a 1);
  rewrite ?row'_col_mx3 ?mul1r ?scale1r ?mxE //=.
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

Lemma crossmulE u v : (u *v v) = row3
  (u``_1 * v``_2%:R - u``_2%:R * v``_1)
  (u``_2%:R * v``_0 - u``_0 * v``_2%:R)
  (u``_0 * v``_1 - u``_1 * v``_0).
Proof.
apply/rowP => i; rewrite !mxE (expand_det_row _ ord0).
rewrite !(mxE, big_ord_recl, big_ord0) !(mul0r, mul1r, addr0).
rewrite /cofactor !det_mx22 !mxE /= mul1r mulN1r opprB -signr_odd mul1r.
by Simp.ord; case: i => [[|[|[]]]] //= ?; rewrite ?(mul1r,mul0r,add0r,addr0).
Qed.

Lemma vece2 (i j : 'I_3) (k := - (i + j) : 'I_3) :
  'e_i *v 'e_j = (-1)^(perm3 i j)%N *+ (i != j) *: 'e_k :> 'rV[R]__.
Proof.
have [->|neq_ij] := altP (i =P j); rewrite (mulr0n,mulr1n).
  by rewrite scale0r crossmulvv.
apply/rowP => k'; case: (I3P k' neq_ij); rewrite !mxE.
- rewrite (@determinant_alternate _ _ _ 0 1) //=.
    by move: i j @k neq_ij => [[|[|[|?]]] ?] [[|[|[|?]]] ?] //=; rewrite mulr0.
  by move=> k''; rewrite !mxE.
- rewrite (@determinant_alternate _ _ _ 0 2%:R) //=.
    by move: i j @k neq_ij => [[|[|[|?]]] ?] [[|[|[|?]]] ?] //=; rewrite mulr0.
  by move=> k''; rewrite !mxE.
rewrite !eqxx mulr1 -[_ ^ _](@det_perm R) {k k'}; congr (\det _).
apply/matrixP => a b; rewrite !mxE permE ffunE /=.
by move: a b i j neq_ij; do 4![move=> [[|[|[|?]]] ?]; rewrite ?mxE //=].
Qed.

Lemma nth_crossmul u v i :
  (u *v v)``_i = u``_(i + 1) * v``_(i + 2%:R) - u``_(i + 2%:R) * v``_(i + 1).
Proof. by case: i => [[|[|[|?]]] ?]; rewrite crossmulE !mxE; Simp.ord. Qed.

Lemma crossmulNv u v : - u *v v = - (u *v v).
Proof. by rewrite crossmulC linearN /= opprK crossmulC. Qed.

(* TODO: useful? *)
Lemma crossmulvN u v : u *v (- v) = - (u *v v).
Proof. by rewrite linearN. Qed.

Lemma crossmulZv u v k : ((k *: u) *v v) = k *: (u *v v).
Proof. by rewrite crossmulC linearZ /= crossmulC scalerN opprK. Qed.

Lemma crossmulvZ u v k : (u *v (k *: v)) = k *: (u *v v).
Proof. by rewrite linearZ. Qed.

Lemma crossmul0E u v :
  (u *v v == 0) = [forall i, [forall j, (i != j) ==> (u``_j * v``_i == u``_i * v``_j)]].
Proof.
apply/eqP/'forall_'forall_implyP; last first.
  move=> uv_eq_vu; apply/rowP=> k; rewrite nth_crossmul mxE.
  rewrite (eqP (uv_eq_vu _ _ _)) ?subrr //.
  by case: k => [[|[|[|?]]] ?] //=.
move=> uv_eq0 i j neq_ij; have := nth_crossmul u v (-(i + j)).
rewrite uv_eq0 !mxE => /(canLR (@addrNK _ _)); rewrite add0r.
move: i j neq_ij; do 2![move=> [[|[|[|?]]] ?] //=; Simp.ord => //=];
by do ?[move=> _ -> //].
Qed.

Lemma mulmxl_crossmulr M u v : M *m (u *v v) = u *v (M *m v).
Proof. by rewrite -(mul_rV_lin1 [linear of crossmul u]) mulmxA mul_rV_lin1. Qed.

Lemma mulmxl_crossmull M u v : M *m (u *v v) = ((M *m u) *v v).
Proof. by rewrite crossmulC mulmxN mulmxl_crossmulr -crossmulC. Qed.

Lemma dotmul_crossmul_shift u v w : u *d (v *v w) = w *d (u *v v).
Proof.
rewrite crossmul_triple.
rewrite -col_mx3_perm_12 xrowE det_mulmx det_perm /= odd_tperm /=.
rewrite -col_mx3_perm_01 xrowE det_mulmx det_perm /= odd_tperm /=.
by rewrite expr1 mulrA mulrNN 2!mul1r -crossmul_triple.
Qed.

Lemma dotmul_crossmulA u v x : u *d (v *v x) = (u *v v) *d x.
Proof. by rewrite dotmul_crossmul_shift dotmulC. Qed.

Lemma dotmul_crossmulCA u v w : u *d (v *v w) = - v *d (u *v w).
Proof. do 2 rewrite dotmul_crossmulA; by rewrite crossmulNv crossmulC. Qed.

Lemma det_col_mx3 u v x : \det (col_mx3 u v x) = (u *v v) *d x.
Proof. by rewrite -crossmul_triple dotmul_crossmulA. Qed.

Lemma det_crossmul_dotmul M u v x :
  (\det M *: (u *v v)) *d x = (((u *m M) *v (v *m M)) *m M^T) *d x.
Proof.
transitivity (\det M * \det (col_mx3 u v x)).
  by rewrite dotmulZv -crossmul_triple dotmul_crossmulA.
transitivity (\det (col_mx3 (u *m M) (v *m M) (x *m M))).
  by rewrite mulrC -det_mulmx mulmx_col3.
by rewrite det_col_mx3 dotmul_trmx.
Qed.

Lemma mulmx_crossmul' M u v : \det M *: (u *v v) = ((u *m M) *v (v *m M)) *m M^T.
Proof. by apply/rowP=> i; rewrite -!dotmul_delta_mx det_crossmul_dotmul. Qed.

Lemma mulmx_crossmul M u v : M \is a GRing.unit ->
  (u *v v) *m (\det M *: M^-1^T) = (u *m M) *v (v *m M).
Proof.
move=> invM.
move: (mulmx_crossmul' M u v) => /(congr1 (fun x => x *m M^T^-1)).
rewrite -mulmxA mulmxV ?unitmx_tr // mulmx1 => <-.
by rewrite -scalemxAr trmx_inv scalemxAl.
Qed.

Lemma double_crossmul (u v w : 'rV[R]_3) :
 u *v (v *v w) = (u *d w) *: v - (u *d v) *: w.
Proof.
suff aux i : u *d w * v``_i - u *d v * w``_i =
   u``_(i + 1) * (v``_i * w``_(i + 1) - v``_(i + 1) * w``_i) -
   u``_(i + 2%:R) * (v``_(i + 2%:R) * w``_i - v``_i * w``_(i + 2%:R)).
  apply/rowP=> -[[|[|[|?]]] ? //=];
  by rewrite !crossmulE !mxE /= aux; Simp.ord.
have neq_iSi: i + 1 != i by case: i => [[|[|[|?]]] ? //=].
have neq_iSSi:  (i + 2%:R != i) && (i + 2%:R != i + 1).
   by case: i neq_iSi => [[|[|[|?]]] ? //=].
do ![rewrite dotmulE (bigD1 i) // (bigD1 (i + 1)) // (bigD1 (i + 2%:R)) //=;
     rewrite big1 ?mul0r ?addr0 ?mulrDl ?opprD;
   last by move: i {neq_iSi neq_iSSi}; do 2![move => [[|[|[|?]]] ? //=]]].
rewrite addrACA mulrAC subrr add0r addrACA -!mulrA -!mulrBr ![w``__ * _]mulrC.
by congr (_ + _); rewrite -[RHS]mulrN opprB.
Qed.

Lemma dotmul_crossmul2 u v w : (u *v v) *v (u *v w) = (u *d (v *v w)) *: u.
Proof.
by rewrite double_crossmul (dotmulC _ u) dotmul_crossmulA crossmulvv dotmul0v
  scale0r subr0 -dotmul_crossmulA.
Qed.

Lemma jacobi u v w : u *v (v *v w) + v *v (w *v u) + w *v (u *v v) = 0.
Proof.
rewrite 3!double_crossmul.
rewrite !addrA -(addrA (_ *: v)) (dotmulC u v) -(addrC (_ *: w)) subrr addr0.
rewrite -!addrA addrC -!addrA (dotmulC w u) -(addrC (_ *: v)) subrr addr0.
by rewrite addrC dotmulC subrr.
Qed.

End crossmul.

Notation "*v%R" := (@crossmul _) : ring_scope.
Notation "u *v w" := (crossmul u w) (at level 40) : ring_scope.

Section orthogonal_rotation_def.

Variables (n : nat) (R : rcfType).

Definition orthogonal := [qualify M : 'M[R]_n | M *m M^T == 1%:M].
Fact orthogonal_key : pred_key orthogonal. Proof. by []. Qed.
Canonical orthogonal_keyed := KeyedQualifier orthogonal_key.

Definition rotation := [qualify M : 'M[R]_n | (M \is orthogonal) && (\det M == 1)].
Fact rotation_key : pred_key rotation. Proof. by []. Qed.
Canonical rotation_keyed := KeyedQualifier rotation_key.

End orthogonal_rotation_def.

Notation "''O[' R ]_ n" := (orthogonal n R)
  (at level 8, n at level 2, format "''O[' R ]_ n") : ring_scope.

Notation "''SO[' R ]_ n" := (rotation n R)
  (at level 8, n at level 2, format "''SO[' R ]_ n") : ring_scope.

Section orthogonal.

Variables (n' : nat) (R : rcfType).
Let n := n'.+1.

Lemma orthogonalE M : (M \is 'O[R]_n) = (M * M^T == 1). Proof. by []. Qed.

Lemma orthogonal1 : 1 \is 'O[R]_n.
Proof. by rewrite orthogonalE trmx1 mulr1. Qed.

Lemma orthogonalEinv M : (M \is 'O[R]_n) = (M \is a GRing.unit) && (M^-1 == M^T).
Proof.
rewrite orthogonalE; have [Mu | notMu] /= := boolP (M \in unitmx); last first.
  by apply: contraNF notMu => /eqP /mulmx1_unit [].
by rewrite -(inj_eq (@mulrI _ M^-1 _)) ?unitrV // mulr1 mulKr.
Qed.

Lemma orthogonal_unit M : (M \is 'O[R]_n) -> (M \is a GRing.unit).
Proof. by rewrite orthogonalEinv => /andP []. Qed.

Lemma orthogonalV M : (M^T \is 'O[R]_n) = (M \is 'O[R]_n).
Proof.
by rewrite !orthogonalEinv unitmx_tr -trmxV (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma orthogonal_inv M : M \is 'O[R]_n -> M^-1 = M^T.
Proof. by rewrite orthogonalEinv => /andP [_ /eqP]. Qed.

Lemma orthogonalEC M : (M \is 'O[R]_n) = (M^T * M == 1).
Proof. by rewrite -orthogonalV orthogonalE trmxK. Qed.

Lemma orthogonal_det M : M \is 'O[R]_n -> `|\det M| = 1.
Proof.
move=> /eqP /(congr1 determinant); rewrite detM det_tr det1 => /eqP.
by rewrite sqr_norm_eq1 => /eqP.
Qed.

Lemma orthogonal_oppr_closed : oppr_closed 'O[R]_n.
Proof. by move=> x; rewrite !orthogonalE linearN /= mulNr mulrN opprK. Qed.
Canonical orthogonal_is_oppr_closed := OpprPred orthogonal_oppr_closed.

Lemma orthogonal_divr_closed : divr_closed 'O[R]_n.
Proof.
split => [| P Q HP HQ]; first exact: orthogonal1.
rewrite orthogonalE orthogonal_inv // trmx_mul trmxK -mulrA.
by rewrite -orthogonal_inv // mulKr // orthogonal_unit.
Qed.
Canonical orthogonal_is_mulr_closed := MulrPred orthogonal_divr_closed.
Canonical orthogonal_is_divr_closed := DivrPred orthogonal_divr_closed.
Canonical orthogonal_is_smulr_closed := SmulrPred orthogonal_divr_closed.
Canonical orthogonal_is_sdivr_closed := SdivrPred orthogonal_divr_closed.

Lemma rotationE M : (M \is 'SO[R]_n) = (M \is 'O[R]_n) && (\det M == 1). Proof. by []. Qed.

Lemma rotationV M : (M^T \is 'SO[R]_n) = (M \is 'SO[R]_n).
Proof. by rewrite rotationE orthogonalV det_tr -rotationE. Qed.

Lemma rotation_inv M : M \is 'SO[R]_n -> M^-1 = M^T.
Proof. by rewrite rotationE orthogonalEinv => /andP[/andP[_ /eqP]]. Qed.

Lemma rotation_det M : M \is 'SO[R]_n -> \det M = 1.
Proof. by move=> /andP[_ /eqP]. Qed.

Lemma rotation1 : 1 \is 'SO[R]_n.
Proof. apply/andP; by rewrite orthogonal1 det1. Qed.

Lemma rotation_sub : {subset 'SO[R]_n <= 'O[R]_n}.
Proof. by move=> M /andP []. Qed.

Lemma rotation_divr_closed : divr_closed 'SO[R]_n.
Proof.
split => [|P Q Prot Qrot]; first exact: rotation1.
rewrite rotationE rpred_div ?rotation_sub //=.
by rewrite det_mulmx det_inv !rotation_det // divr1.
Qed.

Canonical rotation_is_mulr_closed := MulrPred rotation_divr_closed.
Canonical rotation_is_divr_closed := DivrPred rotation_divr_closed.

End orthogonal.

Lemma orthogonalP n R M :
  reflect (forall i j, row i M *d row j M = (i == j)%:R) (M \is 'O[R]_n.+1).
Proof.
apply: (iffP idP) => [|H] /=.
  rewrite orthogonalE => /eqP /matrixP H i j.
  move/(_ i j) : H; rewrite /dotmul !mxE => <-.
  apply eq_bigr => k _; by rewrite !mxE.
rewrite orthogonalE.
apply/eqP/matrixP => i j; rewrite !mxE.
rewrite -H /dotmul !mxE.
apply eq_bigr => k _; by rewrite !mxE.
Qed.

(* TODO: move? *)
Lemma dotmul_conjc_eq0 {R : rcfType} n (v : 'rV[R[i]]_n.+1) :
  (v *m map_mx conjc v^T == 0) = (v == 0).
Proof.
apply/idP/idP => [H|/eqP ->]; last by rewrite mul0mx.
have : \sum_(i < n.+1) v``_i * (v``_i)^* = 0.
  move/eqP/matrixP : H =>/(_ 0 0).
  rewrite !mxE => H; rewrite -{2}H.
  apply/eq_bigr => /= i _; by rewrite !mxE.
move/eqP; rewrite psumr_eq0 /= => [/allP K|]; last first.
  move=> i _; by rewrite -sqr_normc exprn_ge0.
apply/eqP/rowP => i.
move: (K i); rewrite /index_enum -enumT mem_enum inE => /(_ isT).
rewrite -sqr_normc sqrf_eq0 normr_eq0 => /eqP ->; by rewrite mxE.
Qed.

(* eigenvalues of orthogonal matrices have norm 1 *)
Lemma eigenvalue_O (R : rcfType) n M : M \is 'O[R]_n.+1 -> forall k,
   k \in eigenvalue (map_mx (fun x => x%:C) M) -> `| k | = 1.
Proof.
move=> MSO /= k.
case/eigenvalueP => v kv v0.
move/(congr1 trmx)/(congr1 (fun x => map_mx conjc x)) : (kv).
rewrite trmx_mul map_mxM linearZ /= map_mxZ map_trmx.
move/(congr1 (fun x => (k *: v) *m x)).
rewrite -{1}kv -mulmxA (mulmxA (map_mx _ M)) (_ : map_mx _ M *m _ = 1%:M); last first.
  rewrite (_ : map_mx conjc _ = map_mx (fun x => x%:C) M^T); last first.
    apply/matrixP => i j; by rewrite !mxE conjc_real.
  rewrite orthogonalE in MSO.
  by rewrite -map_mxM mulmxE (eqP MSO) map_mx1.
rewrite mul1mx -scalemxAr /= -scalemxAl scalerA => /eqP.
rewrite -subr_eq0 -{1}(scale1r (v *m _)) -scalerBl scaler_eq0 => /orP [].
  by rewrite subr_eq0 mulrC -sqr_normc -{1}(expr1n _ 2) eqr_expn2 // ?ler01 // => /eqP.
by rewrite dotmul_conjc_eq0 (negbTE v0).
Qed.

Lemma orth_preserves_sqr_norm R n M : M \is 'O[R]_n.+1 ->
  {mono (fun u => u *m M) : x / x *d x}.
Proof.
move=> HM u; rewrite dotmul_trmx -mulmxA (_ : M *m _ = 1%:M) ?mulmx1 //.
by move: HM; rewrite orthogonalE => /eqP.
Qed.

Lemma orth_preserves_dotmul {R : rcfType} n (f : 'M[R]_n.+1) :
  {mono (fun u => u *m f) : x y / x *d y} <-> f \is 'O[R]_n.+1.
Proof.
split => H.
  apply/orthogonalP => i j.
  by rewrite 2!rowE H dotmul_delta_mx mxE eqxx /= eq_sym.
move=> u v.
have := orth_preserves_sqr_norm H (u + v).
rewrite mulmxDl dotmulD.
rewrite dotmulD.
rewrite orth_preserves_sqr_norm // (orth_preserves_sqr_norm H v) //.
move/(congr1 (fun x => x - v *d v)).
rewrite -!addrA subrr 2!addr0.
move/(congr1 (fun x => - (u *d u) + x)).
rewrite !addrA (addrC (- (u *d u))) subrr 2!add0r.
rewrite -2!mulr2n => /eqP.
by rewrite eqr_pmuln2r // => /eqP.
Qed.

Section orthogonal_crossmul.

Variable R : rcfType.

(* "From the geometrical definition, the cross product is invariant under
   proper rotations about the axis defined by a × b"
   https://en.wikipedia.org/wiki/Cross_product *)
Lemma mulmxr_crossmulr r u v : r \is 'O[R]_3 ->
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

Lemma eigenspace_trmx r (Hr : r \is 'O[R]_3) (n : 'rV[R]_3) :
  (n <= eigenspace r 1 <-> n <= eigenspace r^T 1)%MS.
Proof.
move: (Hr); rewrite orthogonalE => /eqP Hr1.
move: Hr; rewrite orthogonalEC => /eqP Hr2.
split.
  move/eigenspaceP; rewrite scale1r => nrn.
  apply/eigenspaceP; rewrite scale1r.
  by rewrite -{1}nrn -mulmxA mulmxE Hr1 mulmx1.
move/eigenspaceP; rewrite scale1r => nrn.
apply/eigenspaceP; rewrite scale1r.
by rewrite -{1}nrn -mulmxA mulmxE Hr2 mulmx1.
Qed.

Lemma mulmxr_crossmulr_SO r u v : r \is 'SO[R]_3 ->
  (u *v v) *m r = (u *m r) *v (v *m r).
Proof.
rewrite rotationE => /andP[rO /eqP detr1].
by rewrite mulmxr_crossmulr // detr1 scale1r.
Qed.

Lemma det_rotN1 (M : 'M[R]_3) : M \is 'SO[R]_3 -> \det (M - 1) = 0.
Proof.
move=> MSO.
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

Lemma rot_eigen1 (M : 'M[R]_3) : M \is 'SO[R]_3 -> eigenspace M 1 != 0.
Proof.
move/det_rotN1 => /eqP/det0P[n n0]; rewrite mulmxBr mulmx1 => /eqP.
rewrite subr_eq0 => /eqP nM.
apply/rowV0Pn; exists n => //.
apply/sub_kermxP.
by rewrite mulmxBr mulmx1 nM subrr.
Qed.

Lemma euler (M : 'M[R]_3) : M \is 'SO[R]_3 -> {x : 'rV[R]_3 | (x != 0) && (x *m M == x)}.
Proof.
move/rot_eigen1 => H; apply sigW.
case/rowV0Pn : H => x /eigenspaceP Hx x0; exists x.
rewrite scale1r in Hx.
by rewrite x0 /= Hx.
Qed.

Lemma O3_O2 (M : 'M[R]_3) (P : 'M[R]_2) : M = block_mx (1 : 'M_1) 0 0 P ->
  (M \is 'O[R]_3) = (P \is 'O[R]_2).
Proof.
move=> HM.
rewrite HM !orthogonalE (tr_block_mx (1 : 'M_1)) trmx1 2!trmx0.
rewrite -mulmxE (mulmx_block (1 : 'M_1) _ _ _ 1) !(mulmx0,mul0mx,mulmx1,mul1mx,addr0,add0r).
rewrite -[X in (_ == X) = _](@submxK _ 1 2 1 2).
rewrite (_ : ulsubmx _ = 1); last by apply/rowP => i; rewrite !mxE.
rewrite (_ : ursubmx _ = 0); last by apply/rowP => i; rewrite !mxE.
rewrite (_ : dlsubmx _ = 0); last by apply/colP => i; rewrite !mxE.
rewrite (_ : drsubmx _ = 1); last by apply/matrix2P; rewrite !mxE.
rewrite mulmxE; apply/idP/idP => [|/eqP -> //].
by case/eqP/(@eq_block_mx _ 1 2 1 2) => _ _ _ ->.
Qed.

Lemma SO3_SO2 (M : 'M[R]_3) (P : 'M[R]_2) : M = block_mx (1 : 'M_1) 0 0 P ->
  (M \is 'SO[R]_3) = (P \is 'SO[R]_2).
Proof.
move=> ->; by rewrite rotationE (@O3_O2 _ P) // rotationE (@det_lblock _ 1 2) det1 mul1r.
Qed.

End orthogonal_crossmul.

Section norm.

Variables (R : rcfType) (n : nat).
Implicit Types u : 'rV[R]_n.

Definition norm u := Num.sqrt (u *d u).

Lemma normN a : norm (- a) = norm a.
Proof. by rewrite /norm dotmulNv dotmulvN opprK. Qed.

Lemma norm0 : norm 0 = 0.
Proof. by rewrite /norm dotmul0v sqrtr0. Qed.

Lemma norm_delta_mx i : norm 'e_i = 1.
Proof. by rewrite /norm /dotmul trmx_delta mul_delta_mx mxE !eqxx sqrtr1. Qed.

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

Section norm1.

Variable u : 'rV[R]_n.
Hypothesis u1 : norm u = 1.

Lemma dotmul1 : u *m u^T = 1.
Proof.
by rewrite (mx11_scalar 1) mxE eqxx -(expr1n _ 2) -u1 mulr1n -dotmulvv
  -mx11_scalar.
Qed.

End norm1.

End norm.

Lemma orth_preserves_norm R n M : M \is 'O[R]_n.+1 ->
  {mono (fun u => u *m M) : x / norm x }.
Proof. move=> HM v; by rewrite /norm (proj2 (orth_preserves_dotmul M) HM). Qed.

Lemma norm_row_of_O {R : rcfType} n M : M \is 'O[R]_n.+1 -> forall i, norm (row i M) = 1.
Proof.
move=> MSO i.
apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n; apply/eqP.
rewrite -dotmulvv; move/orthogonalP : MSO => /(_ i i) ->; by rewrite eqxx.
Qed.

Section norm2.

Variable R : rcfType.
Implicit Types u : 'rV[R]_2.

Lemma sqr_norm2 u : norm u ^+ 2 = u``_0 ^+ 2 + u``_1 ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum2E -2!expr2. Qed.

End norm2.

Section norm3.

Variable R : rcfType.
Implicit Types u : 'rV[R]_3.

Lemma sqr_norm u : norm u ^+ 2 = u``_0 ^+ 2 + u``_1 ^+ 2 + u``_2%:R ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum3E !expr2. Qed.

Lemma norm_crossmul' u v : (norm (u *v v)) ^+ 2 = (norm u * norm v) ^+ 2 - (u *d v) ^+ 2 .
Proof.
rewrite sqr_norm crossmulE /SimplFunDelta /= !mxE /=.
transitivity (((u``_0)^+2 + (u``_1)^+2 + (u``_2%:R)^+2)
  * ((v``_0)^+2 + (v``_1)^+2 + (v``_2%:R)^+2)
  - (u``_0 * v``_0 + u``_1 * v``_1 + u``_2%:R * v``_2%:R)^+2).
  set u0 := u``_0. set v0 := v``_0.
  set u1 := u``_1. set v1 := v``_1.
  set u2 := u``_2%:R. set v2 := v``_2%:R.
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

Lemma orth_preserves_norm_crossmul M : M \is 'O[R]_3 ->
  {mono (fun u => u *m M) : x y / norm (x *v y)}.
Proof.
move=> MO u v.
by rewrite -[in RHS](orth_preserves_norm MO) mulmxr_crossmulr // normZ orthogonal_det // mul1r.
Qed.

Lemma norm_crossmul_normal u v : u *d v = 0 ->
  norm u = 1 -> norm v = 1 -> norm (u *v v) = 1.
Proof.
move=> uv0 u1 v1; apply/eqP.
rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 //.
by rewrite norm_crossmul' u1 v1 uv0 expr0n /= subr0 mulr1 // norm_ge0.
Qed.

Lemma dotmul_eq0_crossmul_neq0 (u v : 'rV[R]_3) : u != 0 -> v != 0 -> u *d v == 0 -> u *v v != 0.
Proof.
move=> u0 v0 uv0.
rewrite -norm_eq0 -(@eqr_expn2 _ 2) // ?norm_ge0 // exprnP expr0n -exprnP.
rewrite norm_crossmul' (eqP uv0) expr0n subr0 -expr0n eqr_expn2 //.
by rewrite mulf_eq0 negb_or 2!norm_eq0 u0.
by rewrite mulr_ge0 // ?norm_ge0.
Qed.

Lemma crossmul0_dotmul (u v : 'rV[R]_3) : u *v v == 0 -> (u *d v) ^+ 2 = u *d u * (v *d v).
Proof.
rewrite crossmul0E => uv0.
rewrite !dotmulE expr2 !big_distrl /=.
apply eq_bigr => i _; rewrite -!mulrA; congr (_ * _).
rewrite 2!big_distrr /=.
apply eq_bigr => j /= _; rewrite mulrCA !mulrA; congr (_ * _).
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite mulrC.
move/forallP : uv0 => /(_ i)/forallP/(_ j).
by rewrite ij implyTb => /eqP.
Qed.

End norm3.

Lemma orthogonal3P (R : rcfType) (M : 'M[R]_3) :
  (row 0 M *d row 0 M = 1) -> (row 0 M *d row 1 M = 0) -> (row 0 M *d row 2%:R M = 0) ->
  (row 1 M *d row 0 M = 0) -> (row 1 M *d row 1 M = 1) -> (row 1 M *d row 2%:R M = 0) ->
  (row 2%:R M *d row 0 M = 0) -> (row 2%:R M *d row 1 M = 0) -> (row 2%:R M *d row 2%:R M = 1) ->
  M \is 'O[R]_3.
Proof.
move=> H *.
apply/orthogonalP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> //|].
  by rewrite ifnot0 => /orP [] /eqP ->.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case/boolP : (j == 0) => [/eqP -> //|].
  by rewrite ifnot0 => /orP [] /eqP ->.
case/boolP : (j == 0) => [/eqP -> //|].
by rewrite ifnot0 => /orP [] /eqP ->.
Qed.

Lemma matrix_is_orthogonal {R : rcfType} (M : 'M[R]_3) :
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 -> norm (row 2%:R M) = 1 ->
  row 0 M *d row 1 M = 0 -> row 0 M *d row 2%:R M = 0 -> row 1 M *d row 2%:R M = 0 ->
  M \is 'O[R]_3.
Proof.
move=> ni nj nk xy0 xz0 yz0 /=.
apply/orthogonal3P => //; rewrite ?dotmulvv; try by rewrite dotmulC.
by rewrite ni expr1n.
by rewrite nj expr1n.
by rewrite nk expr1n.
Qed.

Lemma matrix_is_rotation {R : rcfType} (M : 'M[R]_3) :
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 ->
  row 0 M *d row 1 M = 0 ->
  row 2%:R M = row 0 M *v row 1 M -> M \is 'SO[R]_3.
Proof.
move=> ni nj xy0 zxy0 /=.
rewrite rotationE; apply/andP; split.
  apply matrix_is_orthogonal => //.
  by rewrite zxy0 norm_crossmul_normal.
  by rewrite zxy0 dotmul_crossmulA crossmulvv dotmul0v.
  by rewrite zxy0 dotmul_crossmulCA crossmulvv dotmulv0.
rewrite (col_mx3_rowE M) det_col_mx3 zxy0 dotmul_crossmulA.
rewrite crossmulC double_crossmul xy0 scale0r add0r opprK dotmulvv.
by rewrite ni expr1n scale1r dotmulvv nj expr1n.
Qed.


Section colinear.

Variable R : rcfType.
Implicit Type u v : 'rV[R]_3.

Definition colinear u v := u *v v == 0.

Lemma scale_colinear k v : colinear (k *: v) v.
Proof. by rewrite /colinear crossmulC linearZ /= crossmulvv scaler0 oppr0. Qed.

Lemma colinear_refl : reflexive colinear.
Proof. move=> ?; by rewrite /colinear crossmulvv. Qed.

Lemma colinear0 u : colinear 0 u.
Proof. by rewrite /colinear crossmul0v. Qed.

Lemma colinear_sym : symmetric colinear.
Proof. by move=> u v; rewrite /colinear crossmulC -eqr_opp opprK oppr0. Qed.

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

Lemma colinearZv u v k : colinear (k *: u) v = (k == 0) || colinear u v.
Proof. by rewrite /colinear crossmulZv scaler_eq0. Qed.

Lemma colinearvZ u v k : colinear u (k *: v) = (k == 0) || colinear u v.
Proof. by rewrite /colinear crossmulvZ scaler_eq0. Qed.

Lemma colinearNv u v : colinear (- u) v = colinear u v.
Proof. by rewrite /colinear crossmulNv eqr_oppLR oppr0. Qed.

End colinear.

Section normalize.

Variables (R : rcfType) (n : nat).
Implicit Type u v : 'rV[R]_3.

Definition normalize v := (norm v)^-1 *: v.

Lemma normalizeN u : normalize (- u) = - normalize u.
Proof. by rewrite /normalize normN scalerN. Qed.

Lemma normalizeI v : norm v = 1 -> normalize v = v.
Proof. by move=> v1; rewrite /normalize v1 invr1 scale1r. Qed.

Lemma norm_normalize v : v != 0 -> norm (normalize v) = 1.
Proof.
move=> v0; rewrite normZ ger0_norm; last by rewrite invr_ge0 // norm_ge0.
by rewrite mulVr // unitfE norm_eq0.
Qed.

Lemma normalize_eq0 v : (normalize v == 0) = (v == 0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite /normalize scaler0.
case/boolP : (v == 0) => [//| /norm_normalize].
rewrite -norm_eq0 => -> /negPn; by rewrite oner_neq0.
Qed.

Lemma norm_scale_normalize u : norm u *: normalize u = u.
Proof.
case/boolP : (u == 0) => [/eqP -> {u}|u0]; first by rewrite norm0 scale0r.
by rewrite /normalize scalerA divrr ?scale1r // unitfE norm_eq0.
Qed.

Lemma normalizeZ u (u0 : u != 0) k (k0 : 0 < k) : normalize (k *: u) = normalize u.
Proof.
rewrite {1}/normalize normZ gtr0_norm // invrM ?unitfE ?gtr_eqF //; last first.
  by rewrite ltr_neqAle norm_ge0 eq_sym norm_eq0 andbT.
by rewrite scalerA -mulrA mulVr ?mulr1 ?unitfE ?gtr_eqF.
Qed.

(* NB: not used *)
Lemma dotmul_normalize_norm u : u *d normalize u = norm u.
Proof.
case/boolP : (u == 0) => [/eqP ->{u}|u0]; first by rewrite norm0 dotmul0v.
rewrite -{1}(norm_scale_normalize u) dotmulZv dotmulvv norm_normalize //.
by rewrite expr1n mulr1.
Qed.

Lemma dotmul_normalize u v : (normalize u *d v == 0) = (u *d v == 0).
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite /normalize scaler0.
apply/idP/idP.
  rewrite /normalize dotmulZv mulf_eq0 => /orP [|//].
  by rewrite invr_eq0 norm_eq0 (negbTE u0).
rewrite /normalize dotmulZv => /eqP ->; by rewrite mulr0.
Qed.

End normalize.

Section axial_normal_decomposition.

Variables (R : rcfType).
Let vector := 'rV[R]_3.
Implicit Type u v : vector.

Definition axialcomp v u := u *d v *: u.

(* normal component of v w.r.t. u *)
Definition normalcomp v u := v - u *d v *: u.

Lemma normalcompvN u v : normalcomp u (- v)  = normalcomp u v.
Proof. by rewrite /normalcomp dotmulNv scaleNr scalerN opprK. Qed.

Lemma decomp v u : v = axialcomp v u + normalcomp v u.
Proof. by rewrite /axialcomp /normalcomp addrC subrK. Qed.

Definition orthogonalize v u := normalcomp v (normalize u).

Lemma normalcomp_colinear v u : normalcomp v u = 0 -> colinear v u.
Proof.
by move/eqP; rewrite subr_eq0 => /eqP ->; rewrite colinearZv ?colinear_refl orbT.
Qed.

Lemma normalcompP u v : u *d normalcomp v (normalize u) = 0.
Proof.
rewrite /normalcomp /normalize dotmulBr !(dotmulZv, dotmulvZ).
rewrite mulrACA -invfM -expr2 dotmulvv mulrCA.
have [->|u_neq0] := eqVneq u 0; first by rewrite dotmul0v mul0r subrr.
by rewrite mulVr ?mulr1 ?subrr // unitfE sqrf_eq0 norm_eq0.
Qed.

Lemma axialnormal v e : norm e = 1 -> axialcomp v e *d normalcomp v e = 0.
Proof.
move=> ne1; rewrite !(dotmulZv, dotmulvZ, dotmulBr) dotmulvv ne1.
by rewrite expr1n mulr1 subrr mulr0.
Qed.

Lemma coorE (p : 'rV[R]_3) i : p``_i = p *d 'e_i.
Proof. by rewrite dotmul_delta_mx. Qed.

Lemma normeE i : norm ('e_i : 'rV_3) = 1 :> R.
Proof. by rewrite norm_delta_mx. Qed.

Lemma vecij : 'e_0 *v 'e_1 = 'e_2%:R :> 'rV[R]__.
Proof. by rewrite vece2 odd_perm3 /= scale1r. Qed.

Lemma vecjk : 'e_1 *v 'e_2%:R = 'e_0%:R :> 'rV[R]__.
Proof. by rewrite vece2 odd_perm3 /= scale1r. Qed.

Lemma vecki : 'e_2%:R *v 'e_0 = 'e_1 :> 'rV[R]__.
Proof. by rewrite vece2 odd_perm3 /= scale1r. Qed.

Lemma vecji : 'e_1 *v 'e_0 = - 'e_2%:R :> 'rV[R]__.
Proof. by rewrite vece2 odd_perm3 /= scaleN1r. Qed.

Lemma veckj : 'e_2%:R *v 'e_1 = - 'e_0 :> 'rV[R]__.
Proof. by rewrite vece2 odd_perm3 /= scaleN1r. Qed.

Lemma vecik : 'e_0 *v 'e_2%:R = - 'e_1 :> 'rV[R]__.
Proof. by rewrite vece2 odd_perm3 /= scaleN1r. Qed.

Lemma ortho_normalcomp u v : u *d v = 0 -> normalcomp u v = u.
Proof. by move=> uv0; rewrite /normalcomp dotmulC uv0 scale0r subr0. Qed.

End axial_normal_decomposition.
