(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From Stdlib Require Import NsatzTactic.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint rat poly.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import perm path fingroup complex.

(******************************************************************************)
(*                    Minor additions to MathComp libraries                   *)
(*                                                                            *)
(* This file contains minor additions ssrbool, ssralg, ssrnum, and complex    *)
(* and more.                                                                  *)
(*                                                                            *)
(*                 u``_i == the ith component of the row vector u             *)
(*      'e_0, 'e_1, 'e_2 == the canonical vectors                             *)
(* Section Nsatz_rcfType == type classes for the Coq nsatz tactic             *)
(*                          (https://coq.inria.fr/refman/addendum/nsatz.html) *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "''e_' i" (format "''e_' i", at level 8, i at level 2).
Reserved Notation "u '``_' i" (at level 3, i at level 2,
  left associativity, format "u '``_' i").

(* TODO: overrides forms.v *)
Notation "u '``_' i" := (u (@GRing.zero _) i) : ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section extra_ssrbool.

Lemma rew_condAr (a b c : bool) : a = b && c -> (b -> c = a).
Proof. by case: b. Qed.

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Inductive and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" :=
  (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.

Lemma and6P (b1 b2 b3 b4 b5 b6 : bool) :
  reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; constructor; try by case.
Qed.

Lemma and9P (b1 b2 b3 b4 b5 b6 b7 b8 b9 : bool) :
  reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8 & b9]
          [&& b1, b2, b3, b4, b5, b6, b7, b8 & b9].
Proof.
by case b1; case b2; case b3; case b4; case b5; case b6; case b7; case b8; case b9;
  constructor; try by case.
Qed.

End extra_ssrbool.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Lemma lift0E m (i : 'I_m.+1) : lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Module Simp.
Ltac ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[ord_max]natr_Zp /=
      |rewrite -[widen_ord _ _]natr_Zp /=
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=
      |rewrite -[_ + _ : 'I__]natr_Zp /=
      |rewrite -[_ * _ : 'I__]natr_Zp /=
      |rewrite -[- _ : 'I__]natr_Zp /=].

Ltac r := rewrite ?(Monoid.simpm,
                    mulr0,mul0r,mul1r,mulr1,addr0,add0r,
                    mulr1n,mulNr,mulrN,opprK,oppr0,
                    scale0r, scaler0, scaleN1r, scale1r,
                    eqxx)/=.

End Simp.

Section extra_ssreflect.

Lemma ifnot01 (i : 'I_2) : (i != 0) = (i == 1).
Proof. by case: i => -[] // []. Qed.

Lemma ifnot01P (i : 'I_2) : (i != 0) <-> (i == 1).
Proof. by rewrite ifnot01. Qed.

Lemma thirdI3 (i j : 'I_3) : i != j -> exists k, (k != i) && (k != j).
Proof.
move=> neq_ij; exists (- i - j).
by case: i j neq_ij => -[i0|[i1|[i2|//]]] [[|[|[]]]].
Qed.

Lemma ifnot0 (i : 'I_3) : (i != 0) = (i == 1) || (i == 2%:R).
Proof. by move: i; do !case=>//. Qed.

Lemma ifnot0P (i : 'I_3) : (i != 0) <-> (i == 1) || (i == 2%:R).
Proof. by rewrite ifnot0. Qed.

Lemma ifnot1 (i : 'I_3) : (i != 1) = (i == 0) || (i == 2%:R).
Proof. by move: i; do !case=>//. Qed.

Lemma ifnot2 (i : 'I_3) : (i != 2%:R) = (i == 0) || (i == 1).
Proof. by move: i; do !case=>//. Qed.

Lemma eqrNxx (R : numDomainType) (x : R) : (-x == x) = (x == 0).
Proof. by rewrite -[RHS](@mulrn_eq0 _ x 2) addr_eq0 eq_sym. Qed.

Lemma eqmxNxx (R : numFieldType) n m (u : 'M[R]_(m, n)) :
  (- u == u) = (u == 0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite oppr0.
by rewrite -subr_eq0 -opprD -mulr2n -scaler_nat oppr_eq0 scaler_eq0 pnatr_eq0.
Qed.

Lemma sqr_normr (R : realDomainType) (k : R) : `| k | ^+ 2 = k ^+ 2.
Proof. by rewrite real_normK ?num_real. Qed.

Lemma ler_norml1 (R : realDomainType) (x y : R) : `|x| <= y -> x <= y.
Proof. by rewrite ler_norml => /andP[]. Qed.

Lemma pnatf_unit (R : numFieldType) n : n.+1%:R \is a @GRing.unit R.
Proof. by rewrite unitfE pnatr_eq0. Qed.

Lemma liftE0 m (i : 'I_m.+2) : fintype.lift i ord0 = (i == 0)%:R.
Proof. by Simp.ord; rewrite -val_eqE /=; case: (val i). Qed.

Lemma liftE1 m (i : 'I_m.+3) : fintype.lift i 1 = (i <= 1).+1%:R.
Proof. by Simp.ord; case: (val i) => [|[]]. Qed.

(*Lemma sum1E_gen {T : ringType} (f : 'I_1 -> T) P : \sum_(i < 1 | P i) f i = (P ord0)%:R * f 0.
Proof.
case/boolP : (P ord0) => P0; rewrite ?(mul1r,mul0r).
  by rewrite (bigD1 ord0) //= big1 ?addr0 // => i; rewrite (ord1 i) eqxx andbF.
by rewrite big1 // => /= i; rewrite (ord1 i) (negbTE P0).
Qed.  *)

Lemma sum1E (T : pzRingType) (f : 'I_1 -> T) : \sum_(i < 1) f i = f 0.
Proof. by rewrite big_ord1. Qed.

Lemma sum2E (T : pzRingType) (f : 'I_2 -> T) : \sum_(i < 2) f i = f 0 + f 1.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma sum3E (T : pzRingType) (f : 'I_3 -> T) : \sum_(i < 3) f i = f 0 + f 1 + f 2%:R.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma sum4E (T : pzRingType) (f : 'I_4 -> T) : \sum_(i < 4) f i = f 0 + f 1 + f 2%:R + f 3%:R.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

End extra_ssreflect.

Section extra_perm3.

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

End extra_perm3.

Notation "''e_' i" := (delta_mx 0 i) : ring_scope.
Local Open Scope ring_scope.

(* algebra lemmas for matrices of size <= 2,3 *)
Section extra_algebra_23.

Lemma matrix2P (T : eqType) (A B : 'M[T]_2) :
  reflect (A = B)
    [&& A 0 0 == B 0 0, A 0 1 == B 0 1, A 1 0 == B 1 0 & A 1 1 == B 1 1].
Proof.
apply (iffP idP); last by move=> ->; rewrite !eqxx.
case/and4P => /eqP ? /eqP ? /eqP ? /eqP ?; apply/matrixP => i j.
case/boolP : (i == 0) => [|/ifnot01P]/eqP->;
  by case/boolP : (j == 0) => [|/ifnot01P]/eqP->.
Qed.

Lemma matrix3P (T : eqType) (A B : 'M[T]_3) :
  reflect (A = B)
    [&& A 0 0 == B 0 0, A 0 1 == B 0 1, A 0 2%:R == B 0 2%:R,
        A 1 0 == B 1 0, A 1 1 == B 1 1, A 1 2%:R == B 1 2%:R,
        A 2%:R 0 == B 2%:R 0, A 2%:R 1 == B 2%:R 1 & A 2%:R 2%:R == B 2%:R 2%:R].
Proof.
apply (iffP idP) => [|]; last by move=> ->; rewrite !eqxx.
case/and9P; do 9 move/eqP => ?; apply/matrixP => i j.
case/boolP : (i == 0) => [|/ifnot0P/orP[]]/eqP->;
  by case/boolP : (j == 0) => [|/ifnot0P/orP[]]/eqP->.
Qed.

Lemma det_mx11 (T : comPzRingType) (A : 'M[T]_1) : \det A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar det_scalar. Qed.

Lemma cofactor_mx22 (T : comPzRingType) (A : 'M[T]_2) i j :
  cofactor A i j = (-1) ^+ (i + j) * A (i + 1) (j + 1).
Proof.
rewrite /cofactor det_mx11 !mxE; congr (_ * A _ _);
by apply/val_inj; move: i j => [[|[|?]]?] [[|[|?]]?].
Qed.

Lemma det_mx22 (T : comPzRingType) (A : 'M[T]_2) : \det A = A 0 0 * A 1 1 -  A 0 1 * A 1 0.
Proof.
rewrite (expand_det_row _ ord0) !(mxE, big_ord_recl, big_ord0).
rewrite !(mul0r, mul1r, addr0) !cofactor_mx22 !(mul1r, mulNr, mulrN).
by rewrite !(lift0E, add0r) /= addrr_pchar2.
Qed.

Lemma cofactor_mx33 (T : comPzRingType) (A : 'M[T]_3) i j :
  cofactor A i j = (-1) ^+ (i + j) *
                   (A (i == 0)%:R (j == 0)%:R * A ((i <= 1).+1%:R) ((j <= 1).+1%:R) -
                    A (i == 0)%:R ((j <= 1).+1%:R) * A ((i <= 1).+1%:R) (j == 0)%:R).
Proof.
rewrite /cofactor det_mx22 !mxE; congr (_ * (A _ _ * A _ _ - A _ _ * A _ _));
  by rewrite (liftE0, liftE1).
Qed.

Lemma det_mx33 (T : comPzRingType) (M : 'M[T]_3) :
  \det M = M 0 0 * (M 1 1 * M 2%:R 2%:R - M 2%:R 1 * M 1 2%:R) +
           M 0 1 * (M 2%:R 0 * M 1 2%:R - M 1 0 * M 2%:R 2%:R) +
           M 0 2%:R * (M 1 0 * M 2%:R 1 - M 2%:R 0 * M 1 1).
Proof.
rewrite (expand_det_row M 0) sum3E -2!addrA; congr (_ * _ + (_ * _ + _ * _)).
  by rewrite cofactor_mx33 /= expr0 mul1r [in X in _ - X]mulrC.
by rewrite cofactor_mx33 /= expr1 mulN1r opprB mulrC.
by rewrite cofactor_mx33 expr2 mulN1r opprK mul1r /= [in X in _ - X]mulrC.
Qed.

Lemma sqr_mxtrace {T : comPzRingType} (M : 'M[T]_3) : (\tr M) ^+ 2 =
  \sum_i (M i i ^+2) + M 0 0 * M 1 1 *+ 2 + (M 0 0 + M 1 1) * M 2%:R 2%:R *+ 2.
Proof.
rewrite /mxtrace sum3E 2!sqrrD sum3E -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
Qed.

Lemma row3P (T : eqType) (A B : 'rV[T]_3) :
  reflect (A = B) [&& A 0 0 == B 0 0, A 0 1 == B 0 1 & A 0 2%:R == B 0 2%:R].
Proof.
apply (iffP idP) => [|]; last by move=> ->; rewrite !eqxx.
case/and3P; do 3 move/eqP => ?; apply/matrixP => i.
by rewrite (ord1 i){i} => j; case/boolP : (j == 0) => [|/ifnot0P/orP[]]/eqP->.
Qed.

End extra_algebra_23.

Section extra_algebra.

Lemma scaler_eq1 (F : fieldType) (R : lmodType F) (k : F) (a : R) :
  a != 0 -> k *: a = a -> k = 1.
Proof.
move=> a0 /eqP; rewrite -{2}(scale1r a) -subr_eq0 -scalerBl.
by rewrite scaler_eq0 (negbTE a0) subr_eq0 orbF => /eqP.
Qed.

Lemma scaler_eqN1 (F : fieldType) (R : lmodType F) (k : F) (a : R) :
  a != 0 -> - k *: a = a -> k = - 1.
Proof. by move=> a0 /scaler_eq1 => /(_ a0) /eqP; rewrite eqr_oppLR => /eqP. Qed.

Lemma mxE_col_row (T : Type) n (M : 'M[T]_n) i j : M i j = (col j (row i M)) 0 0.
Proof. by rewrite !mxE. Qed.

Variable R : pzRingType.

Lemma col_mx_row_mx m1 n1 (A : 'M[R]_(m1, n1)) n2 m2 :
  col_mx (row_mx A (0 : 'M_(m1, n2))) (0 : 'M_(m2, n1 + n2)) = row_mx (col_mx A 0) 0.
Proof.
set a : 'M_(m2, _ + n2) := 0.
have -> : a = row_mx (0 : 'M_(m2, n1)) 0 by rewrite row_mx0.
by rewrite -block_mxEv block_mxEh col_mx0.
Qed.

Definition mx_lin1 n (M : 'M[R]_n) : {linear 'rV[R]_n -> 'rV[R]_n} :=
  @mulmxr R 1 n n M.

Definition lin1_mx' n (f : {linear 'rV[R]_n -> 'rV[R]_n}) :
  {M : {linear 'rV[R]_n -> 'rV[R]_n} & forall x, f x = M x}.
Proof.
by exists f.
Defined.

Lemma mulmx_trE n (v : 'rV[R]_n) i j : (v^T *m v) i j = v 0 i * v 0 j.
Proof.
by rewrite mxE (bigD1 ord0) //= big1 ?mxE ?addr0 // => i0; rewrite (ord1 i0).
Qed.

End extra_algebra.

Section extra_complex.

Variable R : rcfType.
Implicit Types x : R[i].
Implicit Types a b k : R.

Lemma opp_conjc a b : (- (a -i* b) = (- a +i* b))%C.
Proof. by apply/eqP; rewrite eq_complex /= opprK !eqxx. Qed.

Lemma Re_scale x k : k != 0 -> complex.Re (x / k%:C%C) = complex.Re x / k.
Proof.
move=> k0; case: x => a b /=.
rewrite expr0n /= addr0 mul0r -mulrN opprK mulr0 addr0.
by rewrite expr2 invrM // ?unitfE // (mulrA k) divff // mul1r.
Qed.

Lemma ReNiIm x : complex.Re (x * - 'i%C) = complex.Im x.
Proof. by case: x => a b; simpc. Qed.

Lemma complexZ1 a b k : ((k * a) +i* (k * b) = k%:C * (a +i* b))%C.
Proof. by simpc. Qed.

Lemma complexZ2 a b k : ((k * a) -i* (k * b) = k%:C * (a -i* b))%C.
Proof. by simpc. Qed.

Lemma ReZ x k : complex.Re (k%:C%C * x) = k * complex.Re x.
Proof. case: x => a b /=; by rewrite mul0r subr0. Qed.

Lemma ImZ x k : complex.Im ((k%:C)%C * x) = k * complex.Im x.
Proof. by case: x => a b /=; rewrite mul0r addr0. Qed.

Definition complexZ := (complexZ1, @complexZ2).

Lemma normci : `|'i| = 1 :> R[i].
Proof. by rewrite normc_def /= expr0n add0r expr1n sqrtr1. Qed.

End extra_complex.

Section Nsatz_rcfType.
Variable T : rcfType.

Lemma Nsatz_rcfType_Setoid_Theory : Setoid_Theory T (@eq T).
Proof. by constructor => [x //|x y //|x y z ->]. Qed.

Definition Nsatz_rcfType0 := (0%:R : T).
Definition Nsatz_rcfType1 := (1%:R : T).
Definition Nsatz_rcfType_add (x y : T) := (x + y)%R.
Definition Nsatz_rcfType_mul (x y : T) := (x * y)%R.
Definition Nsatz_rcfType_sub (x y : T) := (x - y)%R.
Definition Nsatz_rcfType_opp (x  : T) := (- x)%R.

#[global]
Instance Nsatz_rcfType_Ring_ops: (@Ring_ops T Nsatz_rcfType0 Nsatz_rcfType1
  Nsatz_rcfType_add
  Nsatz_rcfType_mul
  Nsatz_rcfType_sub
  Nsatz_rcfType_opp (@eq T)).
Defined.

#[global]
Instance Nsatz_rcfType_Ring : (Ring (Ro:=Nsatz_rcfType_Ring_ops)).
Proof.
constructor => //.
- exact: Nsatz_rcfType_Setoid_Theory.
- by move=> x y -> x1 y1 ->.
- by move=> x y -> x1 y1 ->.
- by move=> x y -> x1 y1 ->.
- by move=> x y ->.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulr1.
- exact: mulrA.
- exact: mulrDl.
- move=> x y z; exact: mulrDr.
- exact: subrr.
Defined.

#[global]
Instance Nsatz_rcfType_Cring: (Cring (Rr:=Nsatz_rcfType_Ring)).
Proof. exact: mulrC. Defined.

#[global]
Instance Nsatz_rcfType_Integral_domain : (Integral_domain (Rcr:=Nsatz_rcfType_Cring)).
Proof.
constructor.
  move=> x y.
  rewrite -[_ _ zero]/(x * y = 0)%R => /eqP.
  by rewrite mulf_eq0 => /orP[] /eqP->; [left | right].
rewrite -[_ _ zero]/(1 = 0)%R; apply/eqP.
by rewrite (eqr_nat T 1 0).
Defined.

End Nsatz_rcfType.
