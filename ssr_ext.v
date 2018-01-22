(* coq-robot (c) 2017 AIST and INRIA. License: LGPL v3. *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp
Require Import eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrnum ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup complex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
 OUTLINE:
 1. Section extra_ssrbool
 2. various lemmas about ssralg and ssrnum
 3. section extra_perm3
 4. Section extra_linear
    notation 'e_i
 5. Section extra_complex
*)

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

Lemma ifnot01 (i : 'I_2) : (i != 0) = (i == 1).
Proof. by case: i => -[] // []. Qed.

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

Lemma Neqxx (R : realDomainType) (x : R) : (-x == x) = (x == 0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite oppr0.
by rewrite -subr_eq0 -opprD -mulr2n -mulNrn mulrn_eq0 /= eqr_oppLR oppr0.
Qed.

Lemma Neqxx_mat (R : rcfType) n m (u : 'M[R]_(m, n)) : (- u == u) = (u == 0).
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

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
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
                    eqxx).

End Simp.

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

Lemma sum1E (T : ringType) (f : 'I_1 -> T) : \sum_(i < 1) f i = f 0.
Proof. by rewrite big_ord1. Qed.

Lemma sum2E (T : ringType) (f : 'I_2 -> T) : \sum_(i < 2) f i = f 0 + f 1.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma sum3E (T : ringType) (f : 'I_3 -> T) : \sum_(i < 3) f i = f 0 + f 1 + f 2%:R.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma sum4E (T : ringType) (f : 'I_4 -> T) : \sum_(i < 4) f i = f 0 + f 1 + f 2%:R + f 3%:R.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

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

Reserved Notation "u '``_' i"
    (at level 3, i at level 2, left associativity, format "u '``_' i").
Notation "u '``_' i" := (u (GRing.zero (Zp_zmodType O)) i) : ring_scope.
Notation "''e_' i" := (delta_mx 0 i)
 (format "''e_' i", at level 3) : ring_scope.
Local Open Scope ring_scope.

Section extra_linear.

Lemma row_mx_eq0 (M : ringType) (m n1 n2 : nat)
 (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (M : ringType) (m1 m2 n : nat)
 (A1 : 'M[M]_(m1, n)) (A2 : 'M_(m2, n)):
 (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
by rewrite -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx0 tr_col_mx row_mx_eq0.
Qed.

Lemma col_mx_row_mx (T : ringType) (m1 n1 : nat) (A : 'M[T]_(m1, n1)) n2 m2 :
  col_mx (row_mx A (0 : 'M_(m1, n2))) (0 : 'M_(m2, n1 + n2)) = row_mx (col_mx A 0) 0.
Proof.
set a : 'M_(m2, _ + n2) := 0.
have -> : a = row_mx (0 : 'M_(m2, n1)) 0 by rewrite row_mx0.
by rewrite -block_mxEv block_mxEh col_mx0.
Qed.

Definition mx_lin1 (R : ringType) n (M : 'M[R]_n) : {linear 'rV[R]_n -> 'rV[R]_n} :=
  mulmxr_linear 1 M.

(* courtesy of GG *)
Lemma mxdirect_delta (F : fieldType) (T : finType) (n : nat) (P : pred T) f :
  {in P & , injective f} ->
  mxdirect (\sum_(i | P i) <<'e_(f i) : 'rV[F]_n>>)%MS.
Proof.
pose fP := image f P => Uf; have UfP: uniq fP by apply/dinjectiveP.
suffices /mxdirectP: mxdirect (\sum_i <<'e_i : 'rV[F]_n>>).
  rewrite /= !(bigID [mem fP] predT) -!big_uniq //= !big_map !big_filter.
  by move/mxdirectP; rewrite mxdirect_addsE => /andP[].
apply/mxdirectP=> /=; transitivity (mxrank (1%:M : 'M[F]_n)).
  apply/eqmx_rank; rewrite submx1 mx1_sum_delta summx_sub_sums // => i _.
  by rewrite -(mul_delta_mx (0 : 'I_1)) genmxE submxMl.
rewrite mxrank1 -[LHS]card_ord -sum1_card.
by apply/eq_bigr=> i _; rewrite /= mxrank_gen mxrank_delta.
Qed.

End extra_linear.

Section extra_complex.

Variable R : rcfType.

Lemma opp_conjc (a b : R) : (- (a -i* b) = (- a +i* b))%C.
Proof. by apply/eqP; rewrite eq_complex /= opprK !eqxx. Qed.

Lemma Re_scale (x : R[i]) (k : R) : k != 0 -> complex.Re (x / k%:C%C) = complex.Re x / k.
Proof.
move=> k0; case: x => a b /=.
rewrite expr0n /= addr0 mul0r -mulrN opprK mulr0 addr0.
by rewrite expr2 invrM // ?unitfE // (mulrA k) divff // mul1r.
Qed.

Lemma complexZ1 (a b k : R) : ((k * a) +i* (k * b) = k%:C * (a +i* b))%C.
Proof. by simpc. Qed.

Lemma complexZ2 (a b k : R) : ((k * a) -i* (k * b) = k%:C * (a -i* b))%C.
Proof. by simpc. Qed.

Lemma ReZ (x : R[i]) (k : R) : complex.Re (k%:C%C * x) = k * complex.Re x.
Proof. case: x => a b /=; by rewrite mul0r subr0. Qed.

Lemma ImZ (x : R[i]) (k : R) : complex.Im ((k%:C)%C * x) = k * complex.Im x.
Proof. by case: x => a b /=; rewrite mul0r addr0. Qed.

Definition complexZ := (complexZ1, @complexZ2).

End extra_complex.
