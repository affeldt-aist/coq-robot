Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Lemma mxdirect_delta (F : fieldType) (T : finType)
  (n : nat) (P : pred T) (f : T -> 'I_n) :
  {in P & , injective f} ->
  mxdirect (\sum_(i | P i) <<delta_mx 0 (f i) : 'rV[F]_n>>)%MS.
Proof.
move=> f_inj; apply/mxdirectP => /=.
transitivity (\rank (\sum_(j | P j) (delta_mx (f j) (f j) : 'M[F]_n))).
  apply: eqmx_rank; apply/genmxP; rewrite !genmx_sums.
  apply/eq_bigr => i Pi; rewrite genmx_id.
  apply/genmxP/andP; split; apply/submxP.
    by exists (delta_mx 0 (f i)); rewrite mul_delta_mx.
  by exists (delta_mx (f i) 0); rewrite mul_delta_mx.
rewrite (mxdirectP _) /=.
  by apply: eq_bigr => i _; rewrite /= mxrank_gen !mxrank_delta.
apply/mxdirect_sumsP => /= s Ps.
apply/eqP; rewrite -submx0; apply/rV_subP => u.
rewrite sub_capmx => /andP [/submxP [x ->]].
move=> /(submxMr (delta_mx (f s) (f s))).
rewrite sumsmxMr_gen big1; first by rewrite -mulmxA mul_delta_mx.
move=> i /andP [Pi neq_is]; rewrite mul_delta_mx_0 ?genmx0 //.
by apply: contraNneq neq_is => /f_inj ->.
Qed.

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

End extra.

Section delta.

Import GroupScope.

Fact perm_of_2seq_key : unit. Proof. exact: tt. Qed.
Definition perm_of_2seq :=
  locked_with perm_of_2seq_key
  (fun (T : eqType) n (si so : n.-tuple T) =>
  if (perm_eq si so =P true) isn't ReflectT ik then 1%g
  else sval (sig_eqW (tuple_perm_eqP ik))).
Canonical perm_of_2seq_unlockable := [unlockable fun perm_of_2seq].

Lemma perm_of_2seqE n (T : eqType) (si so : n.-tuple T) (j : 'I_n) :
  perm_eq si so -> tnth so (perm_of_2seq si so j) = tnth si j.
Proof.
rewrite [perm_of_2seq]unlock; case: eqP => // H1 H2.
case: sig_eqW => /= s; rewrite /tnth => -> /=.
by rewrite (nth_map j) ?size_enum_ord // nth_ord_enum.
Qed.

(* Definition perm_of_2seq (T : eqType) n (si : seq T) (so : seq T) : 'S_n := *)
(*   if (size so == n) =P true isn't ReflectT so_n then 1%g *)
(*   else if (perm_eq si (Tuple so_n) =P true) isn't ReflectT ik then 1%g *)
(*   else sval (sig_eqW (tuple_perm_eqP ik)). *)

(* Lemma perm_of_2seqE n (T : eqType) (si so : n.-tuple T) (j : 'I_n) : *)
(*   perm_eq si so -> tnth so (perm_of_2seq n si so j) = tnth si j. *)
(* Proof. *)
(* rewrite /perm_of_2seq; case: eqP => // so_n p_si_so; last first. *)
(*   by rewrite size_tuple eqxx in so_n. *)
(* case: eqP => // ?; case: sig_eqW => /= s; rewrite /tnth => -> /=. *)
(* rewrite (nth_map j) ?size_enum_ord // nth_ord_enum /=. *)
(* by apply: set_nth_default; rewrite size_tuple. *)
(* Qed. *)

Lemma perm_of_2seqV n (T : eqType) (si so : n.-tuple T) : uniq si ->
  (perm_of_2seq si so)^-1%g = perm_of_2seq so si.
Proof.
move=> uniq_si.
apply/permP => /= j.
apply/val_inj/eqP => /=.
rewrite -(@nth_uniq _ (tnth_default si j) (val si)) //=; last 2 first.
- by rewrite size_tuple.
- by rewrite size_tuple.
rewrite [perm_of_2seq]unlock; case: eqP => p; last first.
  case: eqP => // p0; by [rewrite perm_eq_sym p0 in p | rewrite invg1].
case: eqP => [p'|]; last by rewrite perm_eq_sym {1}p.
case: sig_eqW => /= x Hx; case: sig_eqW => /= y Hy.
rewrite {1}Hx (nth_map j); last by rewrite size_enum_ord.
rewrite nth_ord_enum permE f_iinv /tnth Hy (nth_map j); last by rewrite size_enum_ord.
rewrite nth_ord_enum /tnth; apply/eqP/set_nth_default;  by rewrite size_tuple.
Qed.

Variable R : ringType.
Local Open Scope ring_scope.

Definition delta (i k : seq nat) : R :=
  if (perm_eq i k) && (uniq i) then
  (-1) ^+ perm_of_2seq (insubd (in_tuple k) i) (in_tuple k) else 0.

Lemma deltaE n (i k : seq nat) (si : size i = n) (sk : size k = n) : 
   let T l (P : size l = n)  := Tuple (appP eqP idP P) in
   delta i k = if (perm_eq i k) && (uniq i)
               then (-1) ^+ perm_of_2seq (T _ si) (T _ sk) else 0.
Proof.
move=> T; rewrite /delta; have [/andP [pik i_uniq]|//] := ifP.
set i' := insubd _ _; set k' := in_tuple _.
have [] : (i' = T _ si :> seq _ /\ k' = T _ sk :> seq _).
  by rewrite /= val_insubd /= (perm_eq_size pik) eqxx.
move: i' k' (T i si) (T k sk) => /=.
by case: _ / sk => ??????; congr (_ ^+ perm_of_2seq _ _); apply: val_inj.
Qed.

(* Definition deltaE n (i k : seq nat) (si : size i == n) (sk : size k == n) := *)
(*   deltaE (Tuple si) (Tuple sk). *)

(* Lemma delta_cast n (i k : seq nat) (ni : size i = n) (nk : size k = n) : *)
(*   delta i k = delta (Tuple (appP eqP idP ni)) (Tuple (appP eqP idP nk)). *)

Lemma delta_0 (i : seq nat) k : (~~ uniq i) || (~~ uniq k) -> delta i k = 0.
Proof.
case/orP => [Nui|Nuk]; rewrite /delta; case: ifP => // /andP[pik ui].
  by rewrite (negbTE Nui) in ui.
by rewrite -(perm_eq_uniq pik) ui in Nuk.
Qed.

(* Definition scast {m n : nat} (eq_mn : m = n) (s : 'S_m) : 'S_n := *)
(*   ecast n ('S_n) eq_mn s. *)

(* Lemma tcastE (m n : nat) (eq_mn : m = n) (t : 'S_m) (i : 'I_n), *)
(*    tnth (tcast eq_mn t) i = tnth t (cast_ord (esym eq_mn) i) *)
(* tcast_id *)
(*    forall (T : Type) (n : nat) (eq_nn : n = n) (t : n.-tuple T), *)
(*    tcast eq_nn t = t *)
(* tcastK *)
(*    forall (T : Type) (m n : nat) (eq_mn : m = n), *)
(*    cancel (tcast eq_mn) (tcast (esym eq_mn)) *)
(* tcastKV *)
(*    forall (T : Type) (m n : nat) (eq_mn : m = n), *)
(*    cancel (tcast (esym eq_mn)) (tcast eq_mn) *)
(* tcast_trans *)
(*    forall (T : Type) (m n p : nat) (eq_mn : m = n)  *)
(*      (eq_np : n = p) (t : m.-tuple T), *)
(*    tcast (etrans eq_mn eq_np) t = tcast eq_np (tcast eq_mn t) *)
(* L *)

(* Lemma perm_of_2seq_tcast (T : eqType) n m i (k : m.-tuple T) (eq_mn : m = n): *)
(*   perm_of_2seq i (tcast eq_mn k) = scast eq_mn (perm_of_2seq i k). *)

Lemma perm_of_2seq_ii n (i : n.-tuple nat) : perm_of_2seq i i = 1%g.
Proof. Admitted.

Lemma deltaii (i : seq nat) : uniq i -> delta i i = 1.
Proof.
move=> i_uniq; rewrite !(@deltaE (size i)) .
by rewrite perm_eq_refl i_uniq /= perm_of_2seq_ii odd_perm1.
Qed.

Lemma deltaC i k : delta i k = delta k i.
Proof.
have [pik|pik] := boolP (perm_eq i k); last first.
  by rewrite /delta (negPf pik) perm_eq_sym (negPf pik).
have [uk|Nuk] := boolP (uniq k); last by rewrite !delta_0 // Nuk ?orbT.
have si := (perm_eq_size pik); rewrite !(@deltaE (size k)) //.
rewrite pik /= perm_eq_sym pik (perm_eq_uniq pik) uk /=.
by rewrite -perm_of_2seqV // odd_permV.
Qed.

(* Lemma deltaN1 (i : seq nat) k : uniq i -> *)
(*   perm_of_2seq i (in_tuple k) -> delta i k = -1. *)
(* Proof. *)
(* move=> ui; rewrite /delta /perm_of_2seq ui. *)
(* case: eqP => [p|]; last by rewrite odd_perm1. *)
(* case: sig_eqW => /= x ih Hx; by rewrite p Hx expr1. *)
(* Qed. *)

(* Lemma delta_1 (i : seq nat) k : uniq i -> perm_eq i k ->  *)
(*  ~~ perm_of_2seq i (in_tuple k) -> delta i k = 1. *)
(* Proof. *)
(* move=> ui ik. *)
(* rewrite /delta /perm_of_2seq ui. *)
(* case: eqP => [p|]. *)
(*   case: sig_eqW => /= x ih Hx. *)
(*   by rewrite p (negPf Hx) expr0. *)
(* by rewrite ik. *)
(* Qed. *)

Lemma perm_of_2seq_comp n {T: eqType} (s1 s2 s3 : n.-tuple T) :
  uniq s3 -> perm_eq s1 s2 -> perm_eq s2 s3 ->
  (perm_of_2seq s1 s2 * perm_of_2seq s2 s3)%g = perm_of_2seq s1 s3.
Proof.
move=> us3 s12 s23; have s13 := perm_eq_trans s12 s23.
apply/permP => /= i; rewrite permE /=; apply/val_inj/eqP => /=.
rewrite -(@nth_uniq _ (tnth_default s1 i) s3) ?size_tuple // -!tnth_nth.
by rewrite !perm_of_2seqE.
Qed.

Lemma delta_comp (i j k : seq nat) :
  uniq k -> perm_eq i j -> perm_eq j k ->
  delta i k = delta i j * delta j k.
Proof.
move=> uk pij pjk; have pik := perm_eq_trans pij pjk.
have [sj si] := (perm_eq_size pjk, perm_eq_size pik).
rewrite !(@deltaE (size k)) pik pij pjk /=.
rewrite (perm_eq_uniq pij) (perm_eq_uniq pjk) uk.
by rewrite -signr_addb -odd_permM perm_of_2seq_comp.
Qed.

End delta.

Section Normal.

Lemma submx_add_cap (F : fieldType) (m1 m2 m3 n : nat)
   (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A :&: B + A :&: C <= A :&: (B + C))%MS.
Proof.
apply/rV_subP => x /sub_addsmxP [[u v] /= ->]; rewrite sub_capmx.
by rewrite addmx_sub_adds ?addmx_sub ?mulmx_sub ?capmxSl ?capmxSr.
Qed.

Lemma submx_sum_cap (F : fieldType) (k m1 n : nat)
   (A : 'M[F]_(m1, n)) (B_ : 'I_k -> 'M_n) :
   (\sum_i (A :&: B_ i) <= A :&: \sum_i B_ i)%MS.
Proof.
elim/big_ind2: _; rewrite ?capmx0 => //=.
by move=> ???? /addsmxS H /H /submx_trans -> //; apply: submx_add_cap.
Qed.

Variable (R : fieldType) (n : nat).

Print Canonical Projections.

Let dim := #|{set 'I_n}|.
Definition exterior := 'rV[R]_dim.
Canonical exterior_eqType := [eqType of exterior].
Canonical exterior_choiceType := [choiceType of exterior].
Canonical exterior_zmodType := [zmodType of exterior].

Definition sign (A B : {set 'I_n}) : R :=
  let s (A : {set 'I_n}) := [seq val x | x <- enum A] in
  let deltas s := delta R s (sort leq s) in
  deltas (s A) * deltas (s B) * deltas (s (A :|: B)).

Lemma signND (A B : {set 'I_n}) : ~~ [disjoint A & B] -> sign A B = 0.
Proof. Admitted.

Definition mul_ext (u v : exterior) : exterior :=
    \sum_(su : {set 'I_n})
    \sum_(sv : {set 'I_n})
      (u 0 (enum_rank su) * v 0 (enum_rank sv) * sign su sv)
        *: delta_mx 0 (enum_rank (su :|: sv)).
Local Notation "*w%R" := (@mul_ext _).
Local Notation "u *w w" := (mul_ext u w) (at level 40).

Definition extn r : 'M[R]_dim :=
 (\sum_(s : {set 'I_n} | #|s| == r) <<delta_mx 0 (enum_rank s) : 'rV[R]_dim>>)%MS.

Lemma dim_extn r : \rank (extn r) = 'C(n, r).
Proof.
rewrite (mxdirectP _) /=; last first.
  by rewrite mxdirect_delta // => i ???; apply: enum_rank_inj.
rewrite (eq_bigr (fun=> 1%N)); last first.
  by move=> s _; rewrite mxrank_gen mxrank_delta.
by rewrite sum1dep_card card_draws card_ord.
Qed.

Lemma dim_exterior : \rank (1%:M : 'M[R]_dim) = (2 ^ n)%N.
Proof.
rewrite mxrank1 /dim (@eq_card _ _ (mem (powerset [set: 'I_n]))); last first.
  by move=> A; rewrite !inE subsetT.
by rewrite card_powerset cardsT card_ord.
Qed.

Lemma mxdirect_extn : mxdirect (\sum_(i < n.+1) extn i).
Proof.
have card_small (A : {set 'I_n}) : #|A| < n.+1.
  by rewrite ltnS (leq_trans (max_card _)) ?card_ord.
apply/mxdirectP=> /=; rewrite -(@partition_big _ _ _ _ _ xpredT 
          (fun A => Ordinal (card_small A)) xpredT) //=.
rewrite (mxdirectP _) ?mxdirect_delta //=; last by move=> ????/enum_rank_inj.
by rewrite (@partition_big _ _ _ _ _ xpredT 
          (fun A => Ordinal (card_small A)) xpredT) //=.
Qed.

Lemma extnn : (\sum_(i < n.+1) extn i :=: 1%:M)%MS.
Proof.
apply/eqmxP; rewrite -mxrank_leqif_eq ?submx1 // dim_exterior /extn.
rewrite (expnDn 1 1) (mxdirectP _) /=; last exact mxdirect_extn.
apply/eqP/eq_bigr => i _; rewrite (eq_bigr (fun=> 1%N)); last first.
  by move=> A _; rewrite mxrank_gen mxrank_delta.
by rewrite sum1dep_card /= card_draws card_ord !exp1n !muln1.
Qed.

Lemma mul_extnE (u v : exterior) r s : (u <= extn r)%MS -> (v <= extn s)%MS ->
  (u *w v)  = 0.

Lemma mul_extE (u v : exterior) (A : {set 'I_n}) :
  (u *w v) 0 (enum_rank A) = 
  \sum_(s in powerset A)
   (u 0 (enum_rank s) * v 0 (enum_rank (A :\: s)) * sign s (A :\: s)).
Proof.
have bm := (@big_morph _ _ (fun M : 'M__ => M 0 _) 0 +%R); move=> [:mid mop].
rewrite [LHS]bm; last first.
- by abstract: mid; rewrite mxE.
- by abstract: mop; move=> ??; rewrite mxE.
rewrite (bigID (mem (powerset A))) /= [X in _ + X]big1 ?addr0 /=; last first.
  move=> su; rewrite inE => NsuA.
  rewrite bm ?big1 => // sv _; rewrite !mxE /= [_ == _]negbTE ?mulr0 //.
  by apply: contraNneq NsuA => /enum_rank_inj ->; rewrite subsetUl.
apply: eq_bigr => su suA; rewrite bm // (bigD1 (A :\: su)) //= big1 ?addr0.
  rewrite setDE setUIr -setDE setUCr setIT (setUidPr _) -?powersetE //.
  by rewrite !mxE ?eqxx ?mulr1.
move=> sv svNADsu; rewrite !mxE /=.
have [duv|Nduv]:= boolP [disjoint su & sv]; last first.
  by rewrite signND ?(mulr0,mul0r).
rewrite [_ == _]negbTE ?mulr0 //.
apply: contraNneq svNADsu => /enum_rank_inj ->.
by rewrite setDUl setDv set0U (setDidPl _) // disjoint_sym.
Qed.


Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS (at level 69).

Lemma normal_sym k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) :
  A _|_ B = B _|_ A.
Proof.
rewrite !(sameP sub_kermxP eqP) -{1}[A]trmxK -trmx_mul.
by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma normalNm k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : (- A) _|_ B = A _|_ B.
Proof. by rewrite eqmx_opp. Qed.

Lemma normalmN k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : A _|_ (- B) = A _|_ B.
Proof. by rewrite ![A _|_ _]normal_sym normalNm. Qed.

Lemma normalDm k m p (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) (C : 'M[R]_(p,n)) :
  (A + B _|_ C) = (A _|_ C) && (B _|_ C).
Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed.

Lemma normalmD  k m p (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) (C : 'M[R]_(p,n)) :
  (A _|_ B + C) = (A _|_ B) && (A _|_ C).
Proof. by rewrite ![A _|_ _]normal_sym normalDm. Qed.

Definition dotmul (u v : 'rV[R]_n) : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE (u v : 'rV[R]_n) : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma normalvv (u v : 'rV[R]_n) : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

End Normal.

Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS (at level 69).
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Section Crossproduct.

Variable (R : fieldType) (n' : nat).
Let n := n'.+1.

Definition cross (u : 'M[R]_(n',n)) : 'rV_n  :=
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

Lemma cross_multilinear (A B C : 'M_(n',n)) (i0 : 'I_n') (b c : R) :
 row i0 A = b *: row i0 B + c *: row i0 C ->
 row' i0 B = row' i0 A ->
 row' i0 C = row' i0 A -> cross A = b *: cross B + c *: cross C.
Proof.
move=> rABC rBA rCA; apply/rowP=> k; rewrite !mxE.
apply: (@determinant_multilinear _ _ _ _ _ (fintype.lift 0 i0));
do ?[apply/matrixP => i j; rewrite !mxE; case: splitP => //= l;
     rewrite ?ord1 ?mxE //].
- by move=> [] /val_inj <-;
  have := congr1 (fun M : 'M__ => M 0 j) rABC; rewrite !mxE.
Admitted.

Lemma dot_cross (u : 'rV[R]_n) (V : 'M[R]_(n',n)) :
  u *d (cross V) = \det (col_mx u V).
Proof.
rewrite dotmulE (expand_det_row _ 0); apply: eq_bigr => k _; rewrite !mxE /=.
case: splitP => j //=; rewrite ?ord1 //= => _ {j}; congr (_ * _).
rewrite (expand_det_row _ 0) (bigD1 k) //= big1 ?addr0; last first.
  move=> i neq_ik; rewrite !mxE; case: splitP=> //= j.
  by rewrite ord1 mxE (negPf neq_ik) mul0r.
rewrite !mxE; case: splitP => //= j _; rewrite ord1 !mxE !eqxx mul1r.
rewrite !expand_cofactor; apply: eq_bigr => s s0; congr (_ * _).
apply: eq_bigr => i; rewrite !mxE.
by case: splitP => //= j'; rewrite ord1 {j'} -val_eqE => /= ->.
Qed.

Lemma dotmulC (u v : 'rV[R]_n) : u *d v = v *d u.
Proof. by rewrite /dotmul -{1}[u]trmxK -trmx_mul mxE. Qed.

Lemma crossmul_normal (A : 'M[R]_(n',n)) : A _|_ cross A.
Proof.
apply/rV_subP => v /submxP [M ->]; rewrite normalvv dot_cross; apply/det0P.
exists (row_mx (- 1) M); rewrite ?row_mx_eq0 ?oppr_eq0 ?oner_eq0 //.
by rewrite mul_row_col mulNmx mul1mx addNr.
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
rewrite -[M]trmxK [M^T]matrix_sum_delta.
rewrite !linear_sum /=; apply: eq_bigr=> i _.
rewrite !linear_sum /=; apply: eq_bigr=> j _.
rewrite !mxE !linearZ /= trmx_delta.
rewr
rewrite -[in RHS]/(crossmulr _ _).
rewrite linear_sum /= /crossmu.
rewrite 

apply/rowP => k; rewrite !mxE.
rewrite -![_ *v _](mul_rV_lin1 [linear of crossmulr _]).
rewrite -!mulmxA.
rewrite mul_rV_lin.
rewrite -!(mul_rV_lin1 [linear of crossmulr (v * M)]).

rewrite -/(mulmxr _ _) -!(mul_rV_lin1 [linear of mulmxr M]).
rewrite -!(mul_rV_lin1 [linear of crossmulr v]).

rewrite -!/(crossmulr _ _).
rewrite -!(mul_rV_lin1 [linear of crossmulr v]).

 /mulmxr. mul_rV_lin1.
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

Lemma double_crossmul (u v w : 'rV[R]_n) :
 u *v (v *v w) = (u *d w) *: v - (u *d v) *: w.
Proof.
have [->|u_neq0] := eqVneq u 0.
  by rewrite crossmul0v !dotmul0v !scale0r subr0.
have : exists M : 'M_n, u *m M = delta_mx 0 0.

rewrite !crossmulE; apply/rowP => i.
rewrite !dotmulE !(big_ord_recl, big_ord0, addr0) !mxE /=.
simpr; rewrite oppr0 opprB addr0.
by case: i => [[|[|[|?]]]] ? //=; simp_ord => //=; rewrite mulrC ?subrr.
Qed.

rewrite !mulrDl !mulrBr !mulrA ?opprB.
apply/rowP => i.
have : i \in [:: ord0 ; 1 ; 2%:R].
  have : i \in enum 'I_n by rewrite mem_enum.
  rewrite n!enum_ordS (_ : enum 'I_0 = nil) // -enum0.
  apply eq_enum => i'; by move: (ltn_ord i').
rewrite inE; case/orP => [/eqP ->|].
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite n!big_ord_recl big_ord0 !mxE.
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
  do 2 rewrite n!big_ord_recl big_ord0 !mxE.
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
  do 2 rewrite n!big_ord_recl big_ord0 !mxE.
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

Record homogeneous_spec (A B : frame) : Type := {
  rotation : 'M[R]_n ;
  position : vec A }.

Definition homogeneous_mx A B (T : homogeneous_spec A B) : 'M[R]_4 :=
  row_mx (col_mx (rotation T) 0) (col_mx (let: Vec x := position T in x^T) 1).

Definition homogeneous_trans A B (T : homogeneous_spec A B) (x : vec B) : vec A :=
  Vec _ (\row_(i < n) (homogeneous_mx T *m col_mx (let: Vec x' := x in x'^T) 1)^T 0 (inord i)).


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
