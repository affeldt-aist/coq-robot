From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum matrix interval.
From mathcomp Require Import poly archimedean generic_quotient ring_quotient.
From mathcomp Require Import interval_inference.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import contra functions constructive_ereal reals.
From mathcomp Require Import topology prodnormedzmodule tvs normedtype.
From mathcomp Require Import landau ereal sequences derive numfun measure.
From mathcomp Require Import realfun lebesgue_measure lebesgue_integral ftc.
Require Import tilt_analysis ode_common ode_contfun.

(**md**************************************************************************)
(* # Proof of the Cauchy-Lipschitz theorem                                    *)
(*                                                                            *)
(* The main purpose of this file is to formalized the Cauchy-Lipschitz        *)
(* theorem (a.k.a. Picard-Lindelof).                                          *)
(*                                                                            *)
(* We consider an ODE defined by a function phi : K -> 'rV[K]_n -> 'rV[K]_n.  *)
(* The idea of the proof is to define a function                              *)
(* picard := fun t => u0 + \int[mu]_(x in `[a, t]) phi x (g x)                *)
(* and to study the solution of the integral equation g t = picard t.         *)
(*                                                                            *)
(* Preliminaries:                                                             *)
(*   \vint[mu]_(x in A) f x == integral of f of type R -> 'rV_n               *)
(*                                                                            *)
(* picard_fun_subdef u0 r phi a b g gabB ==                                   *)
(*   fun t => u0 + \vint_(x in `[a, t]) phi x (g x)                           *)
(*   defined as a continuous function from `[a, b] to 'rV_n                   *)
(*   morally, takes a function g and returns a function g                     *)
(*   gabB is a proof that g @` `[a, b] `<=` closed_ball u0 r                  *)
(*                                                                            *)
(* picard_fun lip2 cont1 g == same as picard_fun_subdef when                  *)
(*   g @` `[a, b] `<=` closed_ball u0 r and cst 0 o.w.                        *)
(*                                                                            *)
(* Technical constants need for the proof:                                    *)
(*   sup_phi == sup {phi t u0 | t \in [a, b]}                                 *)
(*   safe_dist == min (b - a, r / (k * r + sup_phi), rho / k)                 *)
(*                upper-bound of delta                                        *)
(*                The dependence of safe_dist on the initial state u0 comes   *)
(*                from sup_phi in the second term.                            *)
(*   @img_cball R n f a b k u0 r k0 rho ==                                    *)
(*     set of functions of type (quot_conSet a b U) s.t.                      *)
(*     f @` `[a, a + safe_dist] `<=` closed_ball u0 r                         *)
(*                                                                            *)
(* picard == similar to picard_fun                                            *)
(*   as a function from/to the quotient of functions continuous over `[a, b]  *)
(*   more precisely, function of type {fun img_cball >-> img_cball}           *)
(*                                                                            *)
(* picard_fix == fixpoint of the integral equation defined by picard          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

(* start of preliminaries *)

(* NB: PR to MathComp-Analysis in progress *)
Section pointwise_derivable.
Context {R : realFieldType} {V W : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

Definition derivable_mx M t v :=
  forall i j, derivable (fun x => M x i j) t v.

Lemma derivable_mxP M t v : derivable_mx M t v <-> derivable M t v.
Proof.
split; rewrite /derivable_mx /derivable.
- move=> H.
  apply/cvg_ex => /=.
  pose l := \matrix_(i < m, j < n) sval (cid ((cvg_ex _).1 (H i j))).
  exists l.
  apply/cvgrPdist_le => /= e e0.
  near=> x.
  rewrite /Num.Def.normr/= mx_normrE.
  apply: (bigmax_le _ (ltW e0)) => /= i _.
  rewrite !mxE/=.
  move: i.
  near: x.
  apply: filter_forall => /= i.
  exact: ((@cvgrPdist_le _ _ _ _ (dnbhs_filter 0) _ _).1
    (svalP (cid ((cvg_ex _).1 (H i.1 i.2)))) _ e0).
- move=> /cvg_ex[/= l Hl] i j.
  apply/cvg_ex; exists (l i j).
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0] H.
  near=> x.
  apply: le_trans; last first.
    apply: (H x).
    rewrite /ball_/=.
    rewrite sub0r normrN.
    near: x.
    exact: dnbhs0_lt.
    near: x.
    exact: nbhs_dnbhs_neq.
  rewrite [leRHS]/Num.Def.normr/= mx_normrE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite /= !mxE.
Unshelve. all: by end_near. Qed.

End pointwise_derivable.

(* NB: PR to MCA *)
Section pointwise_derive.
Local Open Scope classical_set_scope.
Context {R : realFieldType} {V W : normedModType R} .

Lemma derive_mx {m n : nat} (M : V -> 'M[R]_(m, n)) t v :
  derivable M t v ->
  'D_v M t = \matrix_(i < m, j < n) 'D_v (fun t => M t i j) t.
Proof.
move=> /cvg_ex[/= l Hl]; apply/cvg_lim => //=.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : (Hl) => /(_ (e / 2)).
rewrite divr_gt0// => /(_ isT)[d /= d0 dle].
near=> x.
rewrite [in leLHS]/Num.Def.normr/= mx_normrE.
apply/(bigmax_le _ (ltW e0)) => -[/= i j] _.
rewrite [in leLHS]mxE/= [X in _ + X]mxE -[X in X - _](subrK (l i j)).
rewrite -(addrA (_ - _)) (le_trans (ler_normD _ _))// (splitr e) lerD//.
- rewrite mxE.
  suff : (h^-1 *: (M (h *: v + t) i j - M t i j)) @[h --> 0^'] --> l i j.
    move/cvg_lim => /=; rewrite /derive /= => ->//.
    by rewrite subrr normr0 divr_ge0// ltW.
  apply/cvgrPdist_le => /= r r0.
  move/cvgrPdist_le : Hl => /(_ r r0)[/= s s0] sr.
  near=> y.
  have : `|l - y^-1 *: (M (y *: v + t) - M t)| <= r.
    rewrite sr//=; last by near: y; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: y; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
  by under eq_bigr do rewrite !mxE; exact: (le_bigmax _ _ (i, j)).
- rewrite mxE.
  have : `|l - x^-1 *: (M (x *: v + t) - M t)| <= e / 2.
    apply: dle => //=; last by near: x; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: x; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE/=.
  under eq_bigr do rewrite !mxE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite !mxE.
Unshelve. all: by end_near. Qed.

End pointwise_derive.

Reserved Notation "\vint [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, i, D at level 60,
  format "'[' \vint [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\vint [ mu ]_ i F"
  (F at level 36, i at level 0,
    right associativity, format "'[' \vint [ mu ]_ i '/  '  F ']'").

(* TODO: move *)
Section row_Rintegral.
Context {R : realType} (d : measure_display) {T : measurableType d}.
Variable (mu : {measure set T -> \bar R}).
Variable (D : set T) (n : nat).

Definition rowRintegral (f : T -> 'rV[R]_n) : 'rV[R]_n :=
  \row_i (\int[mu]_(x in D) (f x) ord0 i).

Local Notation "\vint_ i F" :=
    (rowRintegral (fun i => F)%R) (at level 36, i at level 0,
  format "'[' \vint_ i '/  '  F ']'")  : ring_scope.

Lemma rowRintegralE (f : T -> 'rV[R]_n) i :
  (\vint_x f x) ord0 i = \int[mu]_(x in D) (f x) ord0 i.
Proof. by rewrite /rowRintegral mxE. Qed.

End row_Rintegral.

Notation "\vint [ mu ]_ ( x 'in' D ) f" :=
  (rowRintegral mu D (fun x => f)%R) : ring_scope.
Notation "\vint [ mu ]_ x f" :=
  (rowRintegral mu setT (fun x => f)%R) : ring_scope.

Section rowRintegral.
Context {R : realType}.
Let mu := @lebesgue_measure R.

Lemma rowRintegral_set1 n (f : R -> 'rV[R]_n) (r : R) :
  \vint[mu]_(x in [set r]) f x = 0.
Proof. by apply/rowP => i; rewrite !mxE Rintegral_set1. Qed.

Lemma eq_rowRintegral n (D : set R) (f : R -> 'rV[R]_n) (g : R -> 'rV[R]_n):
 {in D, f =1 g} -> \vint[mu]_(x in D) f x = \vint[mu]_(x in D) g x.
Proof.
move => h.
apply /rowP => i.
rewrite !rowRintegralE.
apply eq_Rintegral => /= x Dx.
by rewrite h.
Qed.

End rowRintegral.

Section rowRintegral_itv_split.
Local Notation mu := lebesgue_measure.

Lemma rowRintegral_itv_split {R : realType} (n : nat) (F : R -> 'rV[R]_n)
    (a c b : R) :
  a <= c <= b ->
  (forall i, mu.-integrable `[a, b] (EFin \o (fun x : R => F x ord0 i))) ->
  \vint[mu]_(s in `[a, b]) F s =
  \vint[mu]_(s in `[a, c]) F s + \vint[mu]_(s in `[c, b]) F s.
Proof.
move=> /andP[t0t1 t1t2] intF.
apply/rowP=> i.
rewrite !rowRintegralE !mxE.
apply/eqP.
rewrite addrC -subr_eq.
apply/eqP.
rewrite (@Rintegral_itvB _ (fun x => F x ord0 i) (BLeft a) (BRight b) c) //=.
apply Rintegral_itv_obnd_cbnd.
apply (@integrableS _ _ _ lebesgue_measure `[a, b] `]c, b] (EFin \o (fun x => F x ord0 i))) =>//.
exact: subset_itvScc.
Qed.

End rowRintegral_itv_split.

(* TODO: PR *)
Section vector_continuous.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.

Lemma within_continuous_coord (h : R -> U) D :
  {within D, continuous h} <-> forall i, {within D, continuous (fun x => h x ord0 i)}.
Proof.
split=> [Dh i|H].
- apply/subspace_continuousP => /= x Dx.
  have /subspace_continuousP/(_ x Dx) H := Dh.
  apply: ((@cvg_comp _ _ _ h (fun z => z ord0 i)) _ _ _ H).
  exact: coord_continuous.
- apply/subspace_continuousP => /= x Dx.
  apply/cvgrPdist_le => /= e e0.
  rewrite near_withinE.
  near=> t => Dt.
  rewrite /Num.norm/= mx_normrE.
  apply/(bigmax_le _ (ltW e0)) => /= -[i j] _ /=.
  rewrite {i}(ord1 i) !mxE.
  move: j Dt.
  near: t.
  apply: filter_forall => /= i.
  have /subspace_continuousP/(_ x Dx) := H i.
  move/cvgrPdist_le => /(_ _ e0).
  rewrite near_withinE.
  exact.
Unshelve. all: by end_near. Qed.

End vector_continuous.

Lemma continuous_within_ext {A B : topologicalType} (g h : A -> B) D :
  {in D, g =1 h} ->
  {within D, continuous g } -> {within D, continuous h}.
Proof.
move=> h1 h2.
apply subspace_continuousP.
move => x Dx.
apply : cvg_trans.
apply (fmap_within_eq (g := g)) => //.
apply nbhs_filter.
move => x' Dx' .
symmetry.
by apply h1.
rewrite <-h1.
move /subspace_continuousP : h2.
by apply.
by rewrite inE.
Qed.

(* TODO: PR *)
Lemma measurable_fun_bigmaxr d (T : measurableType d) (R : realType)
  (D : set T) (n : nat) (f : 'I_n -> T -> R) :
  d.-measurable D ->
  (forall i, measurable_fun D (f i)) ->
  measurable_fun D (fun x => \big[maxr/0]_(i < n) f i x).
Proof.
move=> mD mf.
elim: n f mf => [|n IH] f mf.
  have -> : (fun x : T => \big[maxr/0]_(i < 0) f i x) = 0.
    apply funext => x.
    by rewrite big_ord0.
  exact: measurable_cst.
have -> :  (fun x : T => \big[maxr/0]_(i < n.+1) f i x) =
    fun x => maxr (f ord0 x) (\big[maxr/0]_(i < n) (f (lift ord0 i) x)).
  by apply funext => x;apply big_ord_recl.
apply: measurable_maxr.
  exact: mf.
by apply: IH  => i; exact: mf.
Qed.

Lemma vec_norm_le_sum {R : realType} {n : nat} (x : 'rV[R]_n) :
  `| x | <=  \sum_(i < n) `|x ord0 i|.
Proof.
rewrite  {1}/Num.norm/= mx_normrE.
apply: bigmax_le => /=;first by apply sumr_ge0 => i _; exact: normr_ge0.
move =>  [i0 i] _ /=.
rewrite {i0}(ord1 i0)/=.
rewrite (bigD1 i) //= lerDl.
by apply: sumr_ge0 => j _; exact: normr_ge0.
Qed.

Lemma vmeasurable_norm {R : realType} {n : nat} (D : set R) (F : R -> 'rV[R]_n):
   measurable D -> (forall i, measurable_fun D (fun t => F t ord0 i)) ->
  measurable_fun D (Num.norm \o F).
Proof.
move=> mD h.
have -> : normr \o F = (fun x => \big[maxr/0]_(i < n) `| F x ord0 i |).
  apply: funext => x.
  rewrite  {1}/Num.norm/= mx_normrE.
  rewrite (reindex (fun i : 'I_n => (ord0, i))) => //=.
  exists (@snd 'I_1 'I_n) => /=.
  + by move => i.
  + move => [i j] /= _.
    by rewrite {i}(ord1 i).
apply: measurable_fun_bigmaxr => //= i.
by apply: measurableT_comp => //=.
Qed.

Lemma vintegrable_norm {R : realType} {n : nat} (D : set R) (F : R -> 'rV[R]_n):
  measurable D ->
  (forall i, lebesgue_measure.-integrable D (EFin \o (fun t => F t ord0 i))) ->
  lebesgue_measure.-integrable D (EFin \o (Num.norm \o F)).
Proof.
move => mD intf.
apply (le_integrable (mu:=lebesgue_measure) mD (f := EFin \o (normr \o F))
    (g := EFin \o fun x => (\sum_(i < n) `| F x ord0 i|))).
- apply/measurable_EFinP.
  apply vmeasurable_norm => // i.
  have /integrableP[+ _]/= := intf i.
  by move/measurable_EFinP.
- move => /= x0 Dx0.
  rewrite normr_id.
  rewrite lee_fin.
  rewrite ger0_norm.
  apply vec_norm_le_sum.
  exact: sumr_ge0.
- have -> : EFin \o (fun x => \sum_(i < n) `|F x ord0 i|) =
            fun x => (\sum_(i < n) `|F x ord0 i|%:E).
    by apply/funext => x; rewrite sumEFin.
  apply: integrable_sum => //= i _.
  exact: integrable_norm.
Qed.

Lemma closed_ball_vecE {R : realType} {n} (x0 : 'rV[R]_n) (r : {posnum R}) x :
  closed_ball x0 r%:num x <->
  forall i, closed_ball (x0 ord0 i) r%:num (x ord0 i).
Proof.
split.
- rewrite closed_ballE /closed_ball_ //=.
  rewrite /Num.norm/= mx_normrE => h i.
  rewrite closed_ballE// /closed_ball_/=.
  apply/le_trans/h.
  have -> : x0 ord0 i - x ord0 i = (x0 - x) ord0 i by rewrite !mxE.
  exact: (le_bigmax _ _ (ord0, i)).
- move=> h.
  rewrite closed_ballE// /closed_ball_/=.
  rewrite [in leLHS]/Num.norm/= mx_normrE.
  apply: bigmax_le => //= -[i j] _ /=.
  rewrite {i}(ord1 i)/=.
  move /(_ j) : h.
  by rewrite closed_ballE// /closed_ball_ /= 2!mxE.
Qed.

Section lipschitz_componentE.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 <= k.

Lemma lipschitz_componentE x : k.-lipschitz_B (phi x) <->
  forall i, k.-lipschitz_B (fun y => phi x y ord0 i).
Proof.
split.
- move => lip i /= [x1 x2] /= Bx12.
  move /(_ (x1,x2) Bx12) : lip.
  apply le_trans => /=.
  rewrite /Num.norm/= mx_normrE.
  have -> : phi x x1 ord0 i - phi x x2 ord0 i = (phi x x1 - phi x x2) ord0 i by rewrite !mxE.
  exact: (le_bigmax _ _ (ord0,i)).
- move => h /= [x1 x2] Bx12 /=.
  rewrite [in leLHS]/Num.norm/= mx_normrE.
  apply/bigmax_le.
    by rewrite mulr_ge0 //= ltW.
  move => //= -[i j] _ /=.
  rewrite {i}(ord1 i)/=.
  move /(_ j (x1,x2) Bx12) : h.
  by rewrite !mxE.
Qed.

End lipschitz_componentE.

Definition measure_rV_display : measure_display -> measure_display.
Proof. exact. Qed.

Section measurable_rV.
Context {d} {T : sigmaRingType d}.
Variable n : nat.

Let coors : 'I_n -> 'rV[T]_n -> T := fun i x => x ord0 i.

Let rV_set0 : g_sigma_preimage coors set0.
Proof. exact: sigma_algebra0. Qed.

Let rV_setC A : g_sigma_preimage coors A -> g_sigma_preimage coors (~` A).
Proof. exact: sigma_algebraC. Qed.

Let rV_bigcup (F : _^nat) : (forall i, g_sigma_preimage coors (F i)) ->
  g_sigma_preimage coors (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition _ := @isMeasurable.Build (measure_rV_display d)
  'rV[T]_n (g_sigma_preimage coors) rV_set0 rV_setC rV_bigcup.

End measurable_rV.

(* end of preliminaries *)

(* cauchy-lipschitz really starts here *)

Definition picard_fun_subdef {R : realType} n (U := 'rV[R]_n) (u0 : U) (r : R)
  (B := closed_ball u0 r) (phi : R -> U -> U) (a b : R) (g : R -> U)
    (gabB : g @` `[a, b] `<=` B) : R -> U :=
  fun t => u0 + (\vint[lebesgue_measure]_(x in `[a, t]) phi x (g x))%R.

Section picard_fun_subdef_isFun.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R).
Variables (u0 : U) (r : {posnum R}).
Let B : set U := closed_ball u0 r%:num.
Variable g : R -> U.
Hypothesis gabB : g @` `[a, b] `<=` B.

Let set_fun_picard_fun_subdef :
  {homo picard_fun_subdef phi gabB : x / `[a, b] x >-> [set: U] x}.
Proof. by []. Qed.

HB.instance Definition _ := @isFun.Build
  (subspace `[a, b]) _ `[a, b] [set: U] (picard_fun_subdef phi gabB)
    (set_fun_picard_fun_subdef).

End picard_fun_subdef_isFun.

Section picard_fun_subdef_isContinuous.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R).
Variables (u0 : U) (r : {posnum R}).
Let B : set U := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k != 0.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Variable g : R -> U.
Variable cg : {within `[a, b], continuous g}.
Hypothesis gabB : g @` `[a, b] `<=` B.

Lemma within_continuous_picard_fun_subdef :
  {within `[a, b], continuous (picard_fun_subdef phi gabB)}.
Proof.
have [ab|] := ltP a b; last first.
  rewrite le_eqVlt => /predU1P[ab|ab].
    rewrite [X in {within X, continuous _}](_ : _ = [set a]); last first.
      by rewrite ab set_itv1.
    exact: continuous_subspace1.
  rewrite set_itv_ge// ?bnd_simp -?ltNge//.
  exact: continuous_subspace0.
apply/within_continuous_coord => i.
rewrite /picard_fun_subdef.
suff: {within `[a, b],
    continuous (fun t => \int[mu]_(y in `[a, t]) phi y (g y) ord0 i)}.
  move=> abf x.
  rewrite (_ : (fun r => (u0 + \vint[mu]_(y in `[a, r]) phi y (g y)) ord0 i) =
      (fun r => u0 ord0 i + \int[mu]_(y in `[a, r]) (phi y (g y)) ord0 i)).
    by apply: cvgD; [exact: cvg_cst|exact: abf].
  by apply/funext=> r0; rewrite mxE rowRintegralE.
move=> /= x.
apply: parameterized_integral_continuous.
  exact: ltW.
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
move: i; apply/within_continuous_coord.
exact: (within_continuous_lipschitz cg _ lip2 cont1).
Qed.

HB.instance Definition _ := isContinuous.Build (subspace `[a, b]) U
  (picard_fun_subdef phi gabB : subspace _ -> _)
  within_continuous_picard_fun_subdef.

Let continuous_picard_fun_subdef :
  {within `[a, b], continuous picard_fun_subdef phi gabB}.
Proof. exact: cts_fun. Abort.

End picard_fun_subdef_isContinuous.

Section picard_fun.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Definition picard_fun
    (k : R) (k0 : k != 0) (lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)})
    (cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}})
    (g : R -> U) : R -> U :=
  match pselect (g @` `[a, b] `<=` B) with
  | left gabB => picard_fun_subdef phi gabB
  | _ => cst 0
  end.

End picard_fun.

Section sup_phi.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R).
Variables (u0 : U).

Definition sup_phi : R := sup [set `|phi t u0| | t in `[a, b]].

Lemma sup_phi_ge0 : 0 <= sup_phi.
Proof. by rewrite /sup_phi sup_ge0//= => x [y _ <-]. Qed.

End sup_phi.

Section sup_phi_lemmas.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U).
Variables (u0 : U).

Lemma sup_phiS a b c d : {within `[a, b], continuous (phi ^~ u0)} ->
  a <= b -> `[c, d] `<=` `[a, b] ->
  sup_phi phi c d u0 <= sup_phi phi a b u0.
Proof.
move=> cf ab cdab.
rewrite /sup_phi.
have [cd|dc] := leP c d.
  apply: sup_le => //.
  - move=> _/= [r rcd <-].
    red.
    simpl.
    exists `|phi r u0|; split => //.
    exists r => //.
    by apply: cdab.
  - exists `|phi c u0| => /=.
    exists c => //.
    by rewrite in_itv/= lexx cd.
  - split.
      exists `|phi a u0| => //=.
      exists a => //.
      by rewrite in_itv/= lexx ab.
    have : {within `[a, b], continuous fun t : R => `|phi t u0|}.
      by apply: within_continuous_comp_norm => //.
    move/(@EVT_max R (fun t => `|phi t u0|) _ _ ab) => [e eab Hmax].
    exists (`|phi e u0|) => x/= [r rab <-//].
    exact: Hmax.
rewrite set_itv_ge ?bnd_simp/= -?ltNge// image_set0 sup0.
by apply: sup_ge0 => x/= [y _ <-//].
Qed.

End sup_phi_lemmas.

Section safe_dist.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Variable rho : {posnum R}. (* rho < 1 *)

Local Notation sup_phi := (sup_phi phi a b u0).

Definition safe_dist := Num.min (b - a)
                       (Num.min (r%:num / (k * r%:num + sup_phi))
                                (rho%:num / k)).

Lemma safe_dist_gt0 : 0 < safe_dist.
Proof.
rewrite lt_min subr_gt0 ab/= lt_min mulr_gt0 ?divr_gt0//.
by rewrite invr_gt0// ltr_wpDr ?sup_phi_ge0// mulr_gt0.
Qed.

Lemma ltDl_safe_dist : a < a + safe_dist.
Proof. by rewrite ltrDl safe_dist_gt0. Qed.

Lemma leDl_safe_dist : a <= a + safe_dist.
Proof. by rewrite ltW// ltDl_safe_dist. Qed.

Lemma safe_dist_itv : safe_dist <= b - a.
Proof. by rewrite /safe_dist ge_min lexx. Qed.

End safe_dist.

Section image_in_closed_ball.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Variables (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Variable rho : {posnum R}. (* rho < 1 *)

Import ContSeg_quot.

Local Notation safe_dist := (@safe_dist R n phi a b k u0 r rho).
Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Definition img_cball : set V :=
  [set f : V | f @` `[a, a + safe_dist] `<=` closed_ball u0 r%:num].

Lemma img_cball_nonempty : img_cball !=set0.
Proof.
exists (pi V (cst u0)) => _ [y aay] <-.
suff -> : fun_of_quot_contSeg (\pi_V%qT (cst u0)) y = u0.
  exact: closed_ballxx.
rewrite /fun_of_quot_contSeg/=.
have /eqmod_on_itv : (repr (\pi_V%qT (cst u0)) = cst u0 %[mod V])%qT.
  by rewrite reprK.
by apply; rewrite inE.
Qed.

Lemma img_cballE : a < b -> img_cball =
  @closed_ball R V (pi V (@cst (subspace `[a, a + safe_dist]) U u0)) r%:num.
Proof.
move=> ab; rewrite closed_ballE//.
apply: eq_set => /= f; apply propext; split => h.
- rewrite -(@reprK _ V f).
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite infty_norm_pi infty_norm0_le//.
    by rewrite /= lerDl ltW// safe_dist_gt0.
  move=> x adx.
  move /(_ (f x)) : h.
  rewrite closed_ballE//.
  apply.
  by exists x.
- move => _ [x xad] <-.
  rewrite closed_ballE// /closed_ball_ /=.
  have -> : u0 - f x = ((pi V (cst u0)) - f : V) x.
    rewrite -(@reprK _ V f) /GRing.opp /=.
    rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv// inE.
  rewrite -(@reprK _ V f).
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite eval_mod_on_itv; last by rewrite inE.
  apply: (le_trans (infty_norm0_ge (leDl_safe_dist phi ab u0 r k0 rho) _ xad)).
  rewrite -infty_norm_pi.
  by rewrite Quotient.pi_add Quotient.pi_opp reprK.
Qed.

Lemma closed_img_cball : a < b -> closed img_cball.
Proof. by move=> ?; rewrite img_cballE//; exact: closed_ball_closed. Qed.

End image_in_closed_ball.

Section picard_fun_isFun.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : k != 0.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}.

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).

Lemma lip2_safe_dist : {in `[a, a + safe_dist]%R, forall x, k.-lipschitz_B (phi x)}.
Proof.
move/in_switch : lip2 => lip2'.
apply/in_switch.
apply: lipschitzW lip2'.
apply: subset_itvl.
by rewrite bnd_simp -lerBrDl; exact: safe_dist_itv.
Qed.

Lemma cont1_safe_dist :
  {in B, forall y, {within `[a, a + safe_dist], continuous phi ^~ y}}.
Proof.
move=> /= x xB.
apply: continuous_subspaceW; last exact: cont1.
apply: subset_itvl.
by rewrite bnd_simp -lerBrDl; exact: safe_dist_itv.
Qed.

Local Notation picard_fun :=
  (@picard_fun _ n phi a (a + safe_dist) u0 r k k0 lip2_safe_dist cont1_safe_dist).

Lemma picard_funE g t : g @` `[a, a + safe_dist] `<=` B ->
  picard_fun g t = u0 + \vint[mu]_(x in `[a, t]) phi x (g x).
Proof. by rewrite /picard_fun; case: pselect. Qed.

Lemma picard_fun_init g : g @` `[a, a + safe_dist] `<=` B ->
  picard_fun g a = u0.
Proof.
by move => h; rewrite picard_funE// set_itv1 rowRintegral_set1 addr0.
Qed.

Import ContSeg_quot.

Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Let set_fun_picard_fun (g : V) :
  set_fun `[a, a + safe_dist] [set: U] (picard_fun g).
Proof. by []. Qed.

HB.instance Definition _ (g : V) := @isFun.Build
  (subspace `[a, a + safe_dist]) _
    `[a, a + safe_dist] setT (picard_fun g) (set_fun_picard_fun g).

End picard_fun_isFun.

Section picard_fun_isContinuous.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : k != 0.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}.

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).

Local Notation picard_fun := (@picard_fun _ n phi a (a + safe_dist) u0 r k k0
  (@lip2_safe_dist R n phi a b k u0 r lip2 rho)
  (@cont1_safe_dist R n phi a b k u0 r cont1 rho)).

Import ContSeg_quot.

Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Let continuous_picard_fun (g : V) :
  {within `[a, a + safe_dist], continuous (picard_fun g)}.
Proof.
have [aaD|] := ltP a (a + safe_dist); last first.
  rewrite le_eqVlt => /predU1P[aaD|aaD].
    rewrite [X in {within X, continuous _}](_ : _ = [set a]); last first.
      by rewrite aaD set_itv1.
    exact: continuous_subspace1.
  rewrite set_itv_ge// ?bnd_simp -?ltNge//.
  exact: continuous_subspace0.
have := @cts_fun _ _ g.
rewrite /picard_fun; case: pselect => /=.
  move => z cg.
  apply: (@cts_fun (subspace `[a, a + safe_dist]) U (picard_fun_subdef phi z)).
  - exact: k0.
  - exact: lip2_safe_dist.
  - exact: cont1_safe_dist.
  - exact: cg.
by move=> _ _; apply: continuous_subspaceT => z; exact: cvg_cst.
Qed.

HB.instance Definition _ (g : V) := @isContinuous.Build _ _
  (picard_fun g : subspace _ -> _) (@continuous_picard_fun g).

Check fun g : V => picard_fun g : continuousFunType _ _.

Check fun g : V => (\pi_(V)%qT (picard_fun g)) : V.

End picard_fun_isContinuous.

Section integrable_comp.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : k != 0.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}.

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).

Import ContSeg_quot.

Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Lemma integrable_comp (F : V) y i : y \in `[a, a + safe_dist]%R ->
  F @` `[a, y] `<=` B ->
  mu.-integrable `[a, y] (EFin \o (fun t => phi t (F t) ord0 i)).
Proof.
move=> yaadelta ab0r.
apply: continuous_compact_integrable; first exact: segment_compact.
move: (yaadelta); rewrite in_itv/= => /andP[ay yadelta].
move: i; apply/within_continuous_coord.
apply/(within_continuous_lipschitz _ k0).
- have := @cts_fun _ _ F.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- apply/in_switch.
  move/in_switch : (@lip2_safe_dist R n phi a b k u0 r lip2 rho).
  by apply/lipschitzW/subset_itvl; rewrite bnd_simp.
- rewrite -/B => x xB.
  have := @cont1_safe_dist R n phi a b k u0 r cont1 rho _ xB.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- exact: ab0r.
Qed.

End integrable_comp.

(* PR to MCA *)
Section Rintegral.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types (D : set T).

Lemma Rintegral_cst D : d.-measurable D ->
  forall r, \int[mu]_(_ in D) r = r * fine (mu D).
Proof.
move=> mD r; rewrite /Rintegral/= integral_cst//.
have := leey (mu D); rewrite le_eqVlt => /predU1P[->/=|muy]; last first.
  by rewrite fineM// ge0_fin_numE.
rewrite mulr0 mulr_infty/=; have [_|r0|r0] := sgrP r.
- by rewrite mul0e.
- by rewrite mul1e.
- by rewrite mulN1e.
Qed.

End Rintegral.

(* PR to MCA *)
Section continuous_patch.
Context {R : realType} {n : nat} {U : normedModType R}.
Variables (a b c : R) (f : R -> U) (g : R -> U).
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous f}.
Hypothesis cont2 : {within `[b, c], continuous g}.
Hypothesis matchb : f b = g b.

Lemma within_continuous_patch : {within `[a, c], continuous (patch g `[a, b] f)}.
Proof.
have -> : `[a, c] = `[a, b] `|` `[b, c].
  rewrite (@itv_bndbnd_setU _ _ _ (BRight b)) // ?bnd_simp//=; [|exact: ltW..].
  apply/seteqP; split => [x []|x []].
  by left.
  by right; exact: subset_itv_oc_cc b0.
  by left.
  rewrite -setU1itv ?bnd_simp//; last exact: ltW.
  case; last by right.
  move=> ->; left => /=.
  by rewrite bound_itvE ltW.
apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b c)).
  have eq1 : {in `[a, b], f =1 patch g `[a, b] f }.
    by move=> r rab; rewrite /patch rab.
  apply: (continuous_within_ext eq1).
  exact: cont1.
have eq2 : {in `[b, c], g =1 patch g `[a, b] f }.
  move=> r rab.
  rewrite /patch; case: ifPn => [xab | xabnot] => //.
  suff -> : r = b by rewrite matchb.
  apply: le_anti.
  move: rab xab.
  by rewrite !inE/=!in_itv/= => /andP [-> _] /andP [_ ->].
apply/continuous_subspaceW/(continuous_within_ext eq2)/cont2.
by apply: subset_itvl; rewrite bnd_simp.
Qed.

End continuous_patch.

(* TODO: PR to MCA *)
Lemma nbhs_ge {R : realFieldType} (t x : R) :
  t < x -> \forall x0 \near nbhs x, t <= x0.
Proof.
move=> tx.
exists ((x - t) / 2).
  by rewrite /= divr_gt0// subr_gt0.
move=> y/=.
have [xy|yx] := lerP x y.
  rewrite ltrBlDl => H.
  by rewrite (le_trans (ltW tx)).
rewrite ltrBlDl -ltrBlDr => /ltW; apply: le_trans.
rewrite -lerBlDr opprK.
by rewrite -lerBrDl ler_piMr ?invf_le1 ?ler1n// subr_ge0 ltW.
Qed.

(* TODO: PR to MC *)
Definition And31 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p1.
Definition And32 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p2.
Definition And33 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p3.

Section picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 < k.
Let k0' : k != 0. Proof. by rewrite gt_eqF. Qed.

Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}.

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).
Local Notation picard_fun := (@picard_fun _ n phi a (a + safe_dist) u0 r k k0'
  (@lip2_safe_dist R n phi a b k u0 r lip2 rho)
  (@cont1_safe_dist R n phi a b k u0 r cont1 rho)).

Import ContSeg_quot.

Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Definition picard (f : V) : V := \pi_V%qT (picard_fun f).

Local Notation img_cball := (@img_cball R n phi a b k u0 r rho).
Local Notation sup_phi := (@sup_phi R n phi a b u0).

Let set_fun_picard : set_fun img_cball img_cball picard.
Proof.
move=> F.
rewrite /img_cball/= => invariant _/= [y yaaDelta <-].
rewrite /picard.
apply closed_ball_vecE => i.
rewrite closed_ball_itv//=.
rewrite in_itv//=.
rewrite [X in _ <= X <= _](_ : _ = (picard_fun F) y ord0 i); last first.
  have /eqmod_on_itv : (repr (\pi_(V)%qT (picard_fun F)) =
       picard_fun F %[mod V])%qT.
    by rewrite reprK.
  by move=> <- //; rewrite inE.
rewrite /picard_fun; case: pselect => /= abu0r; last by [].
rewrite /picard_fun_subdef /=.
rewrite mxE/=.
rewrite -ler_distl.
rewrite -addrA subrKC.
rewrite rowRintegralE.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  apply: integrable_comp => //.
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move : yaaDelta; rewrite in_itv /= => /andP[].
have integrable2 : mu.-integrable `[a, y] (EFin \o (fun x => phi x (F x) ord0 i)).
  apply integrable_comp => //=.
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move: yaaDelta; rewrite in_itv /= => /andP[].
have integrable1 : mu.-integrable `[a, y]
    (fun x => `|phi x (F x) ord0 i - phi x u0 ord0 i|%:E + `|phi x u0 ord0 i|%:E).
  rewrite integrableD//=.
    apply integrable_norm => /=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinN.
    rewrite integrableN //=.
    apply: continuous_compact_integrable => //=; first exact: segment_compact.
    apply within_continuous_coord.
    apply/continuous_subspaceW/(@cont1_safe_dist R n phi a b k u0 r cont1 rho).
      apply: subset_itvl; rewrite bnd_simp.
      by move : yaaDelta;rewrite in_itv /= => /andP[].
    by rewrite /B inE; exact: closed_ballxx.
  apply integrable_norm => /=.
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  apply within_continuous_coord.
  apply/continuous_subspaceW/(@cont1_safe_dist R n phi a b k u0 r cont1 rho).
    apply: subset_itvl; rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
  rewrite /B inE.
  exact: closed_ballxx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y])
    (`|phi x (F x) ord0 i - phi x u0 ord0 i| + `|phi x u0 ord0 i|)))//.
  apply: le_Rintegral => //=.
  - exact: integrable_norm.
  - move=> x xay.
    by rewrite (le_trans _ (ler_normD _ _))// subrK.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * `|F x - u0| + sup_phi)))//.
  apply: le_Rintegral => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr //=.
        exact: bounded_cst.
      apply: vintegrable_norm  => //.
      move => j //=.
      under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
      rewrite integrableB //=.
        apply continuous_compact_integrable => //; first exact: segment_compact.
        apply within_continuous_coord.
        apply/continuous_subspaceW/cts_fun.
        apply: subset_itvl; rewrite bnd_simp.
        by move : yaaDelta; rewrite in_itv /= => /andP[].
      apply measurable_bounded_integrable => //=.
        rewrite lebesgue_measure_itv //=.
        case: ifPn => //=.
        by rewrite -EFinD ltry.
      exact: bounded_cst.
    apply measurable_bounded_integrable => //=.
      rewrite lebesgue_measure_itv //=.
      case: ifPn => //=.
      by rewrite -EFinD ltry.
    exact: bounded_cst.
  move=> x xay.
  rewrite lerD//.
    have xaaDelta : x \in `[a, a + safe_dist]%R.
      move: x xay.
      apply: subset_itvl; rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
    move/(lip2_safe_dist lip2) : xaaDelta.
    rewrite lipschitz_componentE//; last exact: ltW.
    move/(_ i (F x, u0)) => /=.
    apply.
    split => /=.
      apply: invariant => /=.
      exists x => //.
      move : xay.
      apply: subset_itvl; rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
    exact: closed_ballxx.
  apply: (@le_trans _ _ `|phi x u0|) => //.
    by rewrite /Num.norm/= mx_normrE /= (le_bigmax _ _ (ord0, i)).
  rewrite /sup_phi ub_le_sup//.
    have [M [Mb1 Mb2]] : bounded_set [set `|phi t u0| | t in `[a,b]].
      apply/compact_bounded/continuous_compact; last exact: segment_compact.
      have [ab|] := ltP a b; last first.
        rewrite le_eqVlt => /predU1P[ab|ab].
          rewrite [X in {within X, continuous _}](_ : _ = [set a]); last first.
            by rewrite ab set_itv1.
          exact: continuous_subspace1.
        rewrite set_itv_ge// ?bnd_simp -?ltNge//.
        exact: continuous_subspace0.
      apply: within_continuous_comp_norm.
        by rewrite ltW.
      by apply cont1;rewrite inE; exact: closed_ballxx.
    exists (M + 1) => _ [x0 x0ab] <- /=.
    rewrite -normr_id.
    apply Mb2.
      by rewrite ltrDl.
    by exists x0.
  exists x => //.
  move: xay; rewrite in_itv/= in_itv/= => /andP[] -> /=.
  move/le_trans; apply.
  move : yaaDelta; rewrite in_itv /= => /andP[].
  move => _ /le_trans; apply.
  by rewrite -lerBrDl safe_dist_itv.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * r%:num + sup_phi)))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr //=.
        exact: bounded_cst.
      apply: vintegrable_norm => // j /=.
      under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
      rewrite integrableB //=.
        apply continuous_compact_integrable => //.
          exact: segment_compact.
        apply within_continuous_coord.
        apply /continuous_subspaceW/cts_fun.
        apply: subset_itvl; rewrite bnd_simp.
        by move : yaaDelta; rewrite in_itv /= => /andP[].
      apply: measurable_bounded_integrable => //=.
        rewrite lebesgue_measure_itv//=.
        case: ifPn => //=.
          by rewrite -EFinD ltry.
        exact: bounded_cst.
      apply measurable_bounded_integrable => //=.
        rewrite lebesgue_measure_itv //=.
        case: ifPn => //=.
        by rewrite -EFinD ltry.
      exact: bounded_cst.
    apply measurable_bounded_integrable => //=.
      rewrite lebesgue_measure_itv //=.
      case: ifPn => //=.
      by rewrite -EFinD ltry.
    exact: bounded_cst.
  - move=> x xay.
    rewrite lerD2r ler_pM2l//.
    have : B (F x).
      apply: invariant => /=.
      exists x => //.
      move: xay; rewrite !in_itv/= => /andP[] -> /= /le_trans.
      apply.
      by move: yaaDelta; rewrite in_itv /= => /andP[].
    by rewrite /B closed_ballE// /closed_ball_/=; rewrite distrC.
rewrite Rintegral_cst//.
rewrite /= (* to remove a reverse_coercion *).
rewrite lebesgue_measure_itv/=.
rewrite lte_fin.
move: (yaaDelta); rewrite in_itv/= => /andP[+ yadelta].
rewrite le_eqVlt => /predU1P[->|ay].
  by rewrite ltxx/= mulr0.
rewrite (@le_trans _ _ ((k * r%:num + sup_phi) * safe_dist))//.
  rewrite ler_wpM2l//.
    by rewrite addr_ge0 ?mulr_ge0 ?(ltW k0)// sup_phi_ge0.
  by rewrite ay//= lerBlDl.
rewrite -ler_pdivlMl//; last first.
  by rewrite ltr_pwDl ?mulr_gt0// sup_phi_ge0.
by rewrite 2!ge_min mulrC lexx/= orbT.
Qed.

Fail Check picard_to_cont : {fun [set: V] >-> [set: V]}.

HB.instance Definition _ := @isFun.Build _ _ _ _ picard set_fun_picard.

Check picard : {fun img_cball >-> img_cball}.
(* still, we can't state that it is a contraction for typing reasons *)

Fail Lemma tmp : is_contraction (picard : {fun [set: _] >-> [set: _]}).
About is_contraction.

End picard.

(* (* see measurable_fun_tnthP *) *)
(* Lemma rV_measurable_fun {d} {T : measurableType d} {R : realType} *)
(*   (D : set T) n (f : T -> 'rV[R]_n) : *)
(*   measurable_fun D f <-> forall i, measurable_fun D (fun t => f t ord0 i). *)
(* Proof. *)
(* split => [mf i mD /= Y mY|mf mD /= Y mY]. *)
(*   admit. *)
(* admit. *)
(* Admitted. *)

(* Definition proj (T : Type) n (A : set (n.-tuple T)) (i : 'I_n) : set T := *)
(*   [set t | exists x, A x /\ t = tnth x i]. *)

(* Lemma vnormr_measurable {R : realType} n (D : set 'rV[R]_n) : *)
(*   measurable_fun D (@Num.norm R 'rV[R]_n). *)
(* Proof. *)
(* move=> mD /= Y mY. *)
(* rewrite /normr/=. *)
(* Admitted. *)

(* Lemma vintegrable_norm {d} {T : measurableType d} {R : realType} *)
(*   (mu : {measure set T -> \bar R}) (D : set T) n (f : T -> 'rV[R]_n) : *)
(*   (forall i, mu.-integrable D (EFin \o (fun t => f t ord0 i))) -> *)
(*   mu.-integrable D (EFin \o (Num.norm \o f)). *)
(* Proof. *)
(* move=> intf. *)
(* apply/integrableP; split. *)
(*   apply/measurable_EFinP. *)
(*   apply/measurableT_comp. *)
(*     exact: vnormr_measurable. *)
(*   apply/rV_measurable_fun => i. *)
(*   have /integrableP[+ _]/= := intf i. *)
(*   by move/measurable_EFinP. *)
(* rewrite (@le_lt_trans _ _ *)
(*     (\big[maxe/-oo]_(i < n) \int[mu]_(x in D) `|f x ord0 i|%:E )%E)//. *)
(*   rewrite /=. *)
(*   under eq_integral do rewrite normr_id. *)
(*   rewrite [in leLHS]/Num.norm/=. *)
(*   under eq_integral do rewrite mx_normrE. *)
(*   admit. *)
(* apply: bigmax_lt => //= i _. *)
(* have /integrableP[_]/= := intf i. *)
(* exact. *)

Section is_contraction_picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R).
Hypothesis ab : a < b.
Variable k : R.
Hypothesis k0 : 0 < k.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}. (* rho < 1 *)
Hypothesis rho1 : (rho%:num < 1).

Import ContSeg_quot.

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).

Notation V := (@quot_contSeg R a (a + safe_dist) U).
Notation img_cball := (@img_cball _ n phi a b k u0 r rho).

Check @cst (subspace `[a, a + safe_dist]) U u0
  : {fun `[a, a + safe_dist] >-> [set: U]}.

Check @cst (subspace `[a, a + safe_dist]) U u0
  : continuousType (subspace `[a, a + safe_dist]) U.

Local Notation picard := (@picard R n phi a b k u0 r k0 lip2 cont1 rho).

Lemma is_contraction_picard : is_contraction picard.
Proof.
rewrite /is_contraction /contraction.
rewrite /picard /picard_fun /picard_fun_subdef.
exists (NngNum (ge0 rho)); split => //=.
move=> /= [/= x y] [Vrx Vry].
rewrite /picard/=.
rewrite !piE/=.
rewrite infty_norm_pi/=.
rewrite /infty_norm0/=.
apply: ge_sup => //=.
  set u := _ \o _; exists (u a) => /=; exists a => //.
  by rewrite in_itv/= lexx leDl_safe_dist.
move=> _ /= [t tNdd <-].
have tb : t <= b.
  move: tNdd.
  rewrite in_itv/= => /andP[Ndt].
  move=> /le_trans; apply.
  by rewrite -lerBrDl; exact: safe_dist_itv.
rewrite /picard_fun/=; case: pselect => //= Hg; case: pselect => [Hg2|//].
rewrite /picard_fun_subdef/=.
rewrite !fctE.
rewrite (addrC u0).
rewrite addrKA.
rewrite [in leLHS]/Num.norm/= mx_normrE.
apply: bigmax_le => //= -[i j] _.
rewrite {i}(ord1 i)/=.
rewrite mxE rowRintegralE mxE rowRintegralE.
have integrable1 : mu.-integrable `[a, t] (EFin \o (fun x0 => phi x0 (x x0) ord0 j)).
  apply: integrable_comp => //=.
    by rewrite gt_eqF.
  apply: subset_trans Hg; apply: image_subset.
  apply/subset_itvl; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[].
have integrable2 : mu.-integrable `[a, t] (EFin \o (fun x0 => phi x0 (y x0) ord0 j)).
  apply: integrable_comp => //=.
    by rewrite gt_eqF.
  move=> _ [x0 h] <-.
  apply: Hg2 => /=.
  exists x0 => //.
  apply/subset_itvl/h; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[].
rewrite -RintegralB//=.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  under [x in integrable _ _  x]eq_fun do rewrite EFinB.
  by rewrite integrableB.
have integrable3 : mu.-integrable `[a, t] (fun x0 => `|x x0 - y x0|%:E).
  rewrite /=.
  apply : vintegrable_norm.
    exact: measurable_itv.
  move => i.
  under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
  rewrite integrableB//=.
    apply continuous_compact_integrable => //=.
      exact: segment_compact.
    apply within_continuous_coord.
    apply/continuous_subspaceW/cts_fun.
    apply: subset_itvl; rewrite bnd_simp.
    by move: tNdd; rewrite in_itv /= => /andP[].
  apply continuous_compact_integrable => //=.
    exact: segment_compact.
  apply within_continuous_coord.
  apply/continuous_subspaceW/cts_fun.
  apply: subset_itvl; rewrite bnd_simp.
  by move: tNdd; rewrite in_itv /= => /andP[].
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `| x t0 - y t0|))//.
  rewrite (@le_trans _ _ (\int[mu]_(t0 in `[a, t]) (k * `|x t0 - y t0|)))//.
    apply: le_Rintegral => //=.
      apply integrable_norm => //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinB.
      rewrite integrableB //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr//=.
      exact: bounded_cst.
    move=> x0 x0at.
    have : x0 \in `[a, b]%R by apply /subset_itvl/x0at.
    move/lip2.
    rewrite /dominated_by/= => /(_ (x x0, y x0)) /=.
    have Bxy : B (x x0) /\ B (y x0).
      split.
        apply: Vrx => /=.
        exists x0 => //.
        apply/subset_itvl/x0at.
        by move: tNdd; rewrite in_itv/= => /andP[Ndt].
      apply: Vry => /=.
      exists x0 => //.
      apply/subset_itvl/x0at.
      by move: tNdd; rewrite in_itv/= => /andP[Ndt].
    move=> /(_ Bxy); apply: le_trans.
    rewrite [in leRHS]/Num.norm/= mx_normrE.
    apply: le_trans; last first.
      by apply: le_bigmax => /=; exact: (ord0, j).
    by rewrite /= !mxE.
  by rewrite RintegralZl.
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `|x - y| ))//.
  rewrite ler_pM2l//.
  apply: le_Rintegral => //=.
    apply measurable_bounded_integrable => //=.
      rewrite lebesgue_measure_itv //=.
      case: ifPn => //=.
      by rewrite -EFinD ltry.
    exact: bounded_cst.
  move=> x0 x0at.
  have x0ad : x0 \in `[a, a + safe_dist]%R.
    apply: subset_itvl x0at; rewrite bnd_simp.
    by move: tNdd; rewrite in_itv/= => /andP[].
  have -> : x x0 - y x0 = (x - y : V) x0.
    apply (@eqmod_on_itv _ _ _ _ (repr x - repr y)) => //.
    by rewrite Quotient.pi_add Quotient.pi_opp !reprK.
  by rewrite infty_norm0_ge// leDl_safe_dist.
rewrite (@le_trans _ _ (k * `|x - y| * (t - a)))//.
  rewrite -mulrA ler_wpM2l//; first exact: ltW.
  rewrite Rintegral_cst// ler_pM//.
  move: tNdd; rewrite in_itv/= => /andP[+ _].
  rewrite le_eqVlt => /predU1P[->|].
    by rewrite set_itv1 lebesgue_measure_set1 subrr lexx.
  by rewrite /= (lebesgue_measure_itv `[a,t]%R) /= lte_fin => ->.
rewrite [leLHS]mulrAC ler_wpM2r//.
move: tNdd; rewrite in_itv/= => /andP[Ndt].
rewrite -lerBlDl.
rewrite /safe_dist !le_min => /andP[_ /andP[_]].
by rewrite ler_pdivlMr// mulrC.
Qed.

End is_contraction_picard.

Definition row_vector {R : realType} (n : nat) := 'rV[R]_n.

HB.instance Definition _ {R : realType} (n : nat) := Complete.on (@row_vector R n).
HB.instance Definition _ {R : realType} (n : nat) := NormedModule.on (@row_vector R n).
(*HB.instance Definition _ {R : realType} (n : nat) := CompleteNormedModule.on (@row_vector R n).*)

Section is_sol.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variable (phi : R -> U -> U).

Definition sol_is_deriv_cbnd (a : R) (b : itv_bound R) (f : R -> U) :=
  {in Interval (BLeft a) b, forall t, derivable f t 1 /\ f^`() t = phi t (f t)}.

Definition sol_is_deriv_co a b := sol_is_deriv_cbnd a (BLeft b).

Definition sol_is_deriv_obnd (a : R) (b : itv_bound R) (f : R -> U) :=
  {in Interval (BRight a) b, forall t, derivable f t 1 /\ f^`() t = phi t (f t)}.

Definition sol_is_deriv_oo a b := sol_is_deriv_obnd a (BLeft b).

(*NB: b = (BLeft r) is open,
      b = (BRight r) is closed,
      b = +oo%R is +oo *)
Definition is_sol_obnd (u0 : U) (a : R) (b : itv_bound R) (f : R -> U) :=
  [/\ f a = u0,
      sol_is_deriv_obnd a b f &
      {within (closure [set` Interval (BRight a) b]), continuous f}].

Definition is_sol_oo u0 a b := is_sol_obnd u0 a (BLeft b).

End is_sol.

Section is_integral_sol.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U).

Definition is_integral_sol := sol a = u0 /\
  forall t, t \in `[a, b]%R -> sol t = sol a + (\vint[mu]_(s in `[a, t]) phi s (sol s))%R.

End is_integral_sol.

Section integral_ode.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U) (k : R) (r : {posnum R}).
Hypothesis k0 : k != 0.
Hypothesis ab : a < b.

Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis cont_sol : {within `[a, b], continuous sol}.
Hypothesis sol_bound : sol @` `[a, b] `<=` closed_ball u0 r%:num.

Lemma picard_iterator_within_continuous i :
  {within `[a, b], continuous (fun x => phi x (sol x) ord0 i)}.
Proof.
move: i.
apply/within_continuous_coord.
exact: (@within_continuous_lipschitz _ _ _ a b u0 r _ _ _ k0).
Qed.

Lemma picard_iterator_continuous i t : t \in `]a, b[%R ->
  {for t, continuous (fun x => phi x (sol x) ord0 i)}.
Proof.
move/within_continuous_continuous; apply => //.
exact: picard_iterator_within_continuous.
Qed.

Lemma picard_iterator_integrable i : mu.-integrable `[a, b]
  (EFin \o (fun x : R => phi x (sol x) ord0 i)).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
exact: picard_iterator_within_continuous.
Qed.

Lemma integral_sol_iff_sol :
  is_integral_sol phi u0 a b sol <-> is_sol_oo phi u0 a b sol.
Proof.
split.
- move => [hinit h].
  split => //; last first.
    apply: continuous_subspaceW cont_sol.
    exact: itv_closure (* TODO: why not equality? *).
  move=> t tab.
  move: (tab); rewrite in_itv /= => /andP[ta tb].
  have -> : sol^`() t  = (fun x => sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))^`() t.
    apply/eq_on_itv_deriv/tab => x xt01; apply h.
    rewrite inE/= in xt01.
    rewrite inE/=.
    exact: subset_itv_oo_cc.
  suff hi : forall i, derivable (fun x => sol x ord0 i) t 1 /\
    (fun x : R => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))%E)^`() t ord0 i =
      phi t (sol t) ord0 i.
    split.
      apply /derivable_mxP.
      rewrite /derivable_mx => i j.
      have [? _] := hi j.
      by rewrite ord1.
    apply/rowP => j.
    by have [_ ?] := hi j.
  move => j.
  have [H1 H2] := @continuous_FTC1_closed _ (fun x => phi x (sol x) ord0 j)
    a t b tb (picard_iterator_integrable j) ta (picard_iterator_continuous tab).
  have Hderivable : derivable (fun x : R => \vint[mu]_(x0 in `[a, x]) phi x0 (sol x0)) t 1.
    apply/(@derivable_mxP R R) => i0 i; rewrite (ord1 i0){i0}/=.
    have [?] := @continuous_FTC1_closed _ (fun x => phi x (sol x) ord0 i)
      a t b tb (picard_iterator_integrable i) ta (picard_iterator_continuous tab).
    rewrite /rowRintegral.
    rewrite [X in derivable X t 1](_ : _ =
      (fun x => \int[mu]_(y in `[a, x]) phi y (sol y) ord0 i))//.
    by apply/funext => x; rewrite mxE.
  rewrite derive1E deriveD /=; last 2 first.
    exact: derivable_cst.
    exact: Hderivable.
  split.
     apply: (near_eq_derivable
         (f := (fun x => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s)) ord0 j))) => //=.
       near=> t'.
       rewrite (h t')//= in_itv/=.
       apply/andP; split.
       - by apply: ltW; near: t'; exact: lt_nbhsr.
       - by apply: ltW; near: t'; exact: lt_nbhsl.
    have -> : (fun x => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))%E ord0 j) =
              cst (sol a ord0 j) +
              (fun x => (\vint[mu]_(s in `[a, x]) (phi s (sol s))) ord0 j).
      by apply funext => x; rewrite mxE.
    apply: derivableD.
      exact: derivable_cst.
    by move/derivable_mxP : Hderivable; exact.
  rewrite -!derive1E derive1_cst add0r -H2 !derive1E derive_mx//= mxE/=.
  congr ('D_1 _ t).
  by apply/funext => t'; rewrite mxE.
move => [hinit h]; split => // t tab.
have /= := tab; rewrite in_itv/= => /andP[ta tb].
apply/rowP => i.
rewrite mxE rowRintegralE.
move: ta; rewrite le_eqVlt => /predU1P[<-|ta].
  by rewrite set_itv1 Rintegral_set1 addr0.
rewrite /Rintegral.
have cont_soli : {within `[a, b], continuous (fun x => sol x ord0 i)}.
  by move: i; exact/within_continuous_coord.
rewrite (@continuous_FTC2 _ (fun x => phi x (sol x) ord0 i) (fun x => sol x ord0 i) _ _ ta).
- by rewrite -EFinB subrKC.
- apply: continuous_subspaceW; last exact: picard_iterator_within_continuous.
  exact: subset_itvl.
- split.
  + move=> t' tx'.
    by have /h[/derivable_mxP] : t' \in `]a, b[%R by exact/subset_itvl/tx'.
  + by move /(continuous_within_itvP _ ab) : cont_soli => [_ + _].
  + have cont_phii' : {within `[a, t], continuous fun x0 : R => sol x0 ord0 i}.
      apply: continuous_subspaceW; last exact: cont_soli.
      exact: subset_itvl.
    by move/(continuous_within_itvP _ ta) : cont_phii' => [_ _ +].
- move=> x xt.
  have /h[? +] : x \in `]a, b[%R by exact/subset_itvl/xt.
  by rewrite !derive1E derive_mx//= => <-; rewrite mxE.
Unshelve. all: by end_near. Qed.

End integral_ode.

Section picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let k0' : k != 0. Proof. by rewrite gt_eqF. Qed.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Variable rho : {posnum R}.
Hypothesis rho1 : rho%:num < 1.

Import ContSeg_quot.

Check U : completeType.
Check U : completePseudoMetricType R.
Check U : normedModType R.
Check U : completeNormedModType R.

Local Notation safe_dist := (@safe_dist R n phi a b k u0 r rho).
Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Check V : completeNormedModType _.

Local Notation img_cball := (@img_cball R n phi a b k  u0 r rho).
Local Notation img_cball_nonempty := (img_cball_nonempty phi a b k u0 r rho).
Local Notation closed_img_cball := (@closed_img_cball R n phi a b k u0 r k0 rho ab).

Local Notation picard := (@picard _ n phi a b k u0 r k0 lip2 cont1 rho).

Definition picard_fix : V :=
  sval (cid2 (@banach_fixed_point R V img_cball
    picard
    (@is_contraction_picard _ n phi a b ab k k0 u0 r lip2 cont1 rho rho1)
    closed_img_cball
    img_cball_nonempty)).

Let picard_fixE : picard_fix = picard picard_fix.
Proof. by rewrite {}/picard_fix; case: cid2. Qed.

Lemma img_cball_picard_fix : img_cball picard_fix.
Proof.
by apply (svalP (cid2 (@banach_fixed_point R V img_cball _
  (@is_contraction_picard R n phi _ _ ab k k0 u0 r lip2 cont1 _ rho1)
  closed_img_cball img_cball_nonempty))).
Qed.

Lemma picard_fix_init : picard_fix a = u0.
Proof.
rewrite picard_fixE eval_mod_on_itv.
  by rewrite /picard_fun /= picard_fun_init//; exact: img_cball_picard_fix.
by rewrite in_itv/= lexx leDl_safe_dist.
Qed.

Lemma picardE g t : img_cball g -> t \in `[a, a + safe_dist]%R ->
  picard g t = u0 + \vint[mu]_(x in `[a, t]) phi x (g x).
Proof.
by move=> Hg taad; rewrite eval_mod_on_itv//; exact: picard_funE.
Qed.

Lemma cauchy_lipschitz_integral_version :
  is_integral_sol phi u0 a (a + safe_dist) picard_fix.
Proof.
split; first exact: picard_fix_init.
move=> t tad.
rewrite {1}picard_fixE// eval_mod_on_itv//.
rewrite picard_fix_init.
exact: picard_funE img_cball_picard_fix.
Qed.

Theorem cauchy_lipschitz_unique (picard_fix' : V) : img_cball picard_fix' ->
  (forall t, t \in `[a, a + safe_dist]%R ->
  picard_fix' t = u0 + \vint[mu]_(x in `[a, t]) phi x (picard_fix' x)) ->
  picard_fix = picard_fix'.
Proof.
move=> imgpicard_fix'_cball h.
apply: (contraction_fixpoint_unique
  (@is_contraction_picard R n phi a b ab k k0 u0 r lip2 cont1 rho rho1)
  img_cball_picard_fix imgpicard_fix'_cball) => //=.
rewrite -(reprK picard_fix').
apply/eqquotP.
rewrite /Quotient.equiv/=.
rewrite inE.
apply/funext => x.
rewrite /patch mem_setE; case: ifPn => [xK|xKnot]; last by [].
rewrite /fun_of_quot_contSeg/=.
rewrite !fctE.
rewrite !reprK.
rewrite picard_funE//=.
rewrite (_ : repr picard_fix' x = picard_fix' x)//.
by rewrite h// subrr.
Qed.

Theorem cauchy_lipschitz_existence : picard_fix a = u0 /\
  {in `]a, a + safe_dist[%R, forall x, picard_fix^`() x = phi x (picard_fix x)}.
Proof.
split; first exact: picard_fix_init.
move => t tad.
rewrite {1}picard_fixE.
apply/rowP => j.
suff -> : (picard picard_fix)^`() t =
          (fun t => u0 + \vint[mu]_(x in `[a, t]) phi x (picard_fix x))^`() t.
  move: (tad); rewrite in_itv /= => /andP[ta tadelta].
  have Fint i : mu.-integrable `[a, a + safe_dist]
      (EFin \o (fun x => phi x (picard_fix x) ord0 i)).
    apply: integrable_comp => //.
      by rewrite in_itv /= lexx andbT leDl_safe_dist.
    exact: img_cball_picard_fix.
  have Fcont i : {for t, continuous (fun x => phi x (picard_fix x) ord0 i)}.
    move: tad; rewrite inE.
    apply/within_continuous_continuous => //=.
      exact: ltDl_safe_dist.
    clear Fint.
    move: i; apply/within_continuous_coord.
    apply: (@within_continuous_lipschitz _ _ _ a _ u0 r _ _ _ k0').
    + exact: cts_fun.
    + exact: lip2_safe_dist.
    + exact: cont1_safe_dist.
    + exact: img_cball_picard_fix.
  have [H1 H2] := @continuous_FTC1_closed _ (fun x => phi x (picard_fix x) ord0 j)
                  a t _ tadelta (Fint j) ta (Fcont j).
  have Hderivable : derivable (fun x => \vint[mu]_(y in `[a, x]) phi y (picard_fix y)) t 1.
    apply/derivable_mxP => i0 i; rewrite (ord1 i0){i0}/=.
    have [?] := @continuous_FTC1_closed _ (fun x => phi x (picard_fix x) ord0 i)
                a t _ tadelta (Fint i) ta (Fcont i).
    rewrite /rowRintegral.
    rewrite [X in derivable X t 1](_ : _ =
        (fun x => \int[mu]_(y in `[a, x]) phi y (picard_fix y) ord0 i))//.
    by apply/funext => x; rewrite mxE.
  rewrite derive1E deriveD /=; last 2 first.
    exact: derivable_cst.
    exact: Hderivable.
  rewrite -!derive1E derive1_cst add0r -H2 !derive1E derive_mx// mxE/=.
  congr ('D_1 _ t).
  by apply/funext => t0; rewrite mxE.
rewrite /picard /picard_fun.
move: t tad.
apply: eq_on_itv_deriv => t tad /=.
rewrite -(@picard_funE _ _ _ a b k _ r k0' lip2 cont1 rho)//=.
  rewrite eval_mod_on_itv// inE; apply: subset_itv_oo_cc.
  by rewrite inE in tad.
exact: img_cball_picard_fix.
Qed.

Lemma cauchy_lipschitz_in_cball (t : R) : `[a, a + safe_dist] t ->
  closed_ball u0 r%:num (picard_fix t).
Proof. by move=> taad; apply: img_cball_picard_fix => /=; exists t. Qed.

End picard.

Section picard_extension.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b c : R) (u0 : U) (sol1 : R -> U) (sol2 : R -> U).
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous (fun x => phi x (sol1 x))}.
Hypothesis cont2 : {within `[b, c], continuous (fun x => phi x (sol2 x))}.
Hypothesis matchb : sol1 b = sol2 b.

Lemma solution_extends : is_integral_sol phi u0 a b sol1 ->
  is_integral_sol phi (sol1 b) b c sol2 ->
  is_integral_sol phi u0 a c (patch sol2 `[a, b] sol1).
Proof.
move => [p0a p0s ] [p1a p1s].
have h0 : patch sol2 `[a, b] sol1 a = u0.
  rewrite /patch.
  case: ifPn => [xK | xKnot] => //.
  move /negP : xKnot.
  by rewrite inE/=in_itv/=lexx ltW.
split=> //.
move=> t tac.
rewrite /patch mem_setE bound_itvE (ltW ab).
case: ifPn => [xK | xKnot] => /=.
  rewrite p0s // p0a.
  apply/rowP => i.
  rewrite !mxE.
  congr (_ + _)%E.
  apply eq_Rintegral => /= x xat.
  suff -> : x \in `[a, b]%R by [].
  move : xat xK.
  rewrite mem_setE /= !in_itv /= => /andP [xat1 xat2] /andP [tab1 tab2].
  apply/andP; split => //.
  exact/le_trans/tab2.
have tbc : t \in `[b, c]%R.
  move : tac.
  move/negP : xKnot.
  rewrite !in_itv /=.
  have /orP := le_total b t.
  case => // -> h1 /andP [h2 ->] //.
  by move: h1; rewrite h2.
transitivity (sol1 a + \vint[lebesgue_measure]_(s in `[a, t])
    phi s (if (s \in `[a, b])%classic then sol1 s else sol2 s))%E; last first.
  by under eq_rowRintegral do rewrite mem_setE.
rewrite (rowRintegral_itv_split (c := b) (F := (fun x => phi x (patch sol2 `[a, b] sol1 x)))).
- rewrite p1s//.
  suff : sol2 b = u0 + \vint[lebesgue_measure]_(s in `[a, b]) phi s (patch sol2 `[a, b] sol1 s).
    move=> ->.
    rewrite -p0a.
    rewrite [in RHS]addrA.
    congr +%R.
    apply eq_rowRintegral => /= x xbt.
    rewrite /patch; case: ifPn => [ | ] => //.
    rewrite inE/=in_itv/= => /andP [_ xleb].
    move : xbt.
    rewrite !inE/=!in_itv/= => /andP [h _].
    suff -> : x = b by rewrite p1a.
    apply le_anti.
    by rewrite xleb.
  rewrite p1a p0s;last by rewrite in_itv/= ltW/=.
  rewrite p0a.
  congr (u0 + _)%E.
  rewrite /patch.
  by apply eq_rowRintegral => /= x ->.
- by rewrite ltW //=; move : tbc; rewrite in_itv/= => /andP [-> _].
- move=> i.
  have cont' : {within `[a, t], continuous (fun x => phi x (patch sol2 `[a, b] sol1 x) ord0 i)}.
    have -> : `[a, t] = `[a, b] `|` `[b, t].
      rewrite (@itv_bndbnd_setU _ _ _ (BRight b))// ?bnd_simp//=; last 2 first.
        exact: ltW.
        by move: tbc; rewrite in_itv/= => /andP[].
      apply/seteqP; split => x.
        move=> []; [by left|right].
        exact: subset_itv_oc_cc b0.
      move=> []; [by left|].
      rewrite -setU1itv ?bnd_simp//; last first.
        by move: tbc; rewrite in_itv/= => /andP[].
      case; [|by right].
      move=> ->; left => /=.
      by rewrite in_itv/= (ltW ab) lexx.
    apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b t)).
      move : i.
      apply /within_continuous_coord.
      have eq1 : {in `[a, b], (fun x0 => phi x0 (sol1 x0)) =1
                              (fun x0 => phi x0 (patch sol2 `[a, b] sol1 x0))}.
        move => x0 x0ab.
        by rewrite /patch x0ab.
      apply: (continuous_within_ext eq1).
      exact: cont1.
    move : i.
    apply /within_continuous_coord.
    have eq2 : {in `[b, c], (fun x0 => phi x0 (sol2 x0)) =1
                            (fun x0 => phi x0 (patch sol2 `[a,b] sol1 x0))}.
      move => x0 x0ab.
      rewrite /patch mem_setE;case: ifPn => [xab | xabnot] => //.
      suff -> : x0 = b by rewrite matchb.
      apply: le_anti.
      move: x0ab xab.
      by rewrite inE/= !in_itv/= => /andP [-> _] /andP [_ ->].
    apply/continuous_subspaceW/(continuous_within_ext eq2)/cont2.
    apply: subset_itvl; rewrite bnd_simp.
    by move : tbc; rewrite in_itv/= => /andP[].
  apply: continuous_compact_integrable => //.
  exact: segment_compact.
Qed.

End picard_extension.

Section cauchy_lipschitz_local.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let k0' : k != 0. Proof. by rewrite gt_eqF. Qed.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}.
Hypothesis rho1 : rho%:num < 1.
(* Let rho : {posnum R} := (2^-1)%:pos. *)

(* Let rho1 : rho%:num < 1. *)
(* Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed. *)

Definition local_solution := repr (picard_fix ab k0 lip2 cont1 rho1).

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).

Lemma solution_local_solution : is_sol_oo phi u0 a (a + safe_dist) local_solution.
Proof.
apply/(integral_sol_iff_sol (k:=k) (r:=r)) => //.
- by rewrite ltDl_safe_dist.
- move=> t td.
  apply: lip2.
  move: td; rewrite /=!in_itv/= => /andP [-> h] /=.
  by rewrite (le_trans h)// -lerBrDl; exact: safe_dist_itv.
- move=> /= x xB  .
  apply/continuous_subspaceW/cont1 => //.
  apply: subset_itvl => //=.
  by rewrite bnd_simp -lerBrDl safe_dist_itv.
- rewrite /local_solution.
  exact: cts_fun.
- by move => _ [t tad] <-; exact: cauchy_lipschitz_in_cball.
- exact: cauchy_lipschitz_integral_version.
Qed.

Lemma solution_stays_in_ball :
  {in `[a, a + safe_dist]%R, forall t, closed_ball u0 r%:num (local_solution t)}.
Proof. by move=> t; move => /cauchy_lipschitz_in_cball; exact. Qed.

Lemma solution_continuous :
  {within `[a, a + safe_dist], continuous local_solution}.
Proof. exact: cts_fun. Qed.

Definition cauchy_lipschitz_local_f :
    continuousFunType `[a, a + safe_dist] [set: 'rV[R]_n] :=
  repr (picard_fix ab k0 lip2 cont1 rho1).

Let f := cauchy_lipschitz_local_f.

Theorem cauchy_lipschitz_local :
  safe_dist > 0 /\
  is_sol_oo phi u0 a (a + safe_dist) f /\
  {in `[a, a + safe_dist]%R, forall t, closed_ball u0 r%:num (f t)}.
Proof.
split; first exact: safe_dist_gt0.
split.
- exact: solution_local_solution.
- exact: solution_stays_in_ball.
Qed.

Local Notation V := (@ContSeg_quot.quot_contSeg R a (a + safe_dist) U).

Theorem cauchy_lipschitz_local_unique f' :
  {within `[a, a + safe_dist], continuous f'} ->
  {in `[a, a + safe_dist]%R, forall t, closed_ball u0 r%:num (f' t)}  ->
  is_sol_oo phi u0 a (a + safe_dist) f' ->
  {in `[a, a + safe_dist]%R, f =1 f'}.
Proof.
move => cont bnd.
move/(@integral_sol_iff_sol _ _ _ _ _ _ _ _ r k0') => []//.
- exact: ltDl_safe_dist.
- move=> t td.
  apply: lip2.
  by apply: subset_itvl td; rewrite bnd_simp -lerBrDl safe_dist_itv.
- move=> /= x xB.
  apply/continuous_subspaceW/cont1 => //.
  by apply: subset_itvl => //=; rewrite bnd_simp -lerBrDl safe_dist_itv.
- by move => _ [t tad] <-;apply bnd;rewrite inE.
move=> f'au0 h1 t tab.
have fc : contseg a (a + safe_dist) f' by exact: mem_set.
have pieq : \pi_V%qT f = \pi_V%qT (contseg_Sub fc).
  rewrite reprK.
  apply: cauchy_lipschitz_unique.
    move => /= _ [t' tad' ] <- /=.
    rewrite /ContSeg_quot.fun_of_quot_contSeg.
    suff -> : (repr (\pi_V%qT (contseg_Sub fc))) t' = f' t'.
      by apply: bnd; rewrite inE.
    by apply: ContSeg_quot.eval_mod_on_itv; rewrite inE.
  move=> t0 t0ad.
  rewrite ContSeg_quot.eval_mod_on_itv //=.
  rewrite h1//.
  rewrite f'au0; congr (u0 + _).
  apply: eq_rowRintegral => t' tad'.
  rewrite ContSeg_quot.eval_mod_on_itv //=.
  move: tad'; rewrite !inE/=;  apply: subset_itvl; rewrite bnd_simp.
  rewrite inE/= in t0ad.
  by move/itvP : t0ad => ->.
suff -> : f t = (ContSeg_quot.fun_of_quot_contSeg (\pi_V%qT (contseg_Sub fc))) t.
  rewrite /ContSeg_quot.fun_of_quot_contSeg/=.
  exact: ContSeg_quot.eval_mod_on_itv.
rewrite -pieq.
by rewrite ContSeg_quot.eval_mod_on_itv.
Qed.

End cauchy_lipschitz_local.

Section continuous_confined.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (a b : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Let B := closed_ball u0 r%:num.

Local Lemma continuous_confined  (g : R -> U) : {within `[a, b], continuous g} ->
  g a = u0 ->
  exists Delta : {posnum R}, {in `[a, a + Delta%:num], forall t, g t \in B}.
Proof.
move /(continuous_within_itvP _ ab)  => [cc cl cr] g0.
have : {within `[a,b], continuous (fun t => `| u0 - g t |) }.
  apply: within_continuous_comp_norm.
    by rewrite ltW.
  apply/continuous_within_itvP => //=.
  split.
  - move => t tab.
    exact: (cvgB (cvg_cst _) (cc _ tab)).
  - exact: (cvgB (cvg_cst _) cl).
  - exact: (cvgB (cvg_cst _) cr).
move/(continuous_within_itvP _ ab) => [_ /cvgrPdist_le + _].
move=> /(_ r%:num).
case=> // Delta /= Delta0.
rewrite /ball_/= g0 subrr normr0/= => H.
have D20 : (0 < Delta / 2) by rewrite divr_gt0.
exists (PosNum D20) => t.
rewrite inE/= in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<-|ta td].
  by rewrite g0 /B inE => _; exact: closed_ballxx.
have /= := H t.
rewrite add0r normrN normr_id.
rewrite inE /B closed_ballE /closed_ball_//=; apply => //.
rewrite ltr0_norm ?subr_lt0// opprB ltrBlDl.
by rewrite (le_lt_trans td)// ltrD2l gtr_pMr// invf_lt1// ltr1n.
Qed.

End continuous_confined.

Section solution_locally_unique.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}) (f : R -> U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis cf : {within `[a, b], continuous f}.
Hypothesis sol1 : is_sol_oo phi u0 a b f.
Let rho_max : {posnum R} := (2^-1)%:pos.

Let dmax rho := safe_dist phi a b k u0 r rho.
Let fc := local_solution ab k0 lip2 cont1.

Lemma initial_solution_unique f' : {within `[a, b], continuous f'} ->
  is_sol_oo phi u0 a b f' ->
  exists D : {posnum R}, {in `[a, a + D%:num]%R, f =1 f'} /\
    {in `[a, a + D%:num]%R, forall t, closed_ball u0 r%:num (f t)}.
Proof.
move => cf' sol2.
suff [rho [D [Hrho [Db P1 P2]]]] : exists rho D : {posnum R}, exists (Hrho : rho%:num < 1),
    [/\ D%:num <= dmax rho,
        {in `[a, a + D%:num]%R, f =1 fc Hrho } &
        {in `[a, a + D%:num]%R, f' =1 fc Hrho} ].
  exists D; split => t tab; first by rewrite P1// P2.
  rewrite P1//.
  apply: solution_stays_in_ball.
  by move: tab; rewrite !inE; apply: subset_itvl; rewrite bnd_simp lerD2l.
have [d1 D1] := continuous_confined r ab cf (And31 sol1).
have [d2 D2] := continuous_confined r ab cf' (And31 sol2).
have [rho [drho1 drho2]] : exists rho, dmax rho <= (Num.min d1%:num d2%:num) /\ rho%:num < 1.
  rewrite /dmax/safe_dist.
  have posk : 0 < Num.min rho_max%:num (Num.min (k * rho_max%:num) (k * (Num.min d1%:num d2%:num))).
    by rewrite lt_min/= invr_gt0// ltr0n/= lt_min divr_gt0//= mulr_gt0.
  exists (PosNum posk); split => //=.
    rewrite !ge_min/= minA; apply/orP; right.
    rewrite !minr_pMl//=; [|by rewrite ltW// invr_gt0..].
    do 2 rewrite ge_min; apply/orP; right.
    apply/orP; right.
    by rewrite mulrAC divff ?mul1r// gt_eqF//.
  by rewrite gt_min; apply/orP; left; rewrite invf_lt1// ltr1n.
have drho_pos : 0 < dmax rho by exact: safe_dist_gt0.
exists rho, (PosNum drho_pos), drho2; split => //.
- move => t tad.
  apply/esym; apply: cauchy_lipschitz_local_unique.
  - apply/continuous_subspaceW/cf => //.
    apply: subset_itvl => //=.
    by rewrite bnd_simp -lerBrDl;apply safe_dist_itv.
  - move=> t0 t0ad.
    suff : f t0 \in closed_ball u0 r%:num by rewrite inE.
    apply D1.
    move: t0ad; rewrite !inE/=; apply: subset_itvl; rewrite bnd_simp/=.
    by rewrite lerD2l// (le_trans drho1)// ge_min lexx.
  - split; first by apply sol1.
    move=> t0 t0ad.
    have [_ + _] := sol1; apply.
    by move: t0ad; rewrite !inE/=; apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
  - apply: continuous_subspaceW cf.
    apply: subset_trans; first exact: itv_closure.
    by apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
  - exact: tad.
move => t tad.
apply/esym; apply : cauchy_lipschitz_local_unique.
- apply/continuous_subspaceW/cf' => //.
  by apply: subset_itvl => /=; rewrite bnd_simp -lerBrDl;apply safe_dist_itv.
- move=> t0 t0ad.
  suff : f' t0 \in closed_ball u0 r%:num by rewrite inE.
  apply D2.
  move: t0ad; rewrite !inE; apply: subset_itvl; rewrite bnd_simp lerD2l.
  by rewrite (le_trans drho1)// ge_min lexx orbT.
- split; first by apply sol2.
  move=> t0 t0ad.
  have [_ + _] := sol2; apply.
  by move: t0ad; rewrite !inE; apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
- apply/continuous_subspaceW/cf' => //.
  apply: subset_trans; first exact: itv_closure.
  by apply: subset_itvl; rewrite bnd_simp -lerBrDl;apply safe_dist_itv.
exact: tad.
Qed.

End solution_locally_unique.

(* TODO: move *)
Section closure_neitv.
Context {R : realType}.
Implicit Type a b : R.

Lemma closure_neitv_oo a b : a < b ->
  closure `]a, b[%classic = `[a, b]%classic.
Proof.
move=> ab.
set c := (a + b) / 2%:R.
set d := (b - a) / 2%:R.
rewrite (_ : a = c - d); last by rewrite /c/d !mulrDl addrKA mulNr opprK -splitr.
rewrite (_ : b = c + d); last by rewrite addrC /c/d !mulrDl mulNr subrKA -splitr.
rewrite -ball_itv -closed_ball_itv ?closure_ballE//.
apply: divr_gt0 => //.
by rewrite subr_gt0.
Qed.

End closure_neitv.

(* TODO: move *)
Lemma within_continuousB {K : realType} {V : normedModType K}
    (A : set K) (f g : _ -> V) :
  {within A, continuous f} -> {within A, continuous g} ->
  {within A, continuous (f - g)}.
Proof.
by move=> cf cg x; apply: cvgB; [exact: cf|exact: cg].
Qed.

Section uniqueness.
Context {R : realType} {n : nat} (a b : R).
Notation U := 'rV[R]_n.
Variable phi : R -> U -> U.
Hypothesis ab : a < b.

Variables (u0 : U).
Hypothesis cont1 : forall y, {within `[a, b], continuous phi ^~ y}.
Hypothesis phi_loclip :
  forall x, exists r k : {posnum R},
    forall t, k%:num.-lipschitz_(closed_ball x r%:num) (phi t).
Variables (f : R -> U) (f' : R -> U).
Hypothesis sol1 : is_sol_oo phi u0 a b f.
Hypothesis sol2 : is_sol_oo phi u0 a b f'.

Lemma locally_unique_extends t : a <= t < b -> f' t = f t ->
  exists Delta : {posnum R}, {in `[t, t + Delta%:num]%R, f =1 f'}.
Proof.
move=> /andP[ta tb] eq.
have [r [k L]] := phi_loclip (f t).
have taab : `[t, b] `<=` `[a, b].
  by move=> ?/=; apply: subset_itvr; rewrite bnd_simp.
have cf0 : {within `[t, b], continuous f}.
  have := And33 sol1.
  rewrite closure_neitv_oo//; exact: continuous_subspaceW.
have cf'0 : {within `[t, b], continuous f'}.
  have := And33 sol2.
  by rewrite closure_neitv_oo//; exact: continuous_subspaceW.
have sol10 : is_sol_oo phi (f t) t  b f.
  split => //; last by rewrite closure_neitv_oo.
  move=> t0 tab.
  apply sol1.
  by move: tab; rewrite !inE/=; apply: subset_itvr; rewrite bnd_simp.
have sol20 : is_sol_oo phi (f t) t b f'.
  split => //; last by rewrite closure_neitv_oo.
  move=> t0 tab.
  apply sol2.
  by move: tab; rewrite !inE/=; apply: subset_itvr; rewrite bnd_simp.
have lip20 : {in `[t, b]%R, forall x,  k%:num.-lipschitz_(closed_ball (f t) r%:num) (phi x)}.
  by move => t0 _;apply L.
have cont1' : {in closed_ball (f t) r%:num,
  forall y : 'rV_n, {within `[t, b], continuous  phi^~ y}}.
    move => y ytb.
   apply /continuous_subspaceW/cont1.
   by apply subset_itvr.
have k0 : 0 < k%:num by [].
have [D [P1 P2]] := initial_solution_unique tb k0 lip20 cont1' cf0 sol10 cf'0 sol20.
by exists D.
Qed.

Let in1_eq1 : {in `[a, a]%R, f =1 f'}.
Proof.
move=> t; rewrite in_itv/= -eq_le => /eqP <-.
by rewrite (And31 sol1) (And31 sol2).
Qed.

Lemma solution_unique : {in `[a, b]%R, f =1 f'}.
Proof.
set E := `[a, b]%classic `&` [set t | {in `[a, t]%R, f =1 f'}].
suff : E b by case.
have Ea : E a by split=> //=; rewrite bound_itvE/= ltW.
have Enonempty : E !=set0 by exists a.
have mon c : E c -> forall d, d \in `[a, c]%R -> E d.
  move=> [/= cab] acff' d dac; split => /=.
    by apply: subset_itvl dac; rewrite bnd_simp (itvP cab).
  move=> t tad; apply: acff'.
  by apply: subset_itvl tad; rewrite bnd_simp (itvP dac).
have monC c d : a <= d -> E c -> ~ E d -> c < d.
  move=> ad Ec nEd.
  rewrite ltNge; apply/negP => cd.
  apply/nEd/(mon c) => //.
  by rewrite in_itv/= ad.
have [hP|/(has_supPn Enonempty)] := lem (has_sup E); last first.
  move=> /(_ b)[x Ex bx].
  by apply/(mon x) => //; rewrite in_itv/= !ltW.
have Eclosed : closed E.
  rewrite closedE/= => p pn.
  suff : forall x, ~ E x -> \forall y \near x, ~ E y.
    by apply: contraPP => Ep /(_ _ Ep).
  move=> x notEx.
  have [xab|xnab] := boolP (x \in `[a, b]%R); last first.
    suff : \forall y \near x, ~ (y \in `[a,b]%R).
      by move=> ?; near do (rewrite not_andP; left).
    move: xnab; rewrite in_itv/= negb_and/= -!ltNge => /orP[xa|xb].
    - near do (apply/negP; rewrite in_itv negb_and/= -!ltNge; apply/orP; left).
      exact: lt_nbhsl.
    - near do (apply/negP; rewrite in_itv negb_and/= -!ltNge; apply/orP; right).
      exact: lt_nbhsr.
  move: notEx;rewrite not_andP => -[//|notEx].
  have [t Et] : exists t, t \in `[a, x]%R /\ f t != f' t.
     rewrite not_existsP => h.
     apply: notEx => t tax.
     have := h t.
     by rewrite not_andP => -[//|/negP/negPn/eqP].
  have [xt|xt]:= eqVneq x t.
    subst t.
    set g := fun x => `|f x - f' x|.
    have contg : {within `[a, b], continuous g}.
      apply/(within_continuous_comp_norm (ltW ab))/within_continuousB.
      - by have := And33 sol1; rewrite (closure_neitv_oo ab).
      - by have := And33 sol2; rewrite (closure_neitv_oo ab).
    have g0x : g x > 0 by rewrite normr_gt0 subr_eq0; case: Et.
    have g0 t : t \in `[a, b]%R -> g t > 0 -> ~ {in `[a, t]%R, f =1 f'}.
      move=> tab + atff'.
      suff -> : g t = 0 by rewrite ltxx.
      apply/normr0P; rewrite atff' ?subrr//.
      by move: tab; rewrite !in_itv/= lexx => /andP[->].
    suff hgx: \forall y \near x^'-, 0 < g y.
      near=> y.
      have [yx|xy Ey] := ltP y x; last first.
        have := mon _ Ey x.
        move: xab.
        by rewrite !in_itv/= xy => /andP[-> _] /(_ isT)[].
      apply/not_andP; rewrite -implyE => yab.
      apply: g0 => //.
      by move: yx; near: y.
    apply: (@cvgr_gt _ _ (x^'-) _ g (g x)) => //.
    have xa : a < x.
      rewrite ltNge.
      contra: notEx.
      move: xab; rewrite in_itv/= => /andP[+ _] ax.
      by move/(conj ax) => /andP; rewrite -eq_le => /eqP ->.
    have /(continuous_within_itvP _ ab)[cg _ gbb] := contg.
    move: xab; rewrite in_itv/= => /andP[_ ].
    rewrite le_eqVlt => /predU1P[-> //|xb].
    apply/cvg_at_left_filter/cg.
    by rewrite in_itv/= xb xa.
  have tx : t < x.
    by case: Et; rewrite in_itv/= lt_neqAle (eq_sym t) xt => /andP[_ ->].
  near=> y.
  move=> Ey.
  have ta : a <= t by case: Et; rewrite in_itv/= => /andP[].
  have /(monC _ _ ta Ey) : ~ E t.
    rewrite not_andP; right => /(_ t).
    by rewrite bound_itvE/= ta => /(_ isT); apply/eqP; case: Et.
  apply/negP; rewrite -leNgt.
  by near: y; exact: nbhs_ge.
have supE : E (sup E).
  by rewrite {1}(closure_id E).1//; apply: closure_sup => //; apply hP.
have sup_itv : a <= sup E by rewrite sup_upper_bound.
have supeq : f' (sup E) = f (sup E).
  apply/esym; apply supE.
  by rewrite  in_itv/= lexx sup_itv.
have [h|h] := leP b (sup E).
  apply: (mon _ supE) => //.
  by rewrite in_itv/= (ltW ab).
have [|Delta Hdelta] := locally_unique_extends _ supeq; first by apply/andP.
have Delta0 : 0 < Delta%:num by [].
suff : Num.min b (sup E + Delta%:num) <= sup E.
  rewrite ge_min => /orP[/(lt_le_trans h)|].
    by rewrite ltxx.
  by rewrite gerDl leNgt Delta0.
apply: sup_upper_bound => //.
split.
  by rewrite /= in_itv/= le_min (ltW ab)/= ler_wpDr//= ge_min lexx.
move=> t ta.
have [ht|ht] := leP t (sup E).
  by apply supE; rewrite in_itv/= (itvP ta).
apply: Hdelta; rewrite in_itv/= ltW//=.
by move: ta; rewrite in_itv/= le_min => /and3P[_].
Unshelve. all: by end_near. Qed.

End uniqueness.

Section picard_symmetric.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (k : R) (u0 : U) (r : {posnum R})  (a b : R).
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Definition phi_ (t : R) x := phi x.

Definition is_sol_sym u0 t0 d (sol : R -> U):=
   sol t0 = u0 /\ sol_is_deriv_oo phi (t0-d) (t0+d) sol.

Let phi_lip2 t0: t0 \in `[a,b]%R ->  {in `[t0, b]%R, forall x, k.-lipschitz_B (phi x)}.  
Proof.
move => tab x abx; apply: lip2.
move : abx; rewrite !inE/=; apply subset_itvr.
by move : tab; rewrite in_itv/= bnd_simp => /andP[-> _].
Qed.

Let phi_cont1 t0 : t0 \in `[a,b]%R -> {in B, forall y, {within `[t0, b], continuous phi ^~ y}}.
Proof.
move => /= tab x Bx.
apply /continuous_subspaceW/cont1 => //.
apply: subset_itvr.
by move : tab; rewrite in_itv/= bnd_simp => /andP[-> _].
Qed.


Let rho : {posnum R} := (2^-1)%:pos.

Let rho1 : rho%:num < 1.
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Let cauchy_lipschitz_fwd t0 : t0 \in `]a,b[%R -> exists f delta,
  delta > 0 /\ is_sol_oo (phi) u0 t0 (t0 + delta) f /\
  {in `[t0, t0 + delta]%R, forall t, closed_ball u0 r%:num (f t)}.
Proof.
rewrite /=in_itv/= => /andP[t0a t0b].
have tab : t0 \in `[a,b]%R.
  by rewrite in_itv/= !ltW.
have [d0 [solf cball]] :=
  cauchy_lipschitz_local t0b k0 (phi_lip2 tab) (phi_cont1 tab) rho1.
exists (@cauchy_lipschitz_local_f R n phi t0 _ k u0 r t0b k0
  (phi_lip2 tab) (phi_cont1 tab) rho rho1).
by exists (safe_dist phi t0 b k u0 r rho).
Qed.

Lemma patch_in {X : Type} (f g : R -> X)  S x : x \in S -> patch f S g x = g x.
Proof.
  move => xs.
  rewrite /patch.
  by rewrite xs.
Qed.


Lemma closed_ball_split (x1 x2 y :U) q : 0 < q ->  closed_ball x1 (q/2) y -> closed_ball x2 (q/2) x1  -> closed_ball x2 q y.
Proof.
  move => hq.
  have hq2:  (0 < q /2).
    by rewrite divr_gt0.
  rewrite !closed_ballE// /closed_ball_ /=. 
  move => h1 h2.
  rewrite -(subrKA x1 x2).
  by apply: (le_trans (ler_normD _ _)); rewrite (splitr q) lerD//.
Qed.

(*todo : move or PR? *)
Lemma within_continuous_minus  (f : R -> U) (c d : R) :
  {within `[-d,-c], continuous f} -> {within `[c,d], continuous f \o -%R}.
Proof.
have [ab|ba _ |-> _] := ltgtP c d; last 2 first.
  by rewrite set_itv_ge ?bnd_simp -?ltNge//; exact: continuous_subspace0.
  by rewrite set_itv1; exact: continuous_subspace1.
move/continuous_within_itvP; rewrite ltrN2 => /(_ ab)[cf fb fa].
apply/(continuous_within_itvP _ ab); split.
- move=> t tab.
  apply: (@cvg_comp _ _ _ -%R f); first exact: oppr_continuous.
  by apply: cf; rewrite oppr_itvoo !opprK.
- by rewrite -{1}(opprK c); apply/cvg_at_leftNP; exact: fa.
- by rewrite -{1}(opprK d); apply/cvg_at_rightNP; exact: fb.
Qed.

Let phi_lip2' t0 : t0 \in `[a,b] ->  {in `[-t0, -a]%R, forall x, k.-lipschitz_B (-phi (-x))}.
Proof.
move => t0ab  /= y ab x B12.
rewrite /= -normrN opprD !opprK.
apply: (lip2 _  B12).
move : ab.
rewrite !in_itv/= lerNl lerNr => /andP[h1 ->]//=.
apply (le_trans h1).
move : t0ab.
by rewrite inE/=in_itv/= => /andP[].
Qed.

Local Lemma phi_cont1' t0 : t0 \in `[a,b] -> {in B, forall y, {within `[-t0, -a], continuous -(fun t => phi (-t) y)}}.
Proof. 
move => t0ab /= y By.
move => t.
apply: continuousN.
have /within_continuous_minus : {within `[-(-a), - (-t0)], continuous phi^~ y}. 
  rewrite !opprK.
  apply /continuous_subspaceW/cont1 => //.
  apply : subset_itvl.
  by move: t0ab; rewrite inE/=in_itv/= bnd_simp => /andP[].
apply.
Qed.

Lemma cauchy_lipschitz_sym t0 : t0 \in `]a,b[%R -> exists f delta, delta > 0 /\ is_sol_sym u0 t0 delta f.
Proof.
move => t0ab.
have t0ab' : t0 \in `[a,b].
  by rewrite inE;apply: subset_itv_oo_cc.
have  [fplus [dplus [dplus0 [solplus cplus]]]] := cauchy_lipschitz_fwd t0ab.
have amin1 : -t0 < -a.
  rewrite ltrNr opprK.
  by move : t0ab; rewrite in_itv/= => /andP[].
have [dminus0 [solminus cminus]] :=
  cauchy_lipschitz_local amin1 k0
    (phi_lip2' t0ab') (phi_cont1' t0ab') rho1.

set fminus0 :=
  @cauchy_lipschitz_local_f R n (fun t x => - phi (-t) x) (-t0) _ k u0 r
    amin1 k0 (phi_lip2' t0ab') (phi_cont1' t0ab') rho rho1.
set dminus := safe_dist (fun t x => - phi (-t) x) (-t0) (-a) k u0 r rho.
set fminus := fminus0 \o -%R.
set r2 := (r%:num/2)%:pos.
set r4 := (r%:num/4)%:pos.
have ler4 : r4%:num <= r%:num. 
  by rewrite /r4/= ler_pdivrMr // ler_pMr // lerDl.
have ler42 : r4%:num <= r2%:num. 
  by rewrite /r4/r2/= ler_pdivrMr// -mulrA ler_pMr // ler_pdivlMl // mulr1 lerD // lerDl.
have adplus : t0 < t0 + dplus by rewrite ltrDl dplus0.
have cfplus := And33 solplus.
rewrite closure_neitv_oo in cfplus; last by rewrite ltrDl.
have [rpos hropos] := ode.continuous_confined (a:=t0) (b:=t0 + dplus) (u0:=u0) r4 adplus cfplus (And31 solplus).
have amind : -t0 < -t0 + dminus by rewrite ltrDl dminus0.
have cfminus' := And33 solminus.
rewrite closure_neitv_oo in cfminus'; last by rewrite ltrDl.
have cfminus : {within `[t0-dminus, t0], continuous fminus}.
  rewrite /fminus.
  apply: within_continuous_minus.
  apply /continuous_subspaceW/cfminus'.
  apply: subset_itvl.
  rewrite -/dminus.
  by rewrite bnd_simp/= opprD opprK.
have [rneg hrneg] := ode.continuous_confined (a:=-t0) (b:=-t0 + dminus) (u0:=u0) r4 amind cfminus' (And31 solminus).
set dboth := Num.min (b-t0) (Num.min dplus (Num.min dminus (Num.min rneg%:num rpos%:num))).
have dboth0 : 0 < dboth.
   rewrite lt_min; apply /andP;split; last by rewrite lt_min dplus0 //= lt_min dminus0 //=.
   rewrite subr_gt0.
   move : t0ab.
   by rewrite in_itv/= => /andP[].
pose f := patch fplus `[t0 - dboth, t0] fminus.
set uneg := f (t0 - dboth).
have Buneg : closed_ball uneg (r%:num/2) `<=` closed_ball u0 r%:num.
  rewrite /uneg/f patch_in/f/=;last first.
    by rewrite inE/=in_itv/= gerBl lexx ltW. 
  move => /=x xb.
  apply: (closed_ball_split _ xb) => //.
  suff : fminus (t0 - dboth) \in closed_ball u0 (r%:num/4).
    rewrite !inE.
    apply le_closed_ball.
    rewrite ler_pdivrMr//= -mulrA /=ler_peMr//.
    by rewrite ler_pdivlMl //= mulr1 ltW // ler_ltD //= ltrDl.
  apply hrneg.
    rewrite inE/=in_itv/= opprB lerDr ltW //= addrC lerD //.
    by rewrite /dboth ge_min; do 3 (apply /orP; right; rewrite ge_min);apply /orP;left.
have f01intersect : fminus t0 = fplus t0.
  by rewrite /fminus/= (And31 solminus) (And31 solplus).
have fa : f t0 = u0.
   rewrite /f patch_in /fminus /=. 
   apply solminus.
   by rewrite inE/=in_itv/= lexx gerBl ltW.
set B' := closed_ball uneg (r2%:num).
have lip2' : {in `[t0-dboth,t0+dboth], forall x, k.-lipschitz_B' (phi x)}.
  move => /= t tab [x1 x2] [Bx1 Bx2].
  apply lip2 => //.
  move : tab.
  rewrite mem_setE.
  apply: subset_itv; rewrite bnd_simp.
  rewrite lerBrDl -lerBrDr.
  by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
  rewrite -lerBrDl.
  by rewrite !ge_min lexx.
  by split;apply Buneg.
have contf_minus :   {within `[t0 - dboth, t0], continuous fminus}.
  apply /continuous_subspaceW/cfminus.
  apply: subset_itvr.
  by rewrite bnd_simp /= lerD //= lerNr opprK 3!ge_min lexx !orbT. 
have contf_plus :   {within `[t0, t0+dboth], continuous fplus}.
  apply /continuous_subspaceW/cfplus.
  apply: subset_itvl.
  by rewrite bnd_simp /= lerD //= 3!ge_min lexx !orbT.
have contf :   {within `[t0 - dboth, (t0 + dboth)%E], continuous f}.
  apply : within_continuous_patch => //.
  by rewrite gtrBl.
  by rewrite ltrDl.
have r42 : r4%:num = (r2%:num / 2).
  rewrite /r4/r2/=.
  rewrite -mulrA.
  apply congr2 => //.
  by rewrite -invfM -natrM.
have fc : {in `[t0-dboth, (t0 + dboth)], forall t : R,  closed_ball (fminus (t0 - dboth)) r2%:num (f t)}.
  move => t tad.
  rewrite /f/=/patch/=.
   have : (closed_ball (fminus (t0-dboth)) (r4%:num)) u0.
     suff:  (fminus (t0-dboth)) \in closed_ball u0 (r4%:num). 
       by rewrite inE/= !closed_ballE/closed_ball_/= // distrC .
     apply: hrneg.
     rewrite !inE/=!in_itv/= lerNr lerNl opprD !opprK gerBl ltW //= lerB //.
     by rewrite !ge_min lexx !orbT.
  rewrite r42.
  move => c1.
  case : ifP => ht.
  - have  : (fminus t) \in closed_ball u0 (r4%:num).
     apply: hrneg.
     move : ht.
     rewrite !inE/=!in_itv/= lerNr lerNl opprD !opprK => /andP[h1 ->//=].
     apply: (le_trans _ h1).
     rewrite lerB //.
     by rewrite !ge_min lexx !orbT.
   rewrite inE.
   rewrite !r42.
   move => c2.
   apply: (closed_ball_split _ c2) =>//.
  - have  : (fplus t) \in closed_ball u0 (r4%:num).
     have ht' : t \in `[t0, t0 + dboth].
       have := tad.
       rewrite !inE /=!in_itv/= => /andP[h1 ->]; apply /andP; split => //.
       have [hat | hat] := lerP t0 t => //.
       rewrite -ht.
       by rewrite inE/=in_itv/= h1//= ltW.
     apply: hropos.
       move : ht'.
       rewrite !inE/= !in_itv/= => /andP[-> h1//=].
       apply: (le_trans h1).
       rewrite lerD //.
       by rewrite !ge_min lexx !orbT.
     rewrite inE.
     rewrite !r42.
     move => c2.
     apply: (closed_ball_split _ c2) =>//.
exists f, dboth.
split => //.
suff  h: is_sol_oo phi (f (t0-dboth)) (t0-dboth) (t0+dboth) f.
  by split => //;apply:(And32 h).  
have kn0 : k != 0 by apply lt0r_neq0.
apply /(integral_sol_iff_sol (r := r2) kn0) => //.
  by rewrite ler_ltD // gtrN.
  move => t tab /= x Bx.
  apply: lip2.
  move : tab.
  apply: subset_itv; rewrite bnd_simp.
  rewrite lerBrDl -lerBrDr.
  by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
  rewrite -lerBrDl.
  by rewrite !ge_min lexx.
  split.
  apply Buneg.
  by apply: Bx.1.
  apply Buneg.
  by apply: Bx.2.
  move => t tab.
  apply /continuous_subspaceW/cont1.
  apply: subset_itv; rewrite bnd_simp.
  rewrite lerBrDl -lerBrDr.
  by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
  rewrite -lerBrDl.
  by rewrite !ge_min lexx.
  apply mem_set.
  apply Buneg.
  by apply set_mem.
  move => _ [t tp] <-.
  rewrite {1}/f patch_in;last first.
    by rewrite inE/=in_itv/= lexx //= gerBl ltW.
  by apply fc; rewrite inE.
apply solution_extends => //.
- by rewrite gtrBl.
- apply : (within_continuous_lipschitz _ kn0 (u0 := u0) (r:=r)).
    exact: contf_minus.
    move => x bx.
    apply lip2.
    move : bx.
    apply: subset_itv; rewrite bnd_simp.
    rewrite lerBrDl -lerBrDr.
    by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
    move : t0ab.
    by rewrite in_itv/=  => /andP[_ /ltW//].
    move => t tab.
    apply /continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp.
    rewrite lerBrDl -lerBrDr.
    by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
    move : t0ab.
    by rewrite in_itv/=  => /andP[_ /ltW//].
    exact: tab.
    move => _ [/= t' tp] <-.
    apply (le_closed_ball (e1:=r4%:num)) => //.
    suff : (fminus t') \in closed_ball u0 r4%:num by rewrite inE.
    apply hrneg.
    move : tp.
    rewrite in_itv/=inE/=in_itv/= lerNl opprK => /andP[h0 ->//=].
    rewrite lerNl opprD opprK //=.
    apply: (le_trans _ h0).
    rewrite lerB //.
    by rewrite !ge_min lexx !orbT.
- apply : (within_continuous_lipschitz _ kn0 (u0 := u0) (r:=r)).
    exact: contf_plus.
    move => x bx.
    apply lip2.
    move : bx.
    apply: subset_itv; rewrite bnd_simp.
    move : t0ab.
    by rewrite in_itv/=  => /andP[/ltW//].
    rewrite -lerBrDl.
    by rewrite ge_min lexx. 
    move => t tab.
    apply /continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp.
    move : t0ab.
    by rewrite in_itv/=  => /andP[/ltW//].
    rewrite -lerBrDl.
    by rewrite ge_min lexx. 
    exact: tab.
    move => _ [/= t' tp] <-.
    apply (le_closed_ball (e1:=r4%:num)) => //.
    suff : (fplus t') \in closed_ball u0 r4%:num by rewrite inE.
    apply hropos.
    move : tp.
    rewrite in_itv/=inE/=in_itv/= => /andP[-> h0 //=].
    apply: (le_trans h0).
    rewrite lerD //=.
    by rewrite !ge_min lexx !orbT.
- apply /(integral_sol_iff_sol (r:=r2) kn0).
  + by rewrite gtrBl.
  + move => x bx.
    apply lip2'.
    move : bx.
    rewrite !inE.
    apply: subset_itvl; rewrite bnd_simp.
    by rewrite lerDl ltW.
  + move => t tab.
    apply /continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp.
    rewrite lerBrDl -lerBrDr.
    by rewrite !ge_min opprK (addrC t0) lexx !orbT.
    move : t0ab.
    by rewrite in_itv/=  => /andP[_ /ltW//].
    apply mem_set.
    apply Buneg.
    by apply set_mem.
  + by [].
  + move => _ [t tp] <-.
    rewrite {1}/f patch_in;last first.
      by rewrite inE/=in_itv/= lexx //= gerBl ltW.
    have tin : t \in `[t0-dboth, t0+dboth].
      move : tp.
      rewrite !inE.
      apply: subset_itv; rewrite bnd_simp //.
      by rewrite lerDl ltW.
    have := fc _ tin.
    rewrite {1}/f patch_in; last by rewrite inE.
    apply.
    split.
      * by rewrite /f patch_in; last rewrite inE/=in_itv/= lexx //= gerBl ltW.
      *  move => t tad.
         case : (And32 solminus (-t)).
           move : tad.
           rewrite -/dminus /=!in_itv/= ltrNr ltrNl opprD !opprK => /andP[h1 ->//=].
           apply: (le_lt_trans _ h1).
           by rewrite lerB// 3!ge_min lexx !orbT.
         move => h1 h2.
         have hd : (derivable fminus t 1).
           rewrite /fminus/=.
           apply /derivable1_diffP.
           apply /differentiable_comp => //.
           apply /derivable1_diffP.
           apply h1.
         split=>//.
         rewrite /fminus/=.
         apply /rowP => i /=.
         rewrite derive1E/=.
         rewrite !derive_mx //= !mxE.
         rewrite -derive1E/=.
       have -> : (fun t0 : R => fminus0 (- t0) ord0 i) = ((fun t => fminus0 t ord0 i) \o -%R).
         by apply funext.
      rewrite  derive1_comp//=.
      rewrite !derive1N//=derive1_id/=.
      move /rowP : h2.
      move /(_ i).
      rewrite !derive1E /=!derive_mx.
      rewrite /=!mxE => ->.
      by rewrite mulrN1 !opprK.
      apply h1.
      by move /derivable_mxP: h1.
      * by rewrite closure_neitv_oo; last rewrite gtrBl.
- apply /(integral_sol_iff_sol (r:=r2) kn0).
  + by rewrite ltrDl.
  +  move=>x bx.
     rewrite /fminus/=.
     rewrite (And31 solminus).
     move => [x1 x2] [ Bx1 Bx2].
     apply: lip2.
     move : bx.
     rewrite !inE.
     apply: subset_itv; rewrite bnd_simp.
     move : t0ab.
     by rewrite in_itv/= => /andP[/ltW//].
     rewrite -lerBrDl.
     by rewrite ge_min lexx.
     split => /=.
     rewrite /B.
     apply: (le_closed_ball _ Bx1). 
     by rewrite ler_pdivrMr // ler_pMr // lerDr.
     apply: (le_closed_ball _ Bx2). 
     by rewrite ler_pdivrMr // ler_pMr // lerDr.
  + move => t tab.
    apply /continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp.
    move : t0ab.
    by rewrite in_itv/=  => /andP[ /ltW//].
    rewrite -lerBrDl.
    by rewrite ge_min lexx.
    rewrite /B.
    suff -> : u0 = fminus t0.
      apply mem_set.
      apply set_mem in tab.
      apply: le_closed_ball tab.
      by rewrite /r2/= ler_piMr// invf_le1 // ler1n.
    rewrite -fa.
    rewrite /f.
    rewrite patch_in//.
    rewrite inE/= bound_itvE.
    by rewrite lerBlDl lerDr ltW.
  + by [].
  + move => _ [t tp] <-.
    rewrite /fminus /=(And31 solminus).
    apply : (le_closed_ball ler42).
    suff :  fplus t \in closed_ball u0 r4%:num by rewrite inE.
    apply hropos.
    move : tp.
    rewrite !inE/=!in_itv/= => /andP[-> h0]//=.
    apply (le_trans h0).
    rewrite lerD //=.
    by rewrite !ge_min lexx !orbT.
    rewrite /fminus /=(And31 solminus).
    split.
    apply solplus.
    move => t tad.
    apply solplus.
    move : tad.
    rewrite !in_itv/= => /andP[-> h0]//=.
    apply (lt_le_trans h0).
    by rewrite lerD //= !ge_min lexx !orbT. 
    apply /continuous_subspaceW/cfplus.
    rewrite closure_neitv_oo;last by rewrite ltrDl.
    apply subset_itvl.
    rewrite bnd_simp /=.
    by rewrite lerD //= !ge_min lexx !orbT. 
Qed.
End picard_symmetric.

Definition locally_lipschitz {R : realType} n (U := 'rV[R]_n) (phi : U -> U) :=
 forall x, exists r k : {posnum R}, k%:num.-lipschitz_(closed_ball x r%:num) phi.
