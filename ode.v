From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval.
From mathcomp Require Import poly archimedean generic_quotient ring_quotient.
From mathcomp Require Import interval_inference.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import contra functions constructive_ereal reals.
From mathcomp Require Import topology prodnormedzmodule tvs normedtype.
From mathcomp Require Import landau ereal sequences derive numfun measure.
From mathcomp Require Import realfun measurable_realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc.
Require Import tilt_mathcomp tilt_analysis ode_common ode_contseg.

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
(* Technical constants needed for the proof:                                  *)
(*   sup_phi == sup {phi t u0 | t \in [a, b]}                                 *)
(*   safe_dist == min (b - a, r / (k * r + sup_phi), rho / k)                 *)
(*                upper-bound of delta                                        *)
(*                The dependence of safe_dist on the initial state u0 comes   *)
(*                from sup_phi in the second term.                            *)
(*   @img_cball R n f a b k u0 r k0 rho ==                                    *)
(*     set of functions of type `C([a, b] U) s.t.                             *)
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

Import MeasurableR.

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
apply Rintegral_itvob_itvcb.
apply (@integrableS _ _ _ lebesgue_measure `[a, b] `]c, b] (EFin \o (fun x => F x ord0 i))) =>//.
exact: subset_itvScc.
Qed.

End rowRintegral_itv_split.

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

Section measurable_fun_bigmaxr.
Import MeasurableR.

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

End measurable_fun_bigmaxr.

Section v.
Import MeasurableR.

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
    exact: sumr_ge0.
  exact: vec_norm_le_sum.
- have -> : EFin \o (fun x => \sum_(i < n) `|F x ord0 i|) =
            fun x => (\sum_(i < n) `|F x ord0 i|%:E).
    by apply/funext => x; rewrite sumEFin.
  apply: integrable_sum => //= i _.
  exact: integrable_norm.
Qed.

End v.

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
    rewrite [X in {within X, continuous _}](_ : _ = [set a]).
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
    by apply/funext=> r0; rewrite mxE rowRintegralE.
  by apply: cvgD; [exact: cvg_cst|exact: abf].
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

HB.lock Definition sup_phi {R : realType} {n : nat}
  (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R) (u0 : U)
  : R := sup [set `|phi t u0| | t in `[a, b]].
Canonical sup_phi_unlockable := Unlockable sup_phi.unlock.

Section sup_phi.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R).
Variables (u0 : U).

Lemma sup_phi_ge0 : 0 <= sup_phi phi a b u0.
Proof. by rewrite unlock/= /sup_phi sup_ge0//= => x [y _ <-]. Qed.

Variable r : {posnum R}.
Let B := closed_ball u0 r%:num : set U.
Hypothesis cont1 : {in B, forall y : U, {within `[a, b], continuous phi^~ y}}.

Lemma normr_phi_sup_phi x : x \in `[a, b]%R ->
  `|phi x u0| <= sup_phi phi a b u0.
Proof.
move=> xab.
rewrite unlock/= ub_le_sup//.
  have [M [Mb1 Mb2]] : bounded_set [set `|phi t u0| | t in `[a,b]].
    apply/compact_bounded/continuous_compact; last exact: segment_compact.
    have [ab|] := ltP a b; last first.
      rewrite le_eqVlt => /predU1P[ab|ab].
        rewrite [X in {within X, continuous _}](_ : _ = [set a]).
          by rewrite ab set_itv1.
        exact: continuous_subspace1.
      rewrite set_itv_ge// ?bnd_simp -?ltNge//.
      exact: continuous_subspace0.
    apply: within_continuous_comp_norm.
    by apply cont1;rewrite inE; exact: closed_ballxx.
  exists (M + 1) => _ [x0 x0ab] <- /=.
  rewrite -normr_id.
  apply Mb2.
    by rewrite ltrDl.
  by exists x0.
by exists x.
Qed.

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
rewrite unlock/=.
have [cd|dc] := leP c d.
  apply: sup_le => //.
  - move=> _/= [r rcd <-].
    rewrite /down/=.
    exists `|phi r u0|; split => //.
    by exists r => //; exact: cdab.
  - exists `|phi c u0| => /=.
    by exists c => //; rewrite bound_itvE.
  - split.
      exists `|phi a u0| => /=.
      by exists a => //; rewrite bound_itvE.
    have : {within `[a, b], continuous fun t : R => `|phi t u0|}.
      exact: within_continuous_comp_norm.
    move=> /(EVT_max ab)[e eab Hmax].
    exists (`|phi e u0|) => x/= [r rab <-].
    exact: Hmax.
rewrite set_itv_ge ?bnd_simp/= -?ltNge// image_set0 sup0.
by apply: sup_ge0 => x/= [y _ <-//].
Qed.

End sup_phi_lemmas.

HB.lock Definition safe_dist {R : realType} {n : nat}
  (U := 'rV[R]_n) (phi : R -> U -> U) (a b k : R) (u0 : U)
  (r rho : {posnum R})
  := Num.min (b - a)
                       (Num.min (r%:num / (k * r%:num + sup_phi phi a b u0))
                                (rho%:num / k)).
Canonical safe_dist_unlockable := Unlockable safe_dist.unlock.

Section safe_dist.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Variable rho : {posnum R}. (* rho < 1 *)

Local Notation safe_dist := (safe_dist phi a b k u0 r rho).
Local Notation sup_phi := (sup_phi phi a b u0).

Lemma safe_dist_gt0 : 0 < safe_dist.
Proof.
rewrite unlock/= lt_min subr_gt0 ab/= lt_min mulr_gt0 ?divr_gt0//.
by rewrite invr_gt0// ltr_wpDr ?sup_phi_ge0// mulr_gt0.
Qed.

Lemma ltDl_safe_dist : a < a + safe_dist.
Proof. by rewrite ltrDl// safe_dist_gt0. Qed.

Lemma leDl_safe_dist : a <= a + safe_dist.
Proof. by rewrite ltW// ltDl_safe_dist. Qed.

Lemma safe_dist_itv : safe_dist <= b - a.
Proof. by rewrite unlock/= ge_min lexx. Qed.

Lemma safe_dist_le_sup_phiV : safe_dist <= r%:num / (k * r%:num + sup_phi).
Proof. by rewrite unlock/= 2!ge_min mulrC lexx/= orbT. Qed.

Lemma safe_dist_le_rho : k * safe_dist <= rho%:num.
Proof. by rewrite mulrC -ler_pdivlMr// unlock/= !ge_min lexx !orbT. Qed.

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
Local Notation C := (`C([a, a + safe_dist] U)).

Definition img_cball : set C :=
  [set f : C | f @` `[a, a + safe_dist] `<=` closed_ball u0 r%:num].

Lemma img_cball_nonempty : img_cball !=set0.
Proof.
exists (pi C (cst u0)) => _ [y aay] <-.
suff -> : fun_of_quot_contSeg (\pi_C%qT (cst u0)) y = u0.
  exact: closed_ballxx.
rewrite /fun_of_quot_contSeg/=.
have /eqmod_on_itv : (repr (\pi_C%qT (cst u0)) = cst u0 %[mod C])%qT.
  by rewrite reprK.
by apply; rewrite inE.
Qed.

Lemma img_cballE : a < b -> img_cball =
  @closed_ball R C (pi C (@cst (subspace `[a, a + safe_dist]) U u0)) r%:num.
Proof.
move=> ab; rewrite closed_ballE//.
apply: eq_set => /= f; apply propext; split => h.
- rewrite -(@reprK _ C f).
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite infty_norm_pi pre_infty_norm_le//.
    by exists a => /=; rewrite bound_itvE lerDl ltW// safe_dist_gt0.
  move=> x adx.
  move /(_ (f x)) : h.
  rewrite closed_ballE//.
  apply.
  exists x => //=.
  by rewrite inE in adx.
- move => _ [x xad] <-.
  rewrite closed_ballE// /closed_ball_ /=.
  have -> : u0 - f x = ((pi C (cst u0)) - f : C) x.
    rewrite -(@reprK _ C f) /GRing.opp /=.
    rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv// inE.
  rewrite -(@reprK _ C f).
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite eval_mod_on_itv; first by rewrite inE.
  move/mem_set in xad.
  apply: (le_trans (pre_infty_norm_ge _ _  _ xad)).
    by exists a => /=; rewrite bound_itvE lerDl ltW// safe_dist_gt0.
  by apply: segment_compact.
(*  (leDl_safe_dist phi ab u0 r k0 rho) *)
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

Local Notation C := (`C([a, a + safe_dist] U)).

Let set_fun_picard_fun (g : C) :
  set_fun `[a, a + safe_dist] [set: U] (picard_fun g).
Proof. by []. Qed.

HB.instance Definition _ (g : C) := @isFun.Build
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

Local Notation C := (`C([a, a + safe_dist] U)).

Let continuous_picard_fun (g : C) :
  {within `[a, a + safe_dist], continuous (picard_fun g)}.
Proof.
have [aaD|] := ltP a (a + safe_dist); last first.
  rewrite le_eqVlt => /predU1P[aaD|aaD].
    rewrite [X in {within X, continuous _}](_ : _ = [set a]).
      by rewrite aaD set_itv1.
    exact: continuous_subspace1.
  rewrite set_itv_ge// ?bnd_simp -?ltNge//.
  exact: continuous_subspace0.
have := @continuous_fun _ _ g.
rewrite /picard_fun; case: pselect => /=.
  move=> z cg.
  apply: (@continuous_fun (subspace `[a, a + safe_dist]) U (picard_fun_subdef phi z)).
  - exact: k0.
  - exact: lip2_safe_dist.
  - exact: cont1_safe_dist.
  - exact: cg.
by move=> _ _; apply: continuous_subspaceT => z; exact: cvg_cst.
Qed.

HB.instance Definition _ (g : C) := @isContinuous.Build _ _
  (picard_fun g : subspace _ -> _) (@continuous_picard_fun g).

Check fun g : C => picard_fun g : continuousSubspaceType _ _.

Check fun g : C => (\pi_C%qT (picard_fun g)) : C.

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

Local Notation C := (`C([a, a + safe_dist] U)).

Import MeasurableR.

Lemma integrable_comp (F : C) y i : y \in `[a, a + safe_dist]%R ->
  F @` `[a, y] `<=` B ->
  mu.-integrable `[a, y] (EFin \o (fun t => phi t (F t) ord0 i)).
Proof.
move=> yaadelta ab0r.
apply: continuous_compact_integrable; first exact: segment_compact.
move: (yaadelta); rewrite in_itv/= => /andP[ay yadelta].
move: i; apply/within_continuous_coord.
apply/(within_continuous_lipschitz _ k0).
- have := @continuous_fun _ _ F.
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

Local Notation C := (`C([a, a + safe_dist] U)).

Definition picard (f : C) : C := \pi_C%qT (picard_fun f).

Local Notation img_cball := (@img_cball R n phi a b k u0 r rho).
Local Notation sup_phi := (@sup_phi R n phi a b u0).

Import MeasurableR.

Let set_fun_picard : set_fun img_cball img_cball picard.
Proof.
move=> F.
rewrite /img_cball/= => invariant _/= [y yaaDelta <-].
rewrite /picard.
apply closed_ball_vecE => i.
rewrite closed_ball_itv//=.
rewrite in_itv//=.
rewrite [X in _ <= X <= _](_ : _ = (picard_fun F) y ord0 i).
  have /eqmod_on_itv : (repr (\pi_C%qT (picard_fun F)) =
       picard_fun F %[mod C])%qT.
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
    apply: integrable_norm => /=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinN.
    rewrite integrableN //=.
    apply: continuous_compact_integrable => //=; first exact: segment_compact.
    move: i {integrable2}.
    apply/(@within_continuous_coord R n `[a, y] (phi ^~ u0)).
    apply/continuous_subspaceW/(@cont1_safe_dist R n phi a b k u0 r cont1 rho).
      apply: subset_itvl; rewrite bnd_simp.
      by move : yaaDelta;rewrite in_itv /= => /andP[].
    by rewrite /B inE; exact: closed_ballxx.
  apply: integrable_norm => /=.
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  move: i {integrable2}.
  apply/(@within_continuous_coord R n `[a, y] (phi ^~ u0)).
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
        move: j.
        apply/(@within_continuous_coord R n `[a, y] F).
        apply/continuous_subspaceW/continuous_fun.
        apply: subset_itvl; rewrite bnd_simp.
        by move : yaaDelta; rewrite in_itv /= => /andP[].
      apply: measurable_bounded_integrable => //=.
        rewrite lebesgue_measure_itv //=.
        case: ifPn => //=.
        by rewrite -EFinD ltry.
      exact: bounded_cst.
    apply: measurable_bounded_integrable => //=.
      rewrite lebesgue_measure_itv //=.
      case: ifPn => //=.
      by rewrite -EFinD ltry.
    exact: bounded_cst.
  move=> x xay.
  rewrite lerD//.
    have xaaDelta : x \in `[a, a + safe_dist]%R.
      apply: subset_itvl xay; rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
    move/(lip2_safe_dist lip2) : xaaDelta.
    rewrite lipschitz_componentE//; first exact: ltW.
    move/(_ i (F x, u0)) => /=.
    apply.
    split => /=.
      apply: invariant => /=.
      exists x => //.
      apply: subset_itvl xay; rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
    exact: closed_ballxx.
  apply: (@le_trans _ _ `|phi x u0|) => //.
    by rewrite /Num.norm/= mx_normrE /= (le_bigmax _ _ (ord0, i)).
  apply: (@normr_phi_sup_phi _ _ _ _ _ _ r) => //.
  apply: subset_itvl xay; rewrite bnd_simp.
  move : yaaDelta; rewrite in_itv /= => /andP[_].
  move=> /le_trans; apply.
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
        move: j.
        apply/(@within_continuous_coord R n `[a, y] F).
        apply /continuous_subspaceW/continuous_fun.
        apply: subset_itvl; rewrite bnd_simp.
        by move : yaaDelta; rewrite in_itv /= => /andP[].
      apply: measurable_bounded_integrable => //=.
        rewrite lebesgue_measure_itv//=.
        case: ifPn => //=.
          by rewrite -EFinD ltry.
        exact: bounded_cst.
      apply: measurable_bounded_integrable => //=.
        rewrite lebesgue_measure_itv //=.
        case: ifPn => //=.
        by rewrite -EFinD ltry.
      exact: bounded_cst.
    apply: measurable_bounded_integrable => //=.
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
rewrite -ler_pdivlMl//.
  by rewrite ltr_pwDl ?mulr_gt0// sup_phi_ge0.
by rewrite mulrC safe_dist_le_sup_phiV.
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

Notation C := (quot_contSeg a (a + safe_dist) U).
Notation img_cball := (@img_cball _ n phi a b k u0 r rho).

Check @cst (subspace `[a, a + safe_dist]) U u0
  : {fun `[a, a + safe_dist] >-> [set: U]}.

Check @cst (subspace `[a, a + safe_dist]) U u0
  : continuousType (subspace `[a, a + safe_dist]) U.

Local Notation picard := (@picard R n phi a b k u0 r k0 lip2 cont1 rho).

Import MeasurableR.

Lemma is_contraction_picard : is_contraction picard.
Proof.
rewrite /is_contraction /contraction.
rewrite /picard /picard_fun /picard_fun_subdef.
exists (NngNum (ge0 rho)); split => //=.
move=> /= [/= x y] [Vrx Vry].
rewrite /picard/=.
rewrite !piE/=.
rewrite infty_norm_pi/=.
rewrite /pre_infty_norm/=.
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
    move: i.
    apply/within_continuous_coord.
    apply/continuous_subspaceW/continuous_fun.
    apply: subset_itvl; rewrite bnd_simp.
    by move: tNdd; rewrite in_itv /= => /andP[].
  apply continuous_compact_integrable => //=.
    exact: segment_compact.
  move: i.
  apply/within_continuous_coord.
  apply/continuous_subspaceW/continuous_fun.
  apply: subset_itvl; rewrite bnd_simp.
  by move: tNdd; rewrite in_itv /= => /andP[].
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `| x t0 - y t0|))//.
  rewrite (@le_trans _ _ (\int[mu]_(t0 in `[a, t]) (k * `|x t0 - y t0|)))//.
    apply: le_Rintegral => //=.
      apply: integrable_norm => //=.
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
    apply: measurable_bounded_integrable => //=.
      rewrite lebesgue_measure_itv //=.
      case: ifPn => //=.
      by rewrite -EFinD ltry.
    exact: bounded_cst.
  move=> x0 x0at.
  have x0ad : x0 \in `[a, a + safe_dist]%R.
    apply: subset_itvl x0at; rewrite bnd_simp.
    by move: tNdd; rewrite in_itv/= => /andP[].
  have -> : x x0 - y x0 = (x - y : C) x0.
    apply (@eqmod_on_itv _ _ _ _ (repr x - repr y)) => //.
    by rewrite Quotient.pi_add Quotient.pi_opp !reprK.
  rewrite pre_infty_norm_ge//.
  by exists a => /=; rewrite bound_itvE// lerDl ltW// safe_dist_gt0.
  exact: segment_compact.
  by rewrite inE.
(* leDl_safe_dist.*)
rewrite (@le_trans _ _ (k * `|x - y| * (t - a)))//.
  rewrite -mulrA ler_wpM2l//; first exact: ltW.
  rewrite Rintegral_cst// ler_pM//.
  move: tNdd; rewrite in_itv/= => /andP[+ _].
  rewrite le_eqVlt => /predU1P[->|].
    by rewrite set_itv1 lebesgue_measure_set1 subrr lexx.
  by rewrite /= (lebesgue_measure_itv `[a,t]%R) /= lte_fin => ->.
rewrite [leLHS]mulrAC ler_wpM2r//.
move: tNdd; rewrite in_itv/= => /andP[Ndt].
rewrite -lerBlDl -[in X in X -> _](@ler_pM2l _ k)// => /le_trans; apply.
by rewrite safe_dist_le_rho.
Qed.

End is_contraction_picard.

Definition row_vector {R : realType} (n : nat) := 'rV[R]_n.

HB.instance Definition _ {R : realType} (n : nat) := Complete.on (@row_vector R n).
HB.instance Definition _ {R : realType} (n : nat) := NormedModule.on (@row_vector R n).
(*HB.instance Definition _ {R : realType} (n : nat) := CompleteNormedModule.on (@row_vector R n).*)

Section is_sol.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variable phi : R -> U -> U.

Definition sol_is_deriv_cbnd (a : R) (b : itv_bound R) (f : R -> U) :=
  {in Interval (BLeft a) b, forall t, derivable f t 1 /\ f^`() t = phi t (f t)}.

Definition sol_is_deriv_co a b := sol_is_deriv_cbnd a (BLeft b).

Definition sol_is_deriv_cy a := sol_is_deriv_cbnd a +oo%O.

Lemma sol_is_deriv_cy_co a b : sol_is_deriv_cy a `<=`
  sol_is_deriv_cbnd a (BLeft b).
Proof.
move=> f H t tab.
apply H.
exact: subset_itvl tab.
Qed.

Definition sol_is_deriv_obnd (a : R) (b : itv_bound R) (f : R -> U) :=
  {in Interval (BRight a) b,
    forall t, derivable f t 1 /\ f^`() t = phi t (f t)}.

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

Lemma is_sol_oo_subset {R : realType} {n : nat} phi (u0 : 'rV[R]_n)
    (a b c d : R) sol : c < d -> a <= c -> d <= b ->
  is_sol_oo phi u0 a b sol -> is_sol_oo phi (sol c) c d sol.
Proof.
move=> cd ac bd isSol; split.
- by [].
- move=> x xcd; apply isSol.
  by apply: subset_itv xcd; rewrite bnd_simp.
- have [_ _ +] := isSol.
  exact/continuous_subspaceW/closureS/subset_itv.
Qed.

Section is_integral_sol.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U).

(*Todo: is this a good way to define it with the extra sol a = u0G?  *)
Definition is_integral_sol := sol a = u0 /\
  forall t, t \in `[a, b]%R -> sol t = sol a + (\vint[mu]_(s in `[a, t]) phi s (sol s))%R.

End is_integral_sol.

Section integral_ode.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 u0' : U) (a b : R) (sol : R -> U) (k : R) (r : {posnum R}).
Hypothesis k0 : k != 0.
Hypothesis ab : a < b.

Let B := closed_ball u0' r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis cont_sol : {within `[a, b], continuous sol}.
Hypothesis sol_bound : sol @` `[a, b] `<=` B.

Lemma picard_iterator_within_continuous i :
  {within `[a, b], continuous (fun x => phi x (sol x) ord0 i)}.
Proof.
move: i.
apply/within_continuous_coord.
exact: (@within_continuous_lipschitz _ _ phi a b u0' r sol _ _ k0).
Qed.

Lemma integral_sol_iff_sol1 :
  is_sol_oo phi u0 a b sol -> is_integral_sol phi u0 a b sol.
Proof.
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
- by rewrite -EFinB subrKC.
Unshelve. all: by end_near. Qed.

End integral_ode.

Section integral_ode2.
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

Lemma picard_iterator_continuous i t : t \in `]a, b[%R ->
  {for t, continuous (fun x => phi x (sol x) ord0 i)}.
Proof.
move/within_continuous_continuous; apply => //.
exact: (picard_iterator_within_continuous k0 lip2 cont1).
Qed.

Import MeasurableR.

Lemma picard_iterator_integrable i : mu.-integrable `[a, b]
  (EFin \o (fun x : R => phi x (sol x) ord0 i)).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
exact: (picard_iterator_within_continuous k0 lip2 cont1).
Qed.

Lemma integral_sol_iff_sol :
  is_integral_sol phi u0 a b sol -> is_sol_oo phi u0 a b sol.
Proof.
move => [hinit h].
split; first by []; last first.
  apply: continuous_subspaceW cont_sol.
  exact: itv_closure (* TODO: why not equality? *).
move=> t tab.
move: (tab); rewrite in_itv /= => /andP[ta tb].
have -> : sol^`() t  = (fun x => sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))^`() t.
  apply/eq_on_itv_deriv/tab => x xt01; apply h.
  exact: subset_itv_oo_cc xt01.
suff hi : forall i, derivable (fun x => sol x ord0 i) t 1 /\
  (fun x : R => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))%R)^`() t ord0 i =
    phi t (sol t) ord0 i.
  split.
    apply /derivable_mxP => i j.
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
rewrite derive1E deriveD /=.
  exact: derivable_cst.
  exact: Hderivable.
split.
   apply: (near_eq_derivable
       (f := (fun x => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s)) ord0 j))) => /=.
     near=> t'.
     rewrite (h t')//= in_itv/=.
     apply/andP; split.
     - by apply: ltW; near: t'; exact: lt_nbhsr.
     - by apply: ltW; near: t'; exact: lt_nbhsl.
  have -> : (fun x => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))%R ord0 j) =
            cst (sol a ord0 j) +
            (fun x => (\vint[mu]_(s in `[a, x]) (phi s (sol s))) ord0 j).
    by apply funext => x; rewrite mxE.
  apply: derivableD.
    exact: derivable_cst.
  move/derivable_mxP : Hderivable.
  by apply.
rewrite -!derive1E derive1_cst add0r -H2 !derive1E derive_mx//= mxE/=.
congr ('D_1 _ t).
by apply/funext => t'; rewrite mxE.
Unshelve. all: by end_near. Qed.

End integral_ode2.

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
  by rewrite in_itv/= lexx leDl_safe_dist.
by rewrite /picard_fun /= picard_fun_init//; exact: img_cball_picard_fix.
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

Theorem picard_fix_unique (picard_fix' : V) : img_cball picard_fix' ->
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

Import MeasurableR.

Lemma cauchy_lipschitz_quot_ex : picard_fix a = u0 /\
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
    + exact: continuous_fun.
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
  rewrite derive1E deriveD /=.
    exact: derivable_cst.
    exact: Hderivable.
  rewrite -!derive1E derive1_cst add0r -H2 !derive1E derive_mx// mxE/=.
  congr ('D_1 _ t).
  by apply/funext => t0; rewrite mxE.
rewrite /picard /picard_fun.
move: t tad.
apply: eq_on_itv_deriv => t tad /=.
rewrite -(@picard_funE _ _ _ a b k _ r k0' lip2 cont1 rho)//=.
  exact: img_cball_picard_fix.
rewrite eval_mod_on_itv// inE; apply: subset_itv_oo_cc.
by rewrite inE in tad.
Qed.

Lemma cauchy_lipschitz_in_cball (t : R) : `[a, a + safe_dist] t ->
  closed_ball u0 r%:num (picard_fix t).
Proof. by move=> taad; apply: img_cball_picard_fix => /=; exists t. Qed.

End picard.

Section picard_extension.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Context (phi : R -> U -> U) (a b c : R) (u0 : U) (sol1 : R -> U) (sol2 : R -> U).
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous (fun x => phi x (sol1 x))}.
Hypothesis cont2 : {within `[b, c], continuous (fun x => phi x (sol2 x))}.
Hypothesis matchb : sol1 b = sol2 b.

Lemma is_integral_sol_patch :
  is_integral_sol phi u0 a b sol1 ->
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
  congr (_ + _)%R.
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
    phi s (if (s \in `[a, b])%classic then sol1 s else sol2 s))%R; last first.
  by under eq_rowRintegral do rewrite mem_setE.
rewrite (rowRintegral_itv_split (c := b) (F := (fun x => phi x (patch sol2 `[a, b] sol1 x)))).
- by rewrite ltW //=; move : tbc; rewrite in_itv/= => /andP [-> _].
- move=> i.
  have cont' : {within `[a, t], continuous (fun x => phi x (patch sol2 `[a, b] sol1 x) ord0 i)}.
    have -> : `[a, t] = `[a, b] `|` `[b, t].
      rewrite (@itv_bndbnd_setU _ _ _ (BRight b))// ?bnd_simp//=.
        exact: ltW.
        by rewrite (itvP tbc).
      apply/seteqP; split => x.
        move=> []; [by left|right].
        exact: subset_itv_oc_cc b0.
      move=> []; [by left|].
      rewrite -(setU1itv false) ?bnd_simp//.
        by rewrite (itvP tbc).
      case; [|by right].
      move=> ->; left => /=.
      by rewrite bound_itvE ltW.
    apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b t)).
      move : i.
      apply /within_continuous_coord.
      have eq1 : {in `[a, b], (fun x0 => phi x0 (sol1 x0)) =1
                              (fun x0 => phi x0 (patch sol2 `[a, b] sol1 x0))}.
        move => x0 x0ab.
        by rewrite /patch x0ab.
      apply: (subspace_eq_continuous eq1).
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
    apply: (@continuous_subspaceW _ _ _ `[b, c]).
      by apply: subset_itvl; rewrite bnd_simp (itvP tbc).
    exact: (subspace_eq_continuous eq2).
  apply: continuous_compact_integrable => //.
  exact: segment_compact.
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
  rewrite p1a p0s; first by rewrite in_itv/= ltW/=.
  rewrite p0a.
  congr (u0 + _)%R.
  rewrite /patch.
  by apply eq_rowRintegral => /= x ->.
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

Let r2 := (r%:num/2)%:pos.
Let B2 := closed_ball u0 r2%:num.

Let ler2 : r2%:num <= r%:num.
Proof. by rewrite /r2/= ler_pdivrMr // ler_pMr // lerDl. Qed.

Let lip2' :  {in `[a, b]%R, forall x, k.-lipschitz_B2 (phi x)}.
Proof.
move => x abx /= y By.
apply: lip2.
by move : abx; rewrite !inE/=; apply subset_itvr.
split.
by apply /le_closed_ball/By.1.
by apply /le_closed_ball/By.2.
Qed.

Let cont1':  {in B2, forall y, {within `[a, b], continuous phi ^~ y}}.
Proof.
move => /= x Bx.
apply /continuous_subspaceW/cont1.
by [].
apply mem_set.
apply set_mem in Bx.
by apply /le_closed_ball/Bx.
Qed.

(* Let rho : {posnum R} := (2^-1)%:pos. *)

(* Let rho1 : rho%:num < 1. *)
(* Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed. *)

Local Notation safe_dist := (safe_dist phi a b k u0 r2 rho).

Definition cauchy_lipschitz_f :
    continuousSubspaceType `[a, a + safe_dist] [set: 'rV[R]_n] :=
  repr (picard_fix ab k0 lip2' cont1' rho1).

Lemma is_sol_cauchy_lipschitz_f :
  is_sol_oo phi u0 a (a + safe_dist) cauchy_lipschitz_f.
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
- exact: continuous_fun.
- apply (subset_trans (B:=B2)).
  by move => _ [t tad] <-;apply: cauchy_lipschitz_in_cball.
  by apply le_closed_ball.
- exact: cauchy_lipschitz_integral_version.
Qed.

Lemma solution_stays_in_ball2 :
  {in `[a, a + safe_dist]%R,
    forall t, closed_ball u0 r2%:num (cauchy_lipschitz_f t)}.
Proof. by move=> t; move => /cauchy_lipschitz_in_cball; exact. Qed.

Lemma solution_stays_in_ball :
  {in `[a, a + safe_dist]%R,
    forall t, closed_ball u0 r%:num (cauchy_lipschitz_f t)}.
Proof.
move => t ta.
apply /le_closed_ball/solution_stays_in_ball2=>//.
Qed.

Lemma solution_continuous :
  {within `[a, a + safe_dist], continuous cauchy_lipschitz_f}.
Proof. exact: continuous_fun. Qed.

Let f := cauchy_lipschitz_f.

Theorem cauchy_lipschitz_ex : is_sol_oo phi u0 a (a + safe_dist) f.
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
- exact: continuous_fun.
- apply (subset_trans (B:=B2)).
  by move => _ [t tad] <-;apply: cauchy_lipschitz_in_cball.
  by apply le_closed_ball.
- exact: cauchy_lipschitz_integral_version.
Qed.


Local Notation V := (@ContSeg_quot.quot_contSeg R a (a + safe_dist) U).

Lemma cauchy_lipschitz_unique_restr f' :
  {within `[a, a + safe_dist], continuous f'} ->
  {in `[a, a + safe_dist]%R, forall t, closed_ball u0 r2%:num (f' t)}  ->
  is_sol_oo phi u0 a (a + safe_dist) f' ->
  {in `[a, a + safe_dist]%R, f =1 f'}.
Proof.
move => cont bnd.
move/(@integral_sol_iff_sol1 _ _ _ u0 (*u0*) u0(*u0'*) _ _ _ _ r k0') => []//.
- exact: ltDl_safe_dist.
- move=> t td.
  apply: lip2.
  by apply: subset_itvl td; rewrite bnd_simp -lerBrDl safe_dist_itv.
- move=> /= x xB.
  apply/continuous_subspaceW/cont1 => //.
  by apply: subset_itvl => //=; rewrite bnd_simp -lerBrDl safe_dist_itv.
  apply (subset_trans (B:=B2)).
  by move => _ [t tad] <-;apply: bnd.
  by apply le_closed_ball.
move=> f'au0 h1 t tab.
have fc : contseg `[a, a + safe_dist] f' by exact: mem_set.
have pieq : \pi_V%qT f = \pi_V%qT (contseg_Sub fc).
  rewrite reprK.
  apply: picard_fix_unique.
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

(* TODO: move *)
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
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R})
          (f : R -> U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis cf : {within `[a, b], continuous f}.
Hypothesis sol1 : is_sol_oo phi u0 a b f.
Let rho_max : {posnum R} := (2^-1)%:pos.

Let r2 := (r%:num/2)%:pos.
Let dmax rho := safe_dist phi a b k u0 r2 rho.
Let fc := cauchy_lipschitz_f ab k0 lip2 cont1.

Lemma initial_solution_unique f' : {within `[a, b], continuous f'} ->
  is_sol_oo phi u0 a b f' ->
  exists D : {posnum R}, {in `[a, a + D%:num]%R, f =1 f'} /\
    {in `[a, a + D%:num]%R, forall t, closed_ball u0 (r2%:num) (f t)}.
Proof.
move => cf' sol2.
suff [rho [D [Hrho [Db P1 P2]]]] : exists rho D : {posnum R},
    exists (Hrho : rho%:num < 1),
    [/\ D%:num <= dmax rho,
        {in `[a, a + D%:num]%R, f =1 fc Hrho } &
        {in `[a, a + D%:num]%R, f' =1 fc Hrho} ].
  exists D; split => t tab; first by rewrite P1// P2.
  rewrite P1//.
  apply: solution_stays_in_ball2.
  by move: tab; rewrite !inE; apply: subset_itvl; rewrite bnd_simp lerD2l.
have [d1 D1] := continuous_confined r2 ab cf (And31 sol1).
have [d2 D2] := continuous_confined r2 ab cf' (And31 sol2).
have [rho [drho1 drho2]] : exists rho, dmax rho <= (Num.min d1%:num d2%:num) /\ rho%:num < 1.
  rewrite /dmax.
  have posk : 0 < Num.min rho_max%:num (Num.min (k * rho_max%:num) (k * (Num.min d1%:num d2%:num))).
    by rewrite lt_min/= invr_gt0// ltr0n/= lt_min divr_gt0//= mulr_gt0.
  exists (PosNum posk); split => //=.
    rewrite unlock/=.
    rewrite !ge_min/= minA; apply/orP; right.
    rewrite !minr_pMl//=; [by rewrite ltW// invr_gt0..|].
    do 2 rewrite ge_min; apply/orP; right.
    apply/orP; right.
    by rewrite mulrAC divff ?mul1r// gt_eqF//.
  by rewrite gt_min; apply/orP; left; rewrite invf_lt1// ltr1n.
have drho_pos : 0 < dmax rho by exact: safe_dist_gt0.
exists rho, (PosNum drho_pos), drho2; split => //.
- move => t tad.
  apply/esym; apply: cauchy_lipschitz_unique_restr.
  - apply/continuous_subspaceW/cf => //.
    apply: subset_itvl => //=.
    by rewrite bnd_simp -lerBrDl;apply safe_dist_itv.
  - move=> t0 t0ad.
    suff : f t0 \in closed_ball u0 r2%:num by rewrite inE.
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
apply/esym; apply : cauchy_lipschitz_unique_restr.
- apply/continuous_subspaceW/cf' => //.
  by apply: subset_itvl => /=; rewrite bnd_simp -lerBrDl;apply safe_dist_itv.
- move=> t0 t0ad.
  suff : f' t0 \in closed_ball u0 r2%:num by rewrite inE.
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

(* only for autonomous, used for tilt *)
Definition locally_lipschitz {R : realType} n (U := 'rV[R]_n) (phi : U -> U) :=
 forall x, exists r k : {posnum R}, k%:num.-lipschitz_(closed_ball x r%:num) phi.

Section loc_lip_uniqueness.
Context {R : realType} {n : nat} (a b : R) (r0 : {posnum R}).
Notation U := 'rV[R]_n.
Variable phi : R -> U -> U.
Hypothesis ab : a < b.
Variable (u0 : U).

Let B := closed_ball u0 r0%:num.

Variables (f : R -> U) (f' : R -> U).
Hypothesis sol1 : is_sol_oo phi u0 a b f.
Hypothesis sol2 : is_sol_oo phi u0 a b f'.
Hypothesis sol1B : forall t, a <= t -> t < b -> B (f t).
Hypothesis phi_local_conds :forall t, a <= t -> t < b -> exists r k : {posnum R},
     forall t', a <= t' <= b -> (k%:num.-lipschitz_(closed_ball (f t) r%:num) (phi t') /\ forall y, closed_ball (f t) r%:num y -> {within `[a, b], continuous phi ^~ y}).

Local Lemma cauchy_lipschitz_unique_right_extension t : a <= t < b ->  f' t = f t ->
  exists Delta : {posnum R}, {in `[t, t + Delta%:num]%R, f =1 f'}.
Proof.
move=> /andP[ta tb] eq.
have [r [k L]] := phi_local_conds ta tb.
have taab : `[t, b] `<=` `[a, b].
  by move=> ?/=; apply: subset_itvr; rewrite bnd_simp.
have cf0 : {within `[t, b], continuous f}.
  have := And33 sol1.
  rewrite closure_itvoo//; exact: continuous_subspaceW.
have cf'0 : {within `[t, b], continuous f'}.
  have := And33 sol2.
  by rewrite closure_itvoo//; exact: continuous_subspaceW.
have sol10 : is_sol_oo phi (f t) t  b f.
  split; [by []| | by rewrite closure_itvoo].
  move=> t0 tab.
  apply sol1.
  by apply: subset_itvr tab; rewrite bnd_simp.
have sol20 : is_sol_oo phi (f t) t b f'.
  split; [by []| | by rewrite closure_itvoo].
  move=> t0 tab.
  apply sol2.
  by apply: subset_itvr tab; rewrite bnd_simp.
have lip20 : {in `[t, b]%R, forall x, k%:num.-lipschitz_(closed_ball (f t) r%:num) (phi x)}.
  move => t0 tab; apply L.
  by rewrite (le_trans ta)/= (itvP tab).
have cont1' : {in closed_ball (f t) r%:num,
  forall y : 'rV_n, {within `[t, b], continuous  phi^~ y}}.
    move => y ytb.
    have : {within `[a,b], continuous phi^~ y}.
      have [| _ +] := L t.
        by rewrite ta ltW.
     apply.
     exact/set_mem.
   exact/continuous_subspaceW/subset_itvr.
have k0 : 0 < k%:num by [].
have [D [P1 P2]] := initial_solution_unique tb k0 lip20 cont1' cf0 sol10 cf'0 sol20.
by exists D.
Qed.

Let in1_eq1 : {in `[a, a]%R, f =1 f'}.
Proof.
move=> t; rewrite in_itv/= -eq_le => /eqP <-.
by rewrite (And31 sol1) (And31 sol2).
Qed.

Lemma locally_cauchy_lipschitz_unique : {in `[a, b]%R, f =1 f'}.
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
      apply/within_continuous_comp_norm/within_continuousB.
      - by have := And33 sol1; rewrite (closure_itvoo ab).
      - by have := And33 sol2; rewrite (closure_itvoo ab).
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
    apply: (@cvgr_gt _ (x^'-) _ _ g (g x)) => //.
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
  by near: y; exact: lt_le_nbhsr.
have supE : E (sup E).
  by rewrite {1}(closure_id E).1//; apply: closure_sup => //; apply hP.
have sup_itv : a <= sup E by rewrite sup_upper_bound.
have supeq : f' (sup E) = f (sup E).
  apply/esym; apply supE.
  by rewrite  in_itv/= lexx sup_itv.
have [h|h] := leP b (sup E).
  apply: (mon _ supE) => //.
  by rewrite in_itv/= (ltW ab).
have [|Delta Hdelta] := cauchy_lipschitz_unique_right_extension _ supeq; first by apply/andP.
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

End loc_lip_uniqueness.

Section uniqueness.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Let r2 := (r%:num/2)%:pos.
Variable rho : {posnum R}. (* rho < 1 *)
Hypothesis rho1 : (rho%:num < 1).
Local Notation safe_dist := (safe_dist phi a b k u0 r2 rho).
Let f := cauchy_lipschitz_f ab k0 lip2 cont1 rho1.

Lemma closed_ball_split (x1 x2 y : U) q : 0 < q ->
  closed_ball x1 (q / 2) y -> closed_ball x2 (q / 2) x1 -> closed_ball x2 q y.
Proof.
move => hq.
have hq2 : 0 < q / 2 by rewrite divr_gt0.
rewrite !closed_ballE// /closed_ball_ /= => h1 h2.
rewrite -(subrKA x1 x2).
by rewrite (le_trans (ler_normD _ _))// (splitr q) lerD.
Qed.
Theorem cauchy_lipschitz_unique f' :
  is_sol_oo phi u0 a (a + safe_dist) f' ->
  {in `[a, a + safe_dist]%R, f =1 f'}.
Proof.
move =>  sol1.
have cont1' :  forall y , B y -> {within `[a, a + safe_dist], continuous phi^~ y}.
  move => y By .
  apply /continuous_subspaceW/cont1.
  apply subset_itvl.
  rewrite bnd_simp -lerBrDl; apply safe_dist_itv.
  by apply mem_set.
apply: (locally_cauchy_lipschitz_unique _ _ (u0 := u0) sol1 ).
- exact: ltDl_safe_dist.
- exact: is_sol_cauchy_lipschitz_f.
move => t tad tbd.
have [r' rp] : exists (r' : {posnum R}), closed_ball (f t) r'%:num `<=` closed_ball u0 r%:num.
  exists r2.
  move => x x0.
  have sb: closed_ball u0 (r%:num / 2) (f t).
  apply solution_stays_in_ball2=> //.
  by rewrite in_itv/= tad//= ltW.
  apply/closed_ball_split/sb => //.
exists r',(PosNum k0).
move => t' /andP[at' bt'].
split.
move => /=[x1 x2] [Bx1 Bx2].
apply lip2.
rewrite in_itv/= at' //=.
apply (le_trans bt').
rewrite -lerBrDl.
apply safe_dist_itv.
split => /=;by apply rp.
move => y By.
have h : y \in B.
  apply mem_set.
  by apply: rp.
have := cont1 h.
apply/continuous_subspaceW.
apply: subset_itvl.
by rewrite bnd_simp -lerBrDl; apply safe_dist_itv.
Qed.

End uniqueness.

Section cauchy_lipschitz_symmetric.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (k : R) (u0 : U) (r : {posnum R})  (a b : R).
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Definition phi_ (t : R) x := phi x.

Definition is_sol_sym u0 t0 d (f : R -> U):=
   f t0 = u0 /\ sol_is_deriv_oo phi (t0 - d) (t0 + d) f.

Let rho : {posnum R} := 2^-1%:pos.

Let rho1 : rho%:num < 1.
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Lemma patch_in {X : Type} (f g : R -> X)  S x : x \in S -> patch f S g x = g x.
Proof.
  move => xs.
  rewrite /patch.
  by rewrite xs.
Qed.

Let r2 := (r%:num / 2)%:pos.
Let r4 := (r%:num / 4)%:pos.

Let ler4 : r4%:num <= r%:num.
Proof. by rewrite /r4/= ler_pdivrMr // ler_pMr // lerDl. Qed.
Let ler42 : r4%:num <= r2%:num.
Proof. by rewrite /r4/r2/= ler_pdivrMr// -mulrA ler_pMr // ler_pdivlMl // mulr1 lerD // lerDl. Qed.

Let B4 := closed_ball u0 r4%:num.

Let phi_lip2 t0: t0 \in `[a,b]%R ->  {in `[t0, b]%R, forall x, k.-lipschitz_B4 (phi x)}.
Proof.
move => tab x abx /= y By.
apply: lip2.
move : abx; rewrite !inE/=; apply subset_itvr.
by move : tab; rewrite in_itv/= bnd_simp => /andP[-> _].
split.
by apply /le_closed_ball/By.1.
by apply /le_closed_ball/By.2.
Qed.

Let phi_cont1 t0 : t0 \in `[a,b]%R -> {in B4, forall y, {within `[t0, b], continuous phi ^~ y}}.
Proof.
move => /= tab x Bx.
apply /continuous_subspaceW/cont1 => //.
apply: subset_itvr.
by move : tab; rewrite in_itv/= bnd_simp => /andP[-> _].
apply mem_set.
apply set_mem in Bx.
by apply /le_closed_ball/Bx.
Qed.

Let phi_lip2' t0 : t0 \in `[a,b]%R ->  {in `[-t0, -a]%R, forall x, k.-lipschitz_B4 (-phi (-x))}.
Proof.
move => t0ab  /= y ab x B12.
rewrite /= -normrN opprD !opprK.
have B12' : (B `*` B) x.
  split.
  by apply /le_closed_ball/B12.1.
  by apply /le_closed_ball/B12.2.
apply: (lip2 _  B12').
move : ab.
rewrite !in_itv/= lerNl lerNr => /andP[h1 ->]//=.
apply (le_trans h1).
move : t0ab.
by rewrite in_itv/= => /andP[].
Qed.

Local Lemma phi_cont1' t0 : t0 \in `[a,b]%R ->
  {in B4, forall y, {within `[-t0, -a], continuous -(fun t => phi (-t) y)}}.
Proof.
move => t0ab /= y By.
move => t.
apply: continuousN.
have /within_continuous_compN : {within `[-(-a), - (-t0)], continuous phi^~ y}.
  rewrite !opprK.
  apply /continuous_subspaceW/cont1 => //.
  apply : subset_itvl.
  by move: t0ab; rewrite /=in_itv/= bnd_simp => /andP[].
apply set_mem in By.
apply mem_set.
by apply : le_closed_ball By.
apply.
Qed.

Let dplus t0 := safe_dist phi t0 b k u0 (r4%:num/2)%:pos rho.
Let dminus t0 := safe_dist (fun t x => - phi (-t) x) (-t0) (-a) k u0 (r4%:num/2)%:pos rho.
Let dboth t0 := Num.min (b - t0) (Num.min (dplus t0) (dminus t0)).

Section cauchy_lipschitz_sym.
Variable t0 : R.
Hypothesis t0ab : t0 \in `]a, b[%R.

Let amin1 : - t0 < - a. Proof. by rewrite ltrN2 (itvP t0ab). Qed.

Let t0ab' : t0 \in `[a, b]%R. Proof. by exact: subset_itv_oo_cc. Qed.

Let fminus0 := @cauchy_lipschitz_f R n (fun t x => - phi (- t) x) (- t0)
  _ k u0 r4 amin1 k0 (phi_lip2' t0ab') (phi_cont1' t0ab') rho rho1.

Let fminus := fminus0 \o -%R.

Let t0b : t0 < b. Proof. by rewrite (itvP t0ab). Qed.

Let fplus := @cauchy_lipschitz_f R n phi t0
  _ k u0 r4 t0b k0 (phi_lip2 t0ab') (phi_cont1 t0ab') rho rho1.


Definition safe_dist_sym := (dboth t0).
Definition cauchy_lipschitz_f_sym := patch fplus `[t0 - safe_dist_sym, t0] fminus.

Lemma cauchy_lipschitz_f_sym_left t :
  t \in `[t0 - safe_dist_sym, t0]%R ->
  cauchy_lipschitz_f_sym t = fminus t.
Proof.
move=> ht.
by rewrite /cauchy_lipschitz_f_sym patch_in // inE.
Qed.

Lemma cauchy_lipschitz_sym_oo :  is_sol_oo phi
    (cauchy_lipschitz_f_sym (t0 - safe_dist_sym))
    (t0 - safe_dist_sym)
    (t0 + safe_dist_sym)
    cauchy_lipschitz_f_sym.
Proof.
have solplus :=
  cauchy_lipschitz_ex t0b k0 (phi_lip2 t0ab') (phi_cont1 t0ab') rho1.
have cplus := solution_stays_in_ball.
have dminus0 : 0 < dminus t0 by exact: safe_dist_gt0.
have solminus :=
  cauchy_lipschitz_ex amin1 k0 (phi_lip2' t0ab') (phi_cont1' t0ab') rho1.
have cminus := solution_stays_in_ball.
have adplus : t0 < t0 + dplus t0 by rewrite ltrDl safe_dist_gt0.
have cfplus := And33 solplus.
rewrite closure_itvoo in cfplus; first by rewrite ltrDl safe_dist_gt0.
have amind : -t0 < -t0 + dminus t0 by rewrite ltrDl dminus0.
have cfminus' := And33 solminus.
rewrite closure_itvoo in cfminus'; first by rewrite ltrDl.
have cfminus : {within `[t0-dminus t0, t0], continuous fminus}.
  rewrite /fminus.
  apply: within_continuous_compN.
  apply/continuous_subspaceW/cfminus'.
  apply: subset_itvl; rewrite bnd_simp -/dminus.
  by rewrite opprD opprK.
have dboth0 : 0 < dboth t0.
  rewrite lt_min; apply /andP;split; last first.
    by rewrite lt_min safe_dist_gt0 //= lt_min dminus0.
  by rewrite subr_gt0 (itvP t0ab).
set uneg := cauchy_lipschitz_f_sym (t0 - dboth t0).
have Buneg : closed_ball uneg (r%:num / 2) `<=` closed_ball u0 r%:num.
  rewrite /uneg/cauchy_lipschitz_f_sym patch_in /cauchy_lipschitz_f_sym/=.
    by rewrite inE/=in_itv/= gerBl lexx ltW.
  move=> /= x xb.
  apply: (closed_ball_split _ xb) => //.
  suff : fminus (t0 - dboth t0) \in closed_ball u0 (r%:num/4).
    rewrite !inE.
    apply le_closed_ball.
    rewrite ler_wpM2l// lef_pV2 ?posrE//.
    by rewrite (natrD _ 2 2) lerDl ler0n.
  apply/mem_set/cminus.
  rewrite in_itv/= opprB lerDr ltW //= addrC lerD//.
  by rewrite /dboth /dplus !ge_min lexx !orbT.
have f01intersect : fminus t0 = fplus t0.
  by rewrite /fminus/= (And31 solminus) (And31 solplus).
have fa : cauchy_lipschitz_f_sym t0 = u0.
  rewrite /cauchy_lipschitz_f_sym patch_in /fminus /=.
    by rewrite inE/= in_itv/= lexx gerBl ltW.
  by apply solminus.
set B' := closed_ball uneg (r2%:num).
have lip2' : {in `[t0 - dboth t0 ,t0 + dboth t0], forall x, k.-lipschitz_B' (phi x)}.
  move => /= t tab [x1 x2] [Bx1 Bx2].
  apply lip2 => //.
    move: tab.
    rewrite mem_setE.
    apply: subset_itv; rewrite bnd_simp.
      rewrite lerBrDl -lerBrDr /dboth /dplus /dminus/= unlock/=.
      by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
    rewrite -lerBrDl.
    by rewrite !ge_min lexx.
  by split; exact: Buneg.
have contf_minus : {within `[t0 - dboth t0, t0], continuous fminus}.
  apply /continuous_subspaceW/cfminus.
  apply: subset_itvr; rewrite bnd_simp.
  by rewrite lerD2l lerN2 /dboth /dminus !ge_min lexx !orbT.
have contf_plus :   {within `[t0, t0+dboth t0], continuous fplus}.
  apply /continuous_subspaceW/cfplus.
  apply: subset_itvl; rewrite bnd_simp/=.
  by rewrite lerD2l /dboth 2!ge_min lexx !orbT.
have contf :   {within `[t0 - dboth t0, t0 + dboth t0], continuous cauchy_lipschitz_f_sym}.
  apply : within_continuous_patch => //.
  by rewrite gtrBl.
  by rewrite ltrDl.
have r42 : r4%:num  = (r2%:num / 2).
  rewrite /r4/r2/=.
  rewrite -mulrA.
  apply congr2 => //.
  by rewrite -invfM -natrM.
have fc : {in `[t0-dboth t0, (t0 + dboth t0)],
    forall t : R,  closed_ball (fminus (t0 - dboth t0)) r2%:num (cauchy_lipschitz_f_sym t)}.
  move => t tad.
  rewrite /cauchy_lipschitz_f_sym/= /patch/=.
   have : (closed_ball (fminus (t0 - dboth t0)) (r4%:num)) u0.
     suff: (fminus (t0 - dboth t0)) \in closed_ball u0 (r4%:num).
       by rewrite inE/= !closed_ballE/closed_ball_/= // distrC .
     apply/mem_set/cminus.
     rewrite !in_itv/= lerNr lerNl opprD !opprK gerBl ltW//= lerB//.
     by rewrite /dboth !ge_min lexx !orbT.
  rewrite r42 => c1.
  case : ifP => ht.
  - have : fminus t \in closed_ball u0 r4%:num.
    apply/mem_set/cminus.
    move: ht.
    rewrite inE/=!in_itv/= lerNr lerNl opprD !opprK => /andP[h1 ->//=].
    by rewrite (le_trans _ h1)// lerD2l lerN2 /safe_dist_sym !ge_min lexx !orbT.
    rewrite inE.
    rewrite !r42.
    move => c2.
    by apply: (closed_ball_split _ c2) =>//.
  - have : fplus t \in closed_ball u0 (r2%:num / 2).
    rewrite -r42.
     have ht' : t \in `[t0, t0 + dboth t0].
       have := tad.
       rewrite !inE /=!in_itv/= => /andP[h1 ->]; apply /andP; split => //.
       have [hat | hat] := lerP t0 t => //.
       rewrite -ht.
       by rewrite inE/=in_itv/= h1//= ltW.
       apply mem_set;apply cplus.
       move : ht'.
       rewrite inE/= !in_itv/= => /andP[-> h1//=].
       apply: (le_trans h1).
       by rewrite lerD // /dboth /dplus 2!ge_min lexx !orbT.
    rewrite inE.
     move => c2.
    by apply: (closed_ball_split _ c2).
split; last by rewrite closure_itvoo // /safe_dist_sym // ler_ltD // gtrN.
by [].
suff h : is_sol_oo phi (cauchy_lipschitz_f_sym (t0-dboth t0))
  (t0 - dboth t0) (t0 + dboth t0) cauchy_lipschitz_f_sym by apply (And32 h).
have kn0 : k != 0 by apply lt0r_neq0.
have at0t0 : a <= t0 - dboth t0.
  rewrite lerBrDl -lerBrDr.
  by rewrite /dboth /dminus /dplus !unlock/= !ge_min opprK (addrC t0) lexx /= !orbT.
have t0t0b : t0 + dboth t0 <= b.
  rewrite -lerBrDl.
  by rewrite !ge_min lexx.
apply/(integral_sol_iff_sol (r := r2) kn0) => /=.
- by rewrite ler_ltD // gtrN.
- move => t tab /= x Bx.
  apply: lip2.
    by apply: subset_itv tab; rewrite bnd_simp.
  split.
    by apply: Buneg; exact: Bx.1.
  by apply: Buneg; exact: Bx.2.
- move=> t tab.
  apply/continuous_subspaceW/cont1.
    by apply: subset_itv; rewrite bnd_simp.
  by apply/mem_set/Buneg/set_mem.
- by [].
- move => _ [t tp] <-.
  rewrite {1}/cauchy_lipschitz_f_sym patch_in.
    by rewrite inE/=in_itv/= lexx //= gerBl ltW.
  by apply fc; rewrite inE.
apply: is_integral_sol_patch => //.
- by rewrite gtrBl.
- apply: (within_continuous_lipschitz _ kn0 (u0 := u0) (r:=r)).
  + exact: contf_minus.
  + move=> x bx.
    apply: lip2.
      apply: subset_itv bx; rewrite bnd_simp//.
      by rewrite (le_trans _ t0t0b)// lerDl ltW.
    move => t tab.
    apply/continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp//.
    by rewrite (itvP t0ab).
    exact: tab.
  + move => _ [/= t' tp] <-.
    apply: (le_closed_ball (e1:=r4%:num)) => //.
    suff : (fminus t') \in closed_ball u0 r4%:num by rewrite inE.
    apply mem_set; apply cminus.
    move : tp.
    rewrite !in_itv/=lerNl opprK => /andP[h0 ->//=].
    rewrite lerNl opprD opprK //=.
    apply: (le_trans _ h0).
    rewrite lerD2l lerN2 /dboth /dplus /dminus.
    by rewrite !ge_min lexx !orbT.
  + apply : (within_continuous_lipschitz _ kn0 (u0 := u0) (r:=r)).
    exact: contf_plus.
  + move=> x bx.
    apply: lip2.
    apply: subset_itv bx; rewrite bnd_simp.
    by rewrite (itvP t0ab).
    by rewrite -lerBrDl ge_min lexx.
    move => t tab.
    apply/continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp//.
    by rewrite (itvP t0ab).
    exact: tab.
    move => _ [/= t' tp] <-.
    apply (le_closed_ball (e1:=r4%:num)) => //.
    suff : (fplus t') \in closed_ball u0 r4%:num by rewrite inE.
    apply/mem_set; apply cplus.
    apply: subset_itvl tp; rewrite bnd_simp lerD2l.
    by rewrite /dboth /dplus 2!ge_min lexx !orbT.
- apply /(integral_sol_iff_sol1 (r:=r2) kn0).
  + by rewrite gtrBl.
  + move => x bx.
    apply: lip2'.
    rewrite inE.
    apply: subset_itvl bx; rewrite bnd_simp.
    by rewrite lerDl ltW.
  + move => t tab.
    apply/continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp//.
    by rewrite (itvP t0ab).
    exact/mem_set/Buneg/set_mem.
  + by [].
  + move => _ [t tp] <-.
    rewrite /uneg.
    rewrite {1}/cauchy_lipschitz_f_sym patch_in.
      by rewrite inE/=in_itv/= lexx //= gerBl ltW.
    have tin : t \in `[t0 - dboth t0, t0 + dboth t0].
      move : tp.
      rewrite !inE.
      apply: subset_itv; rewrite bnd_simp//.
      by rewrite lerDl// ltW.
    have := fc _ tin.
    rewrite {1}/cauchy_lipschitz_f_sym patch_in; first by rewrite inE.
    apply.
    split.
      * by rewrite /cauchy_lipschitz_f_sym patch_in; first rewrite inE/=in_itv/= lexx //= gerBl ltW.
      *  move => t tad.
         case : (And32 solminus (-t)).
           move : tad.
           rewrite -/dminus /=!in_itv/= ltrNr ltrNl opprD !opprK => /andP[h1 ->//=].
           apply: (le_lt_trans _ h1).
           by rewrite lerD2l lerN2 !ge_min lexx !orbT.
         move => h1 h2.
         have hd : derivable fminus t 1.
           rewrite /fminus/=.
           apply/derivable1_diffP.
           apply/differentiable_comp => //.
           apply/derivable1_diffP.
           by apply h1.
         split=>//.
         rewrite /fminus/=.
         apply /rowP => i /=.
         rewrite derive1E/=.
         rewrite !derive_mx //= !mxE.
         rewrite -derive1E/=.
       have -> : (fun t0 : R => fminus0 (- t0) ord0 i) = ((fun t => fminus0 t ord0 i) \o -%R).
         by apply funext.
      rewrite derive1_comp/=.
        by [].
        by move /derivable_mxP: h1.
      rewrite !derive1N//=derive1_id/=.
      move /rowP : h2.
      move /(_ i).
      rewrite !derive1E /=!derive_mx.
      by apply: h1.
      rewrite /=!mxE => ->.
      by rewrite mulrN1 !opprK.
      * by rewrite closure_itvoo; first rewrite gtrBl.
- apply/(integral_sol_iff_sol1 (u0' := fminus t0) (r:=r2) kn0).
  + by rewrite ltrDl.
  + move=> x bx.
    rewrite /fminus/=.
    rewrite (And31 solminus).
    move => [x1 x2] [ Bx1 Bx2].
    apply: lip2.
    move : bx.
    rewrite !inE.
    apply: subset_itv; rewrite bnd_simp.
    by rewrite (itvP t0ab).
    rewrite -lerBrDl.
    by rewrite ge_min lexx.
    split => /=.
    rewrite /B.
    apply: (le_closed_ball _ Bx1).
    by rewrite ler_piMr// invf_le1// ler1n.
    apply: (le_closed_ball _ Bx2).
    by rewrite ler_piMr// invf_le1// ler1n.
  + move => t tab.
    apply /continuous_subspaceW/cont1.
    apply: subset_itv; rewrite bnd_simp.
    by rewrite (itvP t0ab).
    by rewrite -lerBrDl ge_min lexx.
    rewrite /B.
    suff -> : u0 = fminus t0.
      apply mem_set.
      apply set_mem in tab.
      apply: le_closed_ball tab.
      by rewrite /r2/= ler_piMr// invf_le1 // ler1n.
    rewrite -fa.
    rewrite /cauchy_lipschitz_f_sym.
    rewrite patch_in//.
    rewrite inE/= bound_itvE.
    by rewrite lerBlDl lerDr ltW.
  + by [].
  + move => _ [t tp] <-.
    rewrite /fminus /= (And31 solminus).
    apply: (le_closed_ball ler42).
    suff : fplus t \in closed_ball u0 r4%:num by rewrite inE.
      apply/mem_set; apply cplus.
      move/mem_set : tp.
      rewrite inE /=!in_itv/= => /andP[-> //=].
      move/le_trans; apply.
      by rewrite lerD// /dboth /dplus 2!ge_min lexx !orbT.
    rewrite /fminus /=(And31 solminus).
    split; first by apply solplus.
    move=> t tad.
    apply solplus.
    apply: subset_itvl tad; rewrite bnd_simp lerD2l.
    by rewrite /dboth /dplus 2!ge_min lexx !orbT.
    apply/continuous_subspaceW/cfplus.
    rewrite closure_itvoo; first by rewrite ltrDl.
    apply: subset_itvl; rewrite bnd_simp lerD2l.
    by rewrite /dboth /dplus 2!ge_min lexx !orbT.
Qed.

Lemma cauchy_lipschitz_sym_rev_oo :
  is_sol_oo (fun t x => - phi (- t) x) u0
    (- t0) (- t0 + dminus t0) fminus0.
Proof.
exact: cauchy_lipschitz_ex.
Qed.

Lemma cauchy_lipschitz_sym_left t :
  t \in `[t0 - safe_dist_sym, t0]%R ->
  cauchy_lipschitz_f_sym t = fminus0 (- t).
Proof.
move=> ht.
by rewrite cauchy_lipschitz_f_sym_left.
Qed.

Lemma cauchy_lipschitz_sym : is_sol_sym u0 t0 safe_dist_sym cauchy_lipschitz_f_sym.
Proof.
split; last by apply cauchy_lipschitz_sym_oo.
have dminus0 : 0 < dminus t0 by exact: safe_dist_gt0.
have solminus :=
  cauchy_lipschitz_ex amin1 k0 (phi_lip2' t0ab') (phi_cont1' t0ab') rho1.
have dboth0 : 0 < dboth t0.
  rewrite lt_min; apply /andP;split; last first.
    by rewrite lt_min safe_dist_gt0 //= lt_min dminus0.
  by rewrite subr_gt0 (itvP t0ab).
rewrite /cauchy_lipschitz_f_sym patch_in /fminus /=.
  by rewrite inE/= in_itv/= lexx gerBl ltW.
by apply solminus.
Qed.

End cauchy_lipschitz_sym.

End cauchy_lipschitz_symmetric.
Section integral_sol_between.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Context (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U).

Import MeasurableR.

Hypothesis int_phi_sol : forall i,
  mu.-integrable `[a, b]
    (EFin \o (fun x : R => phi x (sol x) ord0 i)).

Lemma integral_sol_between :
  is_integral_sol phi u0 a b sol ->
  forall s t,
    s \in `[a, b]%R ->
    t \in `[s, b]%R ->
    sol t =
      sol s + \vint[mu]_(x in `[s, t]) phi x (sol x).
Proof.
move=> [sola Hsol] s t sab tsb.
have as' : a <= s by move: sab; rewrite in_itv /= => /andP[].
have st : s <= t by move: tsb; rewrite in_itv /= => /andP[].
have tb : t <= b by move: tsb; rewrite in_itv /= => /andP[].

have tab : t \in `[a, b]%R.
  by rewrite in_itv /= (le_trans as' st) tb.

have ast : a <= s <= t by rewrite as' st.

have int_phi_sol_at i :
  mu.-integrable `[a, t]
    (EFin \o (fun x : R => phi x (sol x) ord0 i)).
   apply: (@integrableS _ _ _ mu `[a, b] `[a, t]) => //. 
  by apply: subset_itvl. 

rewrite (Hsol t tab) (Hsol s sab).
rewrite (rowRintegral_itv_split
  (F := fun x => phi x (sol x)) ast int_phi_sol_at).
by rewrite addrA.
Qed.

End integral_sol_between.
