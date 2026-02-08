(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import archimedean generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
Require Import common contfun.

(**md**************************************************************************)
(* # Proof of the Cauchy-Lipschitz theorem                                    *)
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
(*   delta_max == min (b - a, r / (k * r + sup_phi), rho / k)                 *)
(*                upper-bound of delta                                        *)
(*                The dependence of delta_max on the initial state u0 comes   *)
(*                from sup_phi in the second term.                            *)
(*   @img_cball R n f a b k ab u0 r k0 rho ==                                 *)
(*     set of functions of type (quot_continuousFunType (leDl_delta_max ...)) *)
(*     s.t. f @` `[a, a + delta_max] `<=` closed_ball u0 r                    *)
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

(* NB: PR to MathComp-Analysis in progress *)
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
Hypothesis k0 : 0 < k.

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
Hypothesis ab : a <= b.
Variables (u0 : U) (r : {posnum R}).
Let B : set U := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k > 0.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Variable g : R -> U.
Variable cg : {within `[a, b], continuous g}.
Hypothesis gabB : g @` `[a, b] `<=` B.

Lemma within_continuous_picard_fun_subdef :
  {within `[a, b], continuous (picard_fun_subdef phi gabB)}.
Proof.
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
apply: parameterized_integral_continuous => //.
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
move: i; apply/within_continuous_coord.
exact: (within_continuous_lipschitz cg k0 lip2 cont1).
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
    (k : R) (lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)})
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

(* PR 1802 om porgress *)
Lemma EVT_max_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
    A !=set0 -> compact A -> {within A, continuous f} ->
  exists2 c, c \in A & forall t, t \in A -> f t <= f c.
Admitted.

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

Section delta_max.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Variable rho : {posnum R}. (* rho < 1 *)

Local Notation sup_phi := (sup_phi phi a b u0).

Definition delta_max := Num.min (b - a)
                       (Num.min (r%:num / (k * r%:num + sup_phi))
                                (rho%:num / k)).

Lemma delta_max_gt0 : 0 < delta_max.
Proof.
rewrite lt_min subr_gt0 ab/= lt_min mulr_gt0 ?divr_gt0//.
by rewrite invr_gt0// ltr_wpDr ?sup_phi_ge0// mulr_gt0.
Qed.

Lemma ltDl_delta_max : a < a + delta_max.
Proof. by rewrite ltrDl delta_max_gt0. Qed.

Lemma leDl_delta_max : a <= a + delta_max.
Proof. by rewrite ltW// ltDl_delta_max. Qed.

Lemma delta_max_itv : delta_max <= b - a.
Proof. by rewrite /delta_max ge_min lexx. Qed.

End delta_max.

Section image_in_closed_ball.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Variable rho : {posnum R}. (* rho < 1 *)

Import Cont_on_seg_quot.

Local Notation delta_max := (@delta_max R n phi a b k u0 r rho).

Local Notation V :=
  (quot_continuousFunType (@leDl_delta_max _ _ phi a b k ab u0 r k0 rho)).

Definition img_cball : set V :=
  [set f : V | f @` `[a, a + delta_max] `<=` closed_ball u0 r%:num].

Lemma img_cball_nonempty : img_cball !=set0.
Proof.
exists (pi V (cst u0)) => _ [y aay] <-.
suff -> : quot_continuousFunType_to_fun (\pi_(V)%qT (cst u0)) y = u0.
  exact: closed_ballxx.
rewrite /quot_continuousFunType_to_fun/=.
have /eqmod_on_itv : (repr (\pi_(V)%qT (cst u0)) = cst u0 %[mod V])%qT.
  by rewrite reprK.
by apply; rewrite inE.
Qed.

Lemma img_cballE : img_cball =
  @closed_ball R V (pi V (@cst (subspace `[a, a + delta_max]) U u0)) r%:num.
Proof.
rewrite closed_ballE// /img_cball.
apply eq_set => /= f'; apply propext; split => h.
- rewrite -(@reprK _ V f').
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite norm_piE.
  apply: infty_norm0_le => /=.
    exact: leDl_delta_max.
  move=> x adx.
  move /(_ (f' x)) : h.
  rewrite closed_ballE//.
  apply.
  exists x => //.
  by rewrite inE in adx.
- move => _ [x xad] <-.
  rewrite closed_ballE// /closed_ball_ /=.
  have -> : u0 - f' x = ((pi V (cst u0)) - f' : V) x.
    rewrite -(@reprK _ V f') /GRing.opp /=.
    rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv// inE.
  rewrite -(@reprK _ V f').
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite eval_mod_on_itv;last by rewrite inE.
  rewrite -inE in xad.
  apply: (le_trans (infty_norm0_ge (leDl_delta_max phi ab u0 r k0 rho) _ xad)).
  rewrite -(norm_piE (leDl_delta_max phi ab u0 r k0 rho)).
  by rewrite Quotient.pi_add Quotient.pi_opp reprK.
Qed.

Lemma closed_img_cball : closed img_cball.
Proof. by rewrite img_cballE; exact: closed_ball_closed. Qed.

End image_in_closed_ball.

Section picard_fun_isFun.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}. (* rho < 1 *)

Local Notation delta_max := (delta_max phi a b k u0 r rho).

Lemma lip2_delta_max : {in `[a, a + delta_max]%R, forall x, k.-lipschitz_B (phi x)}.
Proof.
(* TODO: generalize to the subset relation *)
move/in_switch : lip2 => lip2'.
apply/in_switch.
apply: lipschitzW lip2'.
apply: subset_itvl.
by rewrite bnd_simp -lerBrDl; exact: delta_max_itv.
Qed.

Lemma cont1_delta_max :
  {in B, forall y, {within `[a, a + delta_max], continuous phi ^~ y}}.
Proof.
move=> /= x xB.
apply: continuous_subspaceW; last exact: cont1.
apply: subset_itvl.
by rewrite bnd_simp -lerBrDl; exact: delta_max_itv.
Qed.

Local Notation picard_fun :=
  (@picard_fun _ n phi a (a + delta_max) u0 r k lip2_delta_max cont1_delta_max).

Lemma picard_funE g t : g @` `[a, a + delta_max] `<=` B ->
  picard_fun g t = u0 + \vint[mu]_(x in `[a, t]) phi x (g x).
Proof. by rewrite /picard_fun; case: pselect. Qed.

Lemma picard_fun_init g : g @` `[a, a + delta_max] `<=` B ->
  picard_fun g a = u0.
Proof.
by move => h; rewrite picard_funE// set_itv1 rowRintegral_set1 addr0.
Qed.

Import Cont_on_seg_quot.

Local Notation V := (quot_continuousFunType
  (@leDl_delta_max R n phi a b k ab u0 r k0 rho)).

Let set_fun_picard_fun (g : V) :
  set_fun `[a, a + delta_max] [set: U] (picard_fun g).
Proof. by []. Qed.

HB.instance Definition _ (g : V) := @isFun.Build
  (subspace `[a, a + delta_max]) _
  `[a, a + delta_max] setT (picard_fun g) (set_fun_picard_fun g).

End picard_fun_isFun.

Section picard_fun_isContinuous.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}. (* rho < 1 *)

Local Notation delta_max := (delta_max phi a b k u0 r rho).

Local Notation picard_fun := (@picard_fun _ n phi a (a + delta_max) u0 r k
  (@lip2_delta_max R n phi a b k u0 r lip2 rho)
  (@cont1_delta_max R n phi a b k u0 r cont1 rho)).

Import Cont_on_seg_quot.

Local Notation V := (quot_continuousFunType
  (@leDl_delta_max R n phi a b k ab u0 r k0 rho)).

Let continuous_picard_fun (g : V) :
  {within `[a, a + delta_max], continuous (picard_fun g)}.
Proof.
have := @cts_fun _ _ g.
rewrite /picard_fun; case: pselect => /=.
  move => z cg.
  apply: (@cts_fun (subspace `[a, a + delta_max])).
  + exact: leDl_delta_max.
  + exact: k0.
  + exact : lip2_delta_max.
  + exact : cont1_delta_max.
  + exact : cg.
move=> _ _.
by apply: continuous_subspaceT => z; exact: cvg_cst.
Qed.

HB.instance Definition _ (g : V) := @isContinuous.Build _ _
  (picard_fun g : subspace _ -> _) (@continuous_picard_fun g).

Check fun g : V => picard_fun g : continuousFunType _ _.

Check fun g : V => (\pi_(V)%qT (picard_fun g )) : V.

End picard_fun_isContinuous.

Section integrable_comp.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Local Notation mu := lebesgue_measure.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}. (* rho < 1 *)

Local Notation delta_max := (delta_max phi a b k u0 r rho).

Import Cont_on_seg_quot.

Local Notation V := (quot_continuousFunType (@leDl_delta_max R n phi a b k ab u0 r k0 rho)).

Lemma integrable_comp (F : V) y : y \in `[a, a + delta_max]%R ->
  F @` `[a, y] `<=` B ->
  forall i,
  mu.-integrable `[a, y] (EFin \o (fun t => phi t (F t) ord0 i)).
Proof.
move => yaadelta ab0r i.
apply: continuous_compact_integrable; first exact: segment_compact.
move: (yaadelta); rewrite  in_itv/= => /andP[ay yadelta].
move: i.
apply/within_continuous_coord.
apply/(within_continuous_lipschitz _ k0).
- have := @cts_fun _ _ F.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- apply/in_switch.
  move/in_switch : (@lip2_delta_max R n phi a b k u0 r lip2 rho).
  by apply/lipschitzW/subset_itvl; rewrite bnd_simp.
- rewrite -/B => x xB.
  have := @cont1_delta_max R n phi a b k u0 r cont1 rho _ xB.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- exact: ab0r.
Qed.

End integrable_comp.

Section picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}. (* rho < 1 *)

Local Notation delta_max := (delta_max phi a b k u0 r rho).

Local Notation picard_fun := (@picard_fun _ n phi a (a + delta_max) u0 r k
  (@lip2_delta_max R n phi a b k u0 r lip2 rho)
  (@cont1_delta_max R n phi a b k u0 r cont1 rho)).

Import Cont_on_seg_quot.

Local Notation V := (quot_continuousFunType (@leDl_delta_max R n phi a b k ab u0 r k0 rho)).

Definition picard (x : V) : V := \pi_V%qT (picard_fun x).

Local Notation img_cball := (@img_cball R n phi a b k ab u0 r k0 rho).

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
    apply/continuous_subspaceW/(@cont1_delta_max R n phi a b k u0 r cont1 rho).
      apply: subset_itvl; rewrite bnd_simp.
      by move : yaaDelta;rewrite in_itv /= => /andP[].
    by rewrite /B inE; exact: closed_ballxx.
  apply integrable_norm => /=.
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  apply within_continuous_coord.
  apply/continuous_subspaceW/(@cont1_delta_max R n phi a b k u0 r cont1 rho).
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
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * `|F x   - u0  | + sup_phi)))//.
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
    have xaaDelta : x \in `[a, a + delta_max]%R.
      move: x xay.
      apply: subset_itvl; rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
    move/(lip2_delta_max lip2) : xaaDelta.
    rewrite lipschitz_componentE//.
    move/(_ i (F x, u0)) => /=.
    apply.
    split => /=.
      apply: invariant => /=.
      exists x => //.
      move : xay.
      apply: subset_itvl; rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
    exact: closed_ballxx.
  apply: (@le_trans  _ _ `|phi x u0 |).
    rewrite {2}/Num.norm/= mx_normrE /=.
    by apply: (le_bigmax _ _ (ord0, i)).
  rewrite /sup_phi ub_le_sup//.
    have [M [Mb1 Mb2]] : bounded_set [set `|phi t u0| | t in `[a,b]].
      apply/compact_bounded/continuous_compact; last exact: segment_compact.
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
  by rewrite -lerBrDl delta_max_itv.
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
rewrite (@le_trans _ _ ((k * r%:num + sup_phi) * delta_max))//.
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

Fail Lemma tmp : is_contraction (picard : {fun [set: W] >-> [set: W]}).
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

(* PR: to master *)
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

Import Cont_on_seg_quot.

Notation V := (quot_continuousFunType (@leDl_delta_max R n phi a b k ab u0 r k0 rho)).
Notation img_cball := (@img_cball _ n phi a b k ab u0 r k0 rho).
Notation delta_max := (delta_max phi a b k u0 r rho).

Check @cst (subspace `[a, a + delta_max]) U u0
  : {fun `[a, a + delta_max] >-> [set: U]}.

Check @cst (subspace `[a, a + delta_max]) U u0
  : continuousType (subspace `[a, a + delta_max]) U.

Local Notation picard := (@picard R n phi a b k ab u0 r k0 lip2 cont1 rho).

Lemma is_contraction_picard : is_contraction picard.
Proof.
rewrite /is_contraction /contraction.
rewrite /picard /picard_fun /picard_fun_subdef.
exists (NngNum (ge0 rho)); split => //=.
move=> /= [/= x y] [Vrx Vry].
rewrite /picard/=.
rewrite !piE/=.
rewrite norm_piE/=.
rewrite /infty_norm0/=.
apply: ge_sup => //=.
  set u := _ \o _; exists (u a) => /=; exists a => //.
  by rewrite in_itv/= lexx leDl_delta_max.
move=> _ /= [t tNdd <-].
have tb : t <= b.
  move: tNdd.
  rewrite in_itv/= => /andP[Ndt].
  move=> /le_trans; apply.
  by rewrite -lerBrDl; exact: delta_max_itv.
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
  apply: subset_trans Hg; apply: image_subset.
  apply/subset_itvl; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[].
have integrable2 : mu.-integrable `[a, t] (EFin \o (fun x0 => phi x0 (y x0) ord0 j)).
  apply: integrable_comp => //= => _ [x0 h] <-.
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
  have x0ad : x0 \in `[a, a + delta_max].
    rewrite inE/=.
    apply: subset_itvl x0at; rewrite bnd_simp.
    by move: tNdd; rewrite in_itv/= => /andP[].
  have -> : x x0 - y x0 = (x - y : V) x0.
    apply (@eqmod_on_itv _ _ _ _ (leDl_delta_max phi ab u0 r k0 rho) (repr x - repr y)) => //.
    by rewrite Quotient.pi_add Quotient.pi_opp !reprK.
  by rewrite infty_norm0_ge// leDl_delta_max.
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
rewrite /delta_max !le_min => /andP[_ /andP[_]].
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
Variables (phi : R -> U -> U) (u0 : U) (a : R) (b : itv_bound R) (sol : R -> U).

Definition is_sol_on :=
  sol a = u0 /\
  {in [set` Interval (BRight a)(*open*) b (*(BLeft b)(*open*)*)], forall x, derivable sol x 1 /\ sol^`() x = phi x (sol x)}.

End is_sol.

Section integral_ode.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (u0 : U) (sol : R -> U) (k : R) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Hypothesis ab : a < b.

Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis cont_sol : {within `[a, b], continuous sol}.
Hypothesis sol_bound : sol @` `[a, b] `<=` closed_ball u0 r%:num.

Definition is_integral_sol_on := sol a = u0 /\
  forall t, `[a, b] t -> sol t = sol a + (\vint[mu]_(s in `[a, t]) phi s (sol s))%R.

(* Definition is_integral_sol_on_open   := *)
(*   phi t0 = u0 /\ *)
(*   forall t, `]t0, t1[ t -> *)
(*     phi t = phi t0 + (\vint[mu]_(s in `[t0, t]) f s (phi s))%R. *)

(* Lemma integral_sol_open_closed : is_integral_sol_on_open -> is_integral_sol_on. *)
(* Proof. *)
(*  move => [h0 h1]. *)
(* split => //. *)
(* move => t. *)
(* case: (eqVneq t t0) => [-> _|Ht0]. *)
(*   by rewrite set_itv1 rowRintegral_set1 addr0. *)
(* rewrite /=in_itv/= => /andP [ht0 ht1]. *)
(* apply h1. *)
(* by rewrite /=in_itv/=ht1//= lt_neqAle ht0/= eq_sym Ht0. *)
(* Qed. *)

Lemma picard_iterator_within_continuous i :
  {within `[a, b], continuous (fun x => phi x (sol x) ord0 i)}.
Proof.
move: i.
apply/within_continuous_coord.
exact: (within_continuous_lipschitz _ k0 _ (u0 := u0) (r := r)).
Qed.

Lemma picard_iterator_continuous i t : t \in `]a, b[ ->
  {for t, continuous (fun x => phi x (sol x) ord0 i)}.
Proof.
rewrite inE => /within_continuous_continuous; apply => //.
exact: picard_iterator_within_continuous.
Qed.

(* Lemma Rintegral_itv_open_closed (a b : R) (g : R -> R) : *)
(*   \int[mu]_(x in `]a, b[) g x *)
(*   = \int[mu]_(x in `[a, b]) g x. *)
(* Proof. *)
(* rewrite Rintegral_itv_obnd_cbnd. *)
(* rewrite Rintegral_itv_bndo_bndc //. *)
(* Admitted. *)

Lemma picard_iterator_integrable i : mu.-integrable `[a, b]
  (EFin \o (fun x : R => phi x (sol x) ord0 i)).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
exact: picard_iterator_within_continuous.
Qed.

Lemma integral_sol_iff_sol : is_integral_sol_on <-> is_sol_on phi u0 a (BLeft b) sol.
Proof.
split.
- move => [hinit h]; split => // t tab.
  move: (tab); rewrite inE /= in_itv /= => /andP[ta tb].
  have -> : sol^`() t  = (fun x => sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))^`() t.
    apply/eq_on_itv_deriv/tab => x xt01; apply h.
    rewrite inE in xt01.
    exact: subset_itv_oo_cc.
    (* move : xt01 . *)
    (* Search "itv" "subs". *)
    (* rewrite inE/=!in_itv/= => /andP [xt01 xt01']. *)
    (* by rewrite ltW. *)
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
       rewrite (h t') //= in_itv/=.
       apply/andP; split.
       - by apply: ltW; near: t'; exact: lt_nbhsr.
       - by apply: ltW; near: t'; exact: lt_nbhsl.
    have -> : (fun x => (sol a + \vint[mu]_(s in `[a, x]) phi s (sol s))%E ord0 j) =
              cst (sol a ord0 j) +
              (fun x =>  (\vint[mu]_(s in `[a, x]) (phi s (sol s))) ord0 j).
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
    by have /h[/derivable_mxP] : t' \in `]a, b[ by rewrite inE; exact/subset_itvl/tx'.
  + by move /(continuous_within_itvP _ ab) : cont_soli => [_ + _].
  + have cont_phii' : {within `[a, t], continuous fun x0 : R => sol x0 ord0 i}.
      apply: continuous_subspaceW; last exact: cont_soli.
      exact: subset_itvl.
    by move/(continuous_within_itvP _ ta) : cont_phii' => [_ _ +].
- move=> x xt.
  have /h[? +] : x \in `]a, b[ by rewrite inE; exact/subset_itvl/xt.
  by rewrite !derive1E derive_mx//= => <-; rewrite mxE.
Unshelve. all: by end_near. Qed.

End integral_ode.

Section picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).
Variables (f : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.
Variable rho : {posnum R}.
Hypothesis rho1 : rho%:num < 1.

Import Cont_on_seg_quot.

Check U : completeType.
Check U : completePseudoMetricType R.
Check U : normedModType R.
Check U : completeNormedModType R.

Notation V := (@quot_continuousFunType R U _ _ (leDl_delta_max f ab u0 r k0 rho)).

Check V : completeNormedModType _.

Local Notation img_cball := (@img_cball R n f a b k ab u0 r k0 rho).

Local Notation img_cball_nonempty := (img_cball_nonempty f ab u0 r k0 rho).
Local Notation closed_img_cball := (@closed_img_cball R n f a b k ab u0 r k0 rho).

Definition picard_fix : V :=
  sval (cid2 (@banach_fixed_point R V img_cball
    (@picard R n f a b k ab u0 r k0 lip2 cont1 rho)
    (@is_contraction_picard _ n f a b ab k k0 u0 r lip2 cont1 rho rho1)
    closed_img_cball
    img_cball_nonempty)).

Let picard_fixE :
  picard_fix = (@picard _ n f a b k ab u0 r k0 lip2 cont1 rho) picard_fix.
Proof. by rewrite {}/picard_fix; case: cid2. Qed.

Lemma img_cball_picard_fix : img_cball picard_fix.
Proof.
by apply (svalP (cid2 (@banach_fixed_point R V img_cball _
  (@is_contraction_picard R n f _ _ ab k k0 u0 r lip2 cont1 _ rho1)
  closed_img_cball img_cball_nonempty))).
Qed.

Lemma picard_fix_init : picard_fix a = u0.
Proof.
rewrite picard_fixE eval_mod_on_itv.
  by rewrite /picard_fun /= picard_fun_init//; exact: img_cball_picard_fix.
by rewrite inE/= in_itv/= lexx leDl_delta_max.
Qed.

Local Notation delta_max := (delta_max f a b k u0 r rho).

Lemma picardE g t : img_cball g -> t \in `[a, a + delta_max] ->
  (@picard _ n f a b k ab u0 r k0 lip2 cont1 rho) g t =
  u0 + \vint[mu]_(x in `[a, t]) f x (g x).
Proof.
by move=> Hg taad; rewrite eval_mod_on_itv//; exact: picard_funE.
Qed.

Lemma cauchy_lipschitz_integral_version :
  is_integral_sol_on f a (a + delta_max) u0 picard_fix.
Proof.
split; first exact: picard_fix_init.
move=> t tad.
rewrite {1}picard_fixE eval_mod_on_itv; last by rewrite inE.
rewrite picard_fix_init.
exact: picard_funE img_cball_picard_fix.
Qed.

Theorem cauchy_lipschitz_unique (picard_fix' : V) : img_cball picard_fix' ->
  (forall t, t \in `[a, a + delta_max] ->
  picard_fix' t = u0 + \vint[mu]_(x in `[a, t]) f x (picard_fix' x)) ->
  picard_fix = picard_fix'.
Proof.
move=> imgpicard_fix'_cball h.
apply: (contraction_fixpoint_unique
  (@is_contraction_picard R n f a b ab k k0 u0 r lip2 cont1 rho rho1)
  img_cball_picard_fix imgpicard_fix'_cball) => //=.
rewrite -(reprK picard_fix').
apply/eqquotP.
rewrite /Quotient.equiv/=.
rewrite inE /submod_itv.
apply/funext => x.
rewrite /patch;case: ifPn => [xK | xKnot] => //.
rewrite /quot_continuousFunType_to_fun /=.
rewrite !fctE.
rewrite !reprK.
rewrite picard_funE//=.
have -> : repr picard_fix' x = picard_fix' x by [].
by rewrite h// subrr.
Qed.

Theorem cauchy_lipschitz_existence : picard_fix a = u0 /\
  {in `]a, a + delta_max[, forall x, picard_fix^`() x = f x (picard_fix x)}.
Proof.
split; first exact: picard_fix_init.
move => t tad.
rewrite {1}picard_fixE.
apply/rowP => j.
suff -> : (picard lip2 cont1 picard_fix)^`() t =
          (fun x0 => u0 + \vint[mu]_(x in `[a, x0]) f x (picard_fix x))^`() t.
  move: (tad); rewrite inE /= in_itv /= => /andP[ta tadelta].
  have Fint i : mu.-integrable `[a, a + delta_max]
      (EFin \o (fun x => f x (picard_fix x) ord0 i)).
    apply: integrable_comp => //.
      by rewrite in_itv /= lexx andbT leDl_delta_max.
    exact: img_cball_picard_fix.
  have Fcont i : {for t, continuous (fun x => f x (picard_fix x) ord0 i)}.
    move: tad; rewrite inE.
    apply/within_continuous_continuous => //=.
      exact: ltDl_delta_max.
    clear Fint.
    move: i; apply/within_continuous_coord.
    apply: (within_continuous_lipschitz _ k0 _ (u0 := u0) (r := r)).
    + exact: cts_fun.
    + exact: lip2_delta_max.
    + exact: cont1_delta_max.
    + exact: img_cball_picard_fix.
  have [H1 H2] := @continuous_FTC1_closed _ (fun x => f x (picard_fix x) ord0 j)
                  a t _ tadelta (Fint j) ta (Fcont j).
  have Hderivable : derivable (fun x => \vint[mu]_(y in `[a, x]) f y (picard_fix y)) t 1.
    apply/derivable_mxP => i0 i; rewrite (ord1 i0){i0}/=.
    have [?] := @continuous_FTC1_closed _ (fun x => f x (picard_fix x) ord0 i)
                a t _ tadelta (Fint i) ta (Fcont i).
    rewrite /rowRintegral.
    rewrite [X in derivable X t 1](_ : _ =
        (fun x => \int[mu]_(y in `[a, x]) f y (picard_fix y) ord0 i))//.
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
rewrite -(@picard_funE _ _ _ a b k _ r lip2 cont1 rho)//=.
  rewrite eval_mod_on_itv// inE; apply: subset_itv_oo_cc.
  by rewrite inE in tad.
exact: img_cball_picard_fix.
Qed.

Lemma cauchy_lipschitz_in_cball (t : R) : `[a, a + delta_max] t ->
  closed_ball u0 r%:num (picard_fix t).
Proof. by move=> taad; apply: img_cball_picard_fix => /=; exists t. Qed.

End picard.

Section continuous_patch.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables  (a b c : R) (f : R -> U) (g : R->U). 
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous f}.
Hypothesis cont2 : {within `[b, c], continuous g}.
Hypothesis matchb : f b = g b.

Lemma within_continuous_patch : {within `[a,c], continuous (patch g `[a, b] f)}.
  have -> : `[a, c] = `[a, b] `|` `[b, c].
      rewrite (@itv_bndbnd_setU _ _ _ (BRight b)) // ?bnd_simp//=; last 2 first.
        exact: ltW.
        exact: ltW.
      apply/seteqP; split => x.
        move=> []; [by left|right].
        exact: subset_itv_oc_cc b0.
      move=> []; [by left|].
      rewrite -setU1itv ?bnd_simp//; last first.
        exact: ltW.
      case; [|by right].
      move=> ->; left => /=.
      by rewrite in_itv/= (ltW ab) lexx.
    apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b c)).
      have eq1 : {in `[a, b],  f =1 patch g `[a, b] f }.
        move => x0 x0ab.
        by rewrite /patch x0ab.
      apply: (continuous_within_ext eq1).
      exact: cont1.
      have eq2 : {in `[b, c],  g =1 patch g `[a, b] f }.
      move => x0 x0ab.
      rewrite /patch;case: ifPn => [xab | xabnot] => //.
      suff -> : x0 = b by rewrite matchb.
      apply: le_anti.
      move: x0ab xab.
      by rewrite !inE/=!in_itv/= => /andP [-> _] /andP [_ ->].
    apply /continuous_subspaceW/(continuous_within_ext eq2)/cont2.
    by apply: subset_itvl; rewrite bnd_simp.
Qed.
End continuous_patch.

Section picard_extension.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b c : R) (u0 : U) (sol1 : R -> U) (sol2 : R -> U).
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous (fun x => phi x (sol1 x))}.
Hypothesis cont2 : {within `[b, c], continuous (fun x => phi x (sol2 x))}.
Hypothesis matchb : sol1 b = sol2 b.

Lemma solution_extends : is_integral_sol_on phi a b u0 sol1 ->
  is_integral_sol_on phi b c (sol1 b) sol2 ->
  is_integral_sol_on phi a c u0 (patch sol2 `[a, b] sol1).
Proof.
move => [p0a p0s ] [p1a p1s].
have h0 : patch sol2 `[a, b] sol1 a = u0.
  rewrite /patch.
  case: ifPn => [xK | xKnot] => //.
  move /negP : xKnot.
  by rewrite inE/=in_itv/=lexx ltW.
split => //.
rewrite h0.
move => t tac.
rewrite /patch.
case: ifPn => [xK | xKnot] => /=.
  rewrite inE in xK.
  rewrite p0s // p0a.
  apply /rowP => i.
  rewrite !mxE.
  congr (_ + _)%E.
  apply eq_Rintegral => /= x xat.
  suff ->: (x \in `[a,b]) by [].
  move : xat xK.
  rewrite !inE /= !in_itv /= => /andP [xat1 xat2] /andP [tab1 tab2].
  apply /andP; split => //.
  exact/le_trans/tab2.
have tbc : t \in `[b, c].
  move : tac.
  move /negP : xKnot.
  rewrite !inE /= !in_itv /=.
  have /orP := le_total b t.
  case => // -> h1 /andP [h2 ->] //.
  by move : h1;rewrite h2.
rewrite (rowRintegral_itv_split (c := b) (F := (fun x => phi x (patch sol2 `[a, b] sol1 x)))).
- rewrite inE in tbc.
  rewrite p1s //.
  suff : sol2 b = u0 + \vint[lebesgue_measure]_(s in `[a, b]) phi s (patch sol2 `[a, b] sol1 s).
    rewrite /GRing.add /= addmxA => ->;congr (addmx _).
    apply eq_rowRintegral => /= x xbt.
    rewrite /patch;case: ifPn => [ | ] => //.
    rewrite inE/=in_itv/= => /andP [_ xleb].
    move : xbt.
    rewrite !inE/=!in_itv/= => /andP [h _].
    suff -> : x = b by rewrite p1a.
    apply le_anti.
    by rewrite xleb.
  rewrite p1a p0s;last by rewrite /=in_itv/=ltW//=.
  rewrite p0a.
  congr (_ + _)%E.
  rewrite /patch.
  by apply eq_rowRintegral => /= x ->.
- by rewrite ltW //=; move : tbc; rewrite inE /= in_itv /= => /andP [-> _].
- move=> i.
  have cont' : {within `[a, t], continuous (fun x => phi x (patch sol2 `[a, b] sol1 x) ord0 i)}.
    have -> : `[a, t] = `[a, b] `|` `[b, t].
      rewrite (@itv_bndbnd_setU _ _ _ (BRight b))// ?bnd_simp//=; last 2 first.
        exact: ltW.
        by move: tbc; rewrite inE/= in_itv/= => /andP[].
      apply/seteqP; split => x.
        move=> []; [by left|right].
        exact: subset_itv_oc_cc b0.
      move=> []; [by left|].
      rewrite -setU1itv ?bnd_simp//; last first.
        by move: tbc; rewrite inE/= in_itv/= => /andP[].
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
      rewrite /patch;case: ifPn => [xab | xabnot] => //.
      suff -> : x0 = b by rewrite matchb.
      apply: le_anti.
      move: x0ab xab.
      by rewrite !inE/=!in_itv/= => /andP [-> _] /andP [_ ->].
    apply /continuous_subspaceW/(continuous_within_ext eq2)/cont2.
    apply: subset_itvl; rewrite bnd_simp.
    by move : tbc; rewrite inE/= in_itv/= => /andP[].
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
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Variable rho : {posnum R}.
Hypothesis rho1 : rho%:num < 1.
(* Let rho : {posnum R} := (2^-1)%:pos. *)

(* Let rho1 : rho%:num < 1. *)
(* Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed. *)

Definition local_solution := repr (picard_fix ab k0 lip2 cont1 rho1).

Local Notation delta_max := (delta_max phi a b k u0 r rho).

Lemma solution_local_solution : is_sol_on phi u0 a (BLeft (a + delta_max)) local_solution.
Proof.
apply /(integral_sol_iff_sol (k:=k) (r:=r)) => //.
- exact: ltDl_delta_max.
- move=> t td.
  apply: lip2.
  move: td; rewrite /=!in_itv/= => /andP [-> h] /=.
  by rewrite (le_trans h)// -lerBrDl; exact: delta_max_itv.
- move=> /= x xB  .
  apply/continuous_subspaceW/cont1 => //.
  apply: subset_itvl => //=.
  by rewrite bnd_simp -lerBrDl delta_max_itv.
- rewrite /local_solution.
  exact: cts_fun.
- by move => _ [t tad] <-; exact: cauchy_lipschitz_in_cball.
- exact: cauchy_lipschitz_integral_version.
Qed.

Lemma solution_stays_in_ball :
  {in `[a, a + delta_max], forall t, closed_ball u0 r%:num (local_solution t)}.
Proof. by move=> t; rewrite inE => /cauchy_lipschitz_in_cball; exact. Qed.

Lemma solution_continuous :
  {within `[a, a + delta_max], continuous local_solution}.
Proof. exact: cts_fun. Qed.

Definition cauchy_lipschitz_local_f : continuousFunType `[a, a + delta_max] [set: 'rV[R]_n] :=
  repr (picard_fix ab k0 lip2 cont1 rho1).

Let f := cauchy_lipschitz_local_f.

Theorem cauchy_lipschitz_local :
  delta_max > 0 /\
  is_sol_on phi u0 a (BLeft (a + delta_max)) f /\
  {in `[a, a + delta_max], forall t, closed_ball u0 r%:num (f t)} /\
  {within `[a, a + delta_max], continuous f}.
Proof.
split; first exact: delta_max_gt0.
split; [| split].
- exact: solution_local_solution.
- exact: solution_stays_in_ball.
- exact: solution_continuous.
Qed.

Local Notation V := (Cont_on_seg_quot.quot_continuousFunType  (@leDl_delta_max _ _ phi a b k ab u0 r k0 rho)).

Theorem cauchy_lipschitz_local_unique f' :
  {within `[a,a+delta_max], continuous f'} ->
  {in `[a, a + delta_max], forall t, closed_ball u0 r%:num (f' t)}  ->
  is_sol_on phi u0 a (BLeft (a + delta_max)) f' ->
  {in `[a, a + delta_max], f =1 f'}.
Proof.
move => cont bnd.
move /(integral_sol_iff_sol k0 (r:=r) ) => []//.
- exact: ltDl_delta_max.
- move=> t td.
  apply: lip2.
  move: td; rewrite /=!in_itv/= => /andP [-> h] /=.
  by rewrite (le_trans h)// -lerBrDl; exact: delta_max_itv.
- move=> /= x xB  .
  apply/continuous_subspaceW/cont1 => //.
  apply: subset_itvl => //=.
  by rewrite bnd_simp -lerBrDl delta_max_itv.
- by move => _ [t tad] <-;apply bnd;rewrite inE.
move => h0 h1.
move => t tab.
have fc :  cont_on_seg a (a+delta_max) f'.
  by apply mem_set.
have pieq :  \pi_V%qT f = \pi_V%qT (cont_on_seg_Sub fc).
  rewrite reprK.
  apply: cauchy_lipschitz_unique.
    move => /= _ [t' tad' ] <- /=.
    rewrite /Cont_on_seg_quot.quot_continuousFunType_to_fun.
    suff -> : (repr (\pi_V%qT (cont_on_seg_Sub fc))) t' = f' t'.
      by apply bnd;rewrite inE.
    by apply Cont_on_seg_quot.eval_mod_on_itv;rewrite inE.
  move => t0.
  rewrite inE  => -t0ad.
  rewrite Cont_on_seg_quot.eval_mod_on_itv //=; last by rewrite inE.
  rewrite h1// h0.
  apply congr1.
  apply: eq_rowRintegral => t' tad'.
  rewrite Cont_on_seg_quot.eval_mod_on_itv //=.
  move: tad'.
  rewrite! inE.
  apply: subset_itvl.
  move : t0ad.
  by rewrite /=in_itv/= => /andP[].
suff -> : f t = (Cont_on_seg_quot.quot_continuousFunType_to_fun (\pi_V%qT (cont_on_seg_Sub fc))) t.
  by rewrite /Cont_on_seg_quot.quot_continuousFunType_to_fun/=;apply Cont_on_seg_quot.eval_mod_on_itv.
rewrite -pieq.
by rewrite Cont_on_seg_quot.eval_mod_on_itv.
Qed.
End cauchy_lipschitz_local.
Section continuous_confined.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (a b : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Let B := closed_ball u0 r%:num.
Local Lemma continuous_confined  (g : R -> U) : {within `[a, b], continuous g} ->  (g a) = u0 -> exists Delta:{posnum R}, {in `[a, a + Delta%:num ], forall t, (g t) \in B}. 
Proof.
move /(continuous_within_itvP _ ab)  => [cc cl cr] g0. 
have : {within `[a,b], continuous (fun t => `| u0 - g t |) }.
  apply: within_continuous_comp_norm. 
    by rewrite ltW.
  apply/ continuous_within_itvP => //=.
  split.
    move => t tab.
    apply: (cvgB (cvg_cst _) (cc _ tab)).
    apply: (cvgB (cvg_cst _) cl).
    apply: (cvgB (cvg_cst _) cr).
move /(continuous_within_itvP _ ab)  => [_ /cvgrPdist_le + _].
move /(_ r%:num).
case => // Delta /= Delta0.
rewrite /ball_/= g0 subrr normr0/= => H.
have D20: (0 < Delta / 2) by rewrite divr_gt0.
exists (PosNum D20).
move => t tab.
move : tab.
rewrite inE /=in_itv/= => /andP[].
rewrite le_eqVlt => /orP[/eqP <- | ].
  rewrite g0 /B inE => _;by apply: closed_ballxx.
move => ta td.
have /=:= (H t).
rewrite add0r normrN normr_id.
rewrite inE /B closed_ballE/closed_ball_//=;apply =>//.
rewrite ltr_distl.
apply /andP;split.
rewrite ltrBlDr.
apply (le_lt_trans td).
  by rewrite ler_ltD// ltr_pdivrMr// ltr_pMr// ltrDl.
apply (lt_le_trans ta).
by rewrite lerDl ltW.
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
Hypothesis sol1 : is_sol_on phi u0 a (BLeft b) f.
Let rho_max : {posnum R} := (2^-1)%:pos.

Let dmax rho :=   delta_max phi a b k u0 r rho.
Let fc := local_solution ab k0 lip2 cont1.

Lemma initial_solution_unique f' :{within `[a,b], continuous f'} ->
  is_sol_on phi u0 a (BLeft b) f' ->
  exists Delta : {posnum R}, {in `[a, a+Delta%:num], f =1 f'} /\
   {in `[a, a + Delta%:num], forall t, closed_ball u0 r%:num (f t)}.
Proof.
move => cf' sol2.
suff [rho [Delta [Hrho [Db [P1 P2]]]]]: exists rho Delta : {posnum R}, exists (Hrho : (rho%:num < 1)) , Delta%:num <= dmax rho /\ {in `[a, a+Delta%:num], f =1 fc Hrho } /\ {in `[a, a+Delta%:num], f' =1 fc Hrho } .
  exists Delta; split =>  t tab; first by rewrite P1 // P2.
  rewrite P1 //.
  apply solution_stays_in_ball.
  move: tab; rewrite !inE/=!in_itv/= => /andP[-> h] //=.
  apply (le_trans h).
  by rewrite lerD.
have [d1 D1] := continuous_confined r ab cf sol1.1.
have [d2 D2] := continuous_confined r ab cf' sol2.1.
have [rho [drho1 drho2]] : exists rho, dmax rho <= (Num.min d1%:num d2%:num) /\ rho%:num < 1. 
  rewrite /dmax/delta_max.
  have posk : 0 < Num.min rho_max%:num (Num.min (k * rho_max%:num) (k * (Num.min d1%:num d2%:num))).
    rewrite lt_min; apply /andP;split=>//.
    rewrite lt_min; apply /andP;split=>//.
    by apply mulr_gt0.
    by apply mulr_gt0.
  exists (PosNum posk).
  split => //=.
    rewrite !ge_min //=;apply /orP;right;apply /orP;right.
    rewrite !minr_pMl //= ?invr_ge0  //; try by rewrite ltW.
    rewrite ge_min; apply /orP;right.
    rewrite ge_min; apply /orP; right.
    by rewrite mulrC mulrA mulVr ?unitfE ?mul1r // ?gt_eqF.
    rewrite gt_min; apply /orP;left.
    by rewrite invf_lt1 // ltrDl.
have drho_pos : 0 < dmax rho.
  by apply delta_max_gt0.
exists rho, (PosNum drho_pos), drho2.
split => //.
split.
  move => t tad.
  apply /esym.
  apply : cauchy_lipschitz_local_unique.
  - apply/continuous_subspaceW/cf => //.
    apply: subset_itvl => //=.
    by rewrite bnd_simp -lerBrDl;apply delta_max_itv.
  - move => t0 t0ad.
    suff : (f t0) \in closed_ball u0 r%:num by rewrite inE.
    apply D1.
    move : t0ad.
    rewrite !inE/=!in_itv/= => /andP[-> h1] //=.
    apply: (le_trans h1).
    rewrite lerD//.
    apply (le_trans drho1).
    by rewrite ge_min lexx;apply /orP;left.
  - split; first by apply sol1.
    move => t0 t0ad.
    have [_ + ] := sol1;apply.
    move : t0ad.
    rewrite !inE/=!in_itv/= => /andP[-> h]//=.
    apply: (lt_le_trans h).
    rewrite -lerBrDl.
    exact: delta_max_itv.
  - exact: tad.
move => t tad.
apply /esym.
apply : cauchy_lipschitz_local_unique.
- apply/continuous_subspaceW/cf' => //.
  apply: subset_itvl => //=.
  by rewrite bnd_simp -lerBrDl;apply delta_max_itv.
- move => t0 t0ad.
  suff : (f' t0) \in closed_ball u0 r%:num by rewrite inE.
  apply D2.
  move : t0ad.
  rewrite !inE/=!in_itv/= => /andP[-> h1] //=.
  apply: (le_trans h1).
  rewrite lerD//.
  apply (le_trans drho1).
  by rewrite ge_min lexx;apply /orP;right.
- split; first by apply sol2.
  move => t0 t0ad.
  have [_ + ] := sol2;apply.
  move : t0ad.
  rewrite !inE/=!in_itv/= => /andP[-> h]//=.
  apply: (lt_le_trans h).
  rewrite -lerBrDl.
  exact: delta_max_itv.
exact: tad.
Qed.

End solution_locally_unique.


Section solution_unique.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}) (f : R -> U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis cf : {within `[a, b], continuous f}.
Hypothesis sol1 : is_sol_on phi u0 a (BLeft b) f.

Lemma unique_at_t0 f' t0: a <= t0 -> t0 < b -> {within `[a,b], continuous f'} -> is_sol_on phi u0 a (BLeft b) f' ->
                          f' t0 = f t0 -> exists Delta : {posnum R}, {in `[a, t0+Delta%:num], f =1 f'}.
                         
Proof.
move => t0a tb0 cf' sol2 ft0.
have ta :  `[t0, b] `<=` `[a, b].
  move => t.
  rewrite /=!in_itv/= => /andP[+ ->]//.
  move => t0t;apply /andP;split=>//.
  by apply /le_trans/t0t.
have lip20 :{in `[t0, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
  move => t t0b;apply lip2.
  move : t0b; rewrite !in_itv/= => /andP[+ ->]//.
  move => t0t;apply /andP;split=>//.
  by apply /le_trans/t0t.
have cont10:  {in B, forall y : 'rV_n, {within `[t0, b], continuous phi^~ y}}.
  move => /=x xB.
  by apply /continuous_subspaceW/cont1.
have cf0 : {within `[t0, b], continuous f}.
  by apply /continuous_subspaceW/cf.
have cf'0 : {within `[t0, b], continuous f'}.
  by apply /continuous_subspaceW/cf'.
have sol10 : is_sol_on phi (f t0) t0 (BLeft b) f.
   split => //.
   move => t tab.
   apply sol1.
   move : tab.
   rewrite !inE/=!in_itv/= => /andP[+ ->].
  move => t0t;apply /andP;split=>//.
  by apply /le_lt_trans/t0t.
have sol20 : is_sol_on phi (f t0) t0 (BLeft b) f'.
   split => //.
   move => t tab.
   apply sol2.
   move : tab.
   rewrite !inE/=!in_itv/= => /andP[+ ->].
  move => t0t;apply /andP;split=>//.
  by apply /le_lt_trans/t0t.
have := initial_solution_unique tb0 k0 lip20 cont10 cf0 .
Admitted.
Lemma solution_unique f': {within `[a,b], continuous f'} -> is_sol_on phi u0 a (BLeft b) f' -> {in `[a,b], f =1 f'}.
Proof.
move => fc' sol2.
set E := [set t | {in `[a,t], f =1 f'}].
suff : E b by rewrite /E/=.
have Enonempty : E !=set0.
  exists a.
  rewrite /E/= => t.
  rewrite set_itv1 inE/= => ->.
  by rewrite sol1.1 sol2.1.
have mon c : a <= c -> E c -> forall c', a <= c' <= c -> E c'. 
  move => ac.
  rewrite /E/= => h c' /andP[ac' cc'] t.
  rewrite inE => tac'.
  apply h.
  by rewrite inE; apply/subset_itvl/tac'.
have [hP | hP] := lem (has_sup E);last first.
  have /(has_supPn Enonempty) := hP.
  move /(_ b) => [x Ex bx].
  apply (mon x) => //.
  rewrite ltW//.
  by apply (lt_trans ab bx).
  by rewrite !ltW.
have Ea : (a <= sup E).
admit.
suff : ~  sup E < b.
admit.
move => h.
Admitted.

End solution_unique.

Section picard_autonomous.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : U -> U) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : k.-lipschitz_B phi.

Definition is_sol_autonomous a b (f : R -> U) := f a = u0 /\
  {in `]a, b[, forall x, derivable f x 1 /\ f^`() x = phi (f x)}.
Definition phi_ (t : R) x := phi x.

Lemma phi_lip2 a b:  {in `[a, b]%R, forall x, k.-lipschitz_B (phi_ x)}.
Proof. by move => x abx; exact: lip2. Qed.

Lemma phi_cont1 a b : {in B, forall y, {within `[a, b], continuous phi_ ^~ y}}.
Proof. by move => /= x Bx; exact: cst_continuous_subspace. Qed.

Lemma autonomous_solution a b f :
  is_sol_autonomous a b f <-> is_sol_on phi_ u0 a (BLeft b) f.
Proof. by []. Qed.

Let rho : {posnum R} := (2^-1)%:pos.

Let rho1 : rho%:num < 1. 
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed. 

Theorem cauchy_lipschitz_autonomous a : exists f delta,
  delta > 0 /\ is_sol_autonomous a (a + delta) f /\
  {in `[a, a + delta], forall t, closed_ball u0 r%:num (f t)} /\
  {within `[a, a + delta], continuous f}.
Proof.
have aa1 : a < a + 1 by rewrite ltrDl.
have [d0 [solf [cball cf]]] :=
  cauchy_lipschitz_local aa1 k0 (@phi_lip2 a (a + 1)) (@phi_cont1 a (a + 1)) rho1.
exists (@cauchy_lipschitz_local_f R n phi_ a _ k u0 r aa1 k0
  (@phi_lip2 a (a + 1)) (@phi_cont1 a (a + 1)) rho rho1).
by exists (delta_max phi_ a (a + 1) k u0 r rho).
Qed.

End picard_autonomous.

Section locally_lipschitz.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables phi : U -> U.

Hypothesis locally_lipschitz : forall x,
  exists r k : {posnum R}, k%:num.-lipschitz_(closed_ball x r%:num) phi.

Theorem cauchy_lipschitz_ll u0 a : exists f delta r,
  delta > 0 /\ is_sol_autonomous phi u0 a (a + delta) f /\
  {in `[a, a + delta], forall t, closed_ball u0 r (f t)}.
Proof.
have [/= r [k lip]] := locally_lipschitz u0.
have [//|f [delta [delta_ft0 [solf [cball cf]]]]] := cauchy_lipschitz_autonomous  _ lip a.
by exists f, delta, r%:num.
Qed.

End locally_lipschitz.
