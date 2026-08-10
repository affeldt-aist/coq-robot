From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval.
From mathcomp Require Import poly generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
Require Import ode_common.

(**md**************************************************************************)
(* # Continuous functions over a closed interval                              *)
(*                                                                            *)
(* The main purpose of this file is to define the quotient of continuous      *)
(* function over a closed interval. It is shown to form a complete normed     *)
(* type.                                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*         infty_norm f := pre_infty_norm (repr f)                            *)
(*   quot_contSeg a b U := quotient of continuous functions over a closed     *)
(*                         interval [a, b] to some normed module U            *)
(*                         Notation: `C[a, b] or `C([a, b] U)                 *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "`C[ a , b ]" (at level 0, a, b at level 0,
  format "`C[ a ,  b ]").
Reserved Notation "`C([ a , b ] W )" (at level 1, a, b at next level,
  format "`C([ a ,  b ]  W )").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Module ContSeg_zlmodType.
Section contSeg_zlmodtype.
Context {R : realType} (K : set R) (V : normedModType R).

HB.instance Definition _ := GRing.isZmodClosed.Build _ _
  (contseg_zmod_closed K V).

Fail Check continuousSubspaceType K [set: V] : zmodType.

HB.instance Definition _ :=
  [SubChoice_isSubZmodule of continuousSubspaceType K [set: V] by <:].

Check continuousSubspaceType K [set: V] : zmodType.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (contseg K) (@contfun_scaler_closed R K V).

Fail Check @continuousSubspaceType R V K [set: V] : lmodType _.

(*HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of continuousSubspaceType K [set: V] by <:].*)
HB.instance Definition _ :=
  [SubNmodule_isSubLSemiModule of continuousSubspaceType K [set: V] by <:].

Check continuousSubspaceType K [set: V] : lmodType _.

End contSeg_zlmodtype.
End ContSeg_zlmodType.

Section submod_contSeg.
Context {R : realType} (a b : R) {V : normedModType R}.
Local Notation T := (continuousSubspaceType `[a, b] [set: V]).

(* NB: point does not need to be 0, so rewrite f \_ K explicitly *)
Definition patch_contSeg0 : {pred T} :=
  [pred f : T | patch 0 `[a, b] f == 0].

End submod_contSeg.
Arguments patch_contSeg0 {R} {a b} V ab.

Module ContSeg_submod.
Export ContSeg_zlmodType.

Section submod_definition.
Context {R : realType} {V : normedModType R}.
Variables a b : R.

Lemma submod_closed_contSeg : submod_closed (@patch_contSeg0 _ a b V).
Proof.
split => /=.
- rewrite inE/=; apply/funext => x.
  by rewrite /patch; case: ifPn.
- move => f u v.
  rewrite !inE => u0 v0.
  apply/funext => u1.
  rewrite /patch; case: ifPn => // u1ab.
  move: u0 v0; rewrite /patch.
  move=> /(congr1 (fun x => x u1)); rewrite u1ab => uu1.
  move=> /(congr1 (fun x => x u1)); rewrite u1ab => vu1.
  by rewrite -[LHS]/(f *: u u1 + v u1) uu1 vu1 addr0 scaler0.
Qed.

Fail Check (patch_contSeg0 V ab) : zmodClosed _.

HB.instance Definition _ :=
  GRing.isZmodClosed.Build _ _ (GRing.submod_closedB submod_closed_contSeg).

Check (@patch_contSeg0 _ a b V) : zmodClosed _.

End submod_definition.
End ContSeg_submod.

Section contSeg_seminorm.
Context {R : realType} {W : normedModType R}.
(*Variables a b : R.
Let K := `[a, b].*)
Variable K : set R.
Hypotheses (compactK : compact K).
Local Notation T := (continuousSubspaceType K [set: W]).

Import ContSeg_zlmodType.

(* NB: require Nmodule properties *)
Lemma pre_infty_norm_eq0 : pre_infty_norm (0 : T) = 0.
Proof.
rewrite /pre_infty_norm.
have [K0|K0] := eqVneq K set0.
  by rewrite [X in [set _ | _ in X]](_ : _ = set0)// image_set0// sup0.
rewrite -(sup1 0); congr sup.
apply: eq_set => /= z.
apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
move/set0P : K0 => [c Kc].
by exists c => //; rewrite normr0.
Qed.

(* NB: require Nmodule properties *)
Lemma pre_infty_normrMn (f : T) n : pre_infty_norm (f *+ n) = pre_infty_norm f *+ n.
Proof.
rewrite /pre_infty_norm.
have [K0|K0] := eqVneq K set0.
  do 2 rewrite [X in [set _ | _ in X]](_ : _ = set0)// image_set0//.
  by rewrite sup0 mul0rn.
rewrite -sup_Mn//.
rewrite image_comp/=; congr (sup _).
apply: eq_imagel => z Kz /=; rewrite -normrMn /=.
have /(congr1 (@^~ z)) <- := natmulfctE f n.
congr (normr (_ z)).
(* NB: investigate *)
elim: n f => //= n IH f.
by rewrite !mulrS -IH.
Qed.

Lemma pre_infty_normN (f : T) : pre_infty_norm (- f) = pre_infty_norm f.
Proof.
rewrite /pre_infty_norm; congr sup; apply: eq_set => /= x0.
apply: propext; split => [[x1 in_itv] | [x1 in_itv]] H; exists x1 => //.
  by rewrite -normrN.
by rewrite normrN.
Qed.

End contSeg_seminorm.

Module ContSeg_quot.
Export ContSeg_zlmodType.

Import ContSeg_submod.
Import Quotient.

Section contSeg_quotient.
Context {R : realType} (a b : R) {W : normedModType R}.

(*Definition eq_seg (f g : continuousSubspaceType a b) := `[< {in `[a, b], f =1 g} >].

Let eq_seg_refl : reflexive eq_seg.
Proof. by move=> f; apply/asboolP => r. Qed.

Let eq_seg_sym : symmetric eq_seg.
Proof. by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP => r /h. Qed.

(* TODO: wait for quotient *)
Let eq_seg_trans : transitive eq_seg.
Proof.
by move=> f g h /asboolP fg /asboolP gh; apply/asboolP => r rab; rewrite fg// gh.
Qed.

Canonical eq_seg_canonical :=
  EquivRel eq_seg eq_seg_refl eq_seg_sym eq_seg_trans.*)

Local Open Scope quotient_scope.

Definition quot_contSeg := {quot (@patch_contSeg0 R a b W)}.
Local Notation T := quot_contSeg.

(* NB: ZmodQuotient is defined in ring_quotient.v *)
HB.instance Definition _ := ZmodQuotient.on T.

Definition fun_of_quot_contSeg (f : T) : subspace `[a, b] -> W := repr f.
Coercion fun_of_quot_contSeg : T >-> Funclass.

Lemma eq_segP (f g : T) : reflect ({in `[a, b], f =1 g}) (f == g %[mod T]).
Proof.
apply/(iffP idP); rewrite eqmodE//=.
- rewrite equivE inE => fgab0 x xab.
  move/(congr1 (fun z => z x)) : fgab0.
  by rewrite /patch xab => /subr0_eq.
- move=> abfg.
  rewrite /equivE inE; apply/funext => x.
  rewrite /patch; case: ifPn => //= xab.
  rewrite !fctE.
  by apply/eqP; rewrite subr_eq0; exact/eqP/abfg.
Qed.

Lemma eqmod_on_itv f g : f = g %[mod T] -> {in `[a, b]%R, f =1 g}.
Proof.
move=> /eqmodP + x xab.
move/set_mem => abfg0.
apply: subr0_eq.
move/(congr1 (fun z => z x)) : abfg0.
by rewrite /patch mem_setE/= xab.
Qed.

Lemma eval_mod_on_itv f x : x \in `[a, b]%R -> (\pi_T f : T) x = f x.
Proof.
move => xab.
apply: (@eqmod_on_itv (repr (\pi_T f)) f) => //.
by rewrite reprK.
Qed.

Lemma quot_contSeg_fctB (f g : T) t : t \in `[a, b]%R ->
  (f - g : T) t = (f : T) t - (g : T) t.
Proof.
move=> tab.
rewrite -(reprK f) -(reprK g).
rewrite /GRing.opp/=.
rewrite -Quotient.pi_opp.
rewrite /GRing.add/=.
rewrite -Quotient.pi_add.
by rewrite !eval_mod_on_itv.
Qed.

End contSeg_quotient.
End ContSeg_quot.
Arguments ContSeg_quot.quot_contSeg {R} a b W.

Notation "`C[ a , b ]" := (ContSeg_quot.quot_contSeg a b _).
Notation "`C([ a , b ] W )" := (ContSeg_quot.quot_contSeg a b W).

Section zmodule_normed.
Context {R : realType} {W : normedModType R}.
Variables a b : R.

Import ContSeg_quot.

Definition infty_norm (f : `C([a , b] W)) := pre_infty_norm (repr f).

Local Open Scope quotient_scope.

Lemma ler_infty_normD (x y : `C[a, b]) :
  infty_norm (x + y) <= infty_norm x + infty_norm y :> R.
Proof.
rewrite /infty_norm/=.
have [K0|K0] := eqVneq `[a, b] set0.
  rewrite /pre_infty_norm.
  do ! rewrite [X in [set _ | _ in X]](_ : _ = set0)// image_set0//.
  by rewrite sup0 addr0.
have ab : a <= b.
  rewrite leNgt; apply: contra K0 => ba.
  by rewrite set_itv_ge// bnd_simp -ltNge.
move/set0P in K0.
rewrite -sup_sumE; [apply: normr_has_sup => //; exact: segment_compact..|].
apply: sup_le.
- move=> A -[s sab] <-{A}.
  rewrite /down/=.
  eexists.
  split.
    exists `|repr x s|; first by exists s.
    exists `|repr y s|; first by exists s.
    reflexivity.
  suff  -> : repr (x + y) s = repr x s + repr y s by exact: ler_normD.
  suff : repr (x + y) = repr x + repr y %[mod `C[a, b]].
    move=> /eqmod_on_itv ->.
      by [].
    by [].
  by rewrite Quotient.pi_add !reprK.
- apply: (normr_has_sup _ _ _).1 => //.
  exact: segment_compact.
- split.
  + exists (`|x a| + `|repr y a|)=> /=.
    exists (`|repr x a|) => //; [exists a => //; by rewrite in_itv/= lexx ab|].
    by exists `|repr y a| => //; exists a => //; rewrite bound_itvE.
  + exists (sup [set `|repr x r| | r in `[a, b]] + sup [set `|repr y r| | r in `[a, b]]).
    apply ubP => _ [x0 xs] [y0 ys] <-.
    rewrite lerD// ub_le_sup//.
      by apply: (normr_has_sup x _ _).2 => //; exact: segment_compact.
    by apply: (normr_has_sup y _ _).2 => //; exact: segment_compact.
Qed.

Lemma infty_normr0_eq0 (x : `C[a, b]) : infty_norm x = 0 -> x = 0.
Proof.
rewrite /infty_norm /pre_infty_norm /= => H.
rewrite -(reprK x) -(reprK (0 : `C[a, b])).
apply/eqquotP.
rewrite Quotient.equivE inE; apply: funext => r /=.
rewrite /patch; case : ifPn => // /set_mem in_itv.
rewrite 3!fctE.
have -> : {in `[a, b]%R, repr (0 : `C[a, b]) =1 (0 : @continuousSubspaceType R W `[a, b] setT)}.
- apply/eqmod_on_itv.
  by rewrite reprK /GRing.zero /= /Quotient.zero /= -lock.
- by rewrite inE.
- rewrite [LHS]subr0.
  apply/eqP; rewrite -normr_le0.
  have [ab|ab] := leP a b.
    have ab0 : `[a, b] !=set0 by exists r.
    have := sup_upper_bound (normr_has_sup x (@segment_compact _ a b) ab0).
    rewrite H /ubound /=.
    apply.
    by exists r.
  move: in_itv; rewrite /= in_itv/= => /andP[ar rb].
  by have := le_trans ar rb; rewrite leNgt ab.
Qed.

Lemma infty_normrMn (x : `C[a, b]) n : infty_norm (x *+ n) = infty_norm x *+ n.
Proof.
rewrite /infty_norm -pre_infty_normrMn.
apply: pre_infty_norm_itv_eq => r rab.
suff : repr (x *+ n) = repr x *+ n %[mod `C[a, b]].
 move=> /eqmod_on_itv ->//.
 by rewrite inE in rab.
elim n; [rewrite !mulr0n // reprK /GRing.zero /= /Quotient.zero /= -lock // | ].
move => n' IHn'; rewrite reprK !mulrS.
rewrite reprK in IHn'.
rewrite Quotient.pi_add reprK.
by move : IHn' <-.
Qed.

Require Import tilt_analysis.

Let infty_norm_pi0 x : infty_norm (\pi_`C[a, b] x) = pre_infty_norm x.
Proof.
rewrite /infty_norm /=.
have /eqmod_on_itv Heq : repr (\pi_`C[a, b] x) = x %[mod `C[a, b]] by rewrite reprK.
apply: pre_infty_norm_itv_eq.
by apply/in_switch.
Qed.

Lemma infty_normrN (x : `C[a, b]) : infty_norm (- x) = infty_norm x.
Proof.
rewrite -(reprK x) /GRing.opp /= -Quotient.pi_opp !infty_norm_pi0.
rewrite /infty_norm /pre_infty_norm; congr sup.
apply/eq_set => /= x0.
apply/propext; split => [[x1 in_itv] | [x1 in_itv]] H; exists x1 =>//.
  by rewrite -normrN.
by rewrite normrN.
Qed.
(* TODO: dev the theory of sup following the theory of ess_sup *)

Fail Check `C[a, b] : normedZmodType R.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R `C[a, b]
  infty_norm ler_infty_normD infty_normr0_eq0 infty_normrMn infty_normrN.

Lemma infty_norm_pi x : `|\pi_`C[a, b] x| = pre_infty_norm x.
Proof. by rewrite /Num.norm /= infty_norm_pi0. Qed.

Lemma infty_norm_lt (f : `C[a, b]) e :
  `| f | < e -> {in `[a, b]%R, forall x : R, `|f x| < e}.
Proof.
rewrite -{1}(reprK f) infty_norm_pi => h x xab.
have [ab|ab] := leP a b.
  apply/le_lt_trans/h/pre_infty_norm_ge => //.
  by exists a => /=; rewrite bound_itvE.
  exact: segment_compact.
  by rewrite inE.
move: xab; rewrite in_itv/= => /andP[/le_trans /[apply]].
by rewrite leNgt ab.
Qed.

Lemma infty_norm_le (f : `C[a, b]) e :
  `| f | <= e -> {in `[a, b]%R, forall x : R, `|f x| <= e}.
Proof.
rewrite -{1}(reprK f) infty_norm_pi => h x xab.
have [ab|ab] := leP a b.
  apply/le_trans/h/pre_infty_norm_ge => //.
  by exists a => /=; rewrite bound_itvE.
  exact: segment_compact.
  by rewrite inE.
move: xab; rewrite in_itv/= => /andP[/le_trans /[apply]].
by rewrite leNgt ab.
Qed.

Lemma infty_norm_le2 (f : `C[a, b]) e : 0 <= e ->
  {in `[a, b]%R, forall x : R, `|f x| <= e} -> `| f | <= e.
Proof.
move=> e0 h; have [ab|ba] := leP a b.
  rewrite -(reprK f) infty_norm_pi pre_infty_norm_le//.
  by exists a => /=; rewrite bound_itvE.
  exact/in_switch.
rewrite [leLHS](_ : _ = 0)//.
rewrite /Num.norm/= /infty_norm /pre_infty_norm.
rewrite [X in [set _ | _ in X]](_ : _ = set0) ?image_set0 ?sup0//.
by rewrite set_itv_ge// bnd_simp -ltNge.
Qed.

Check `C[a, b] : normedZmodType R.

Check (pseudoMetric_normed `C[a, b]) : pseudoMetricType R.
Check (pseudoMetric_normed `C[a, b]) : normedZmodType R.

Fail Check (pseudoMetric_normed `C[a, b]) : normedModType R.

End zmodule_normed.

Section quot_contSeg_normedtype.
Context {R : realType} {W : normedModType R} {r s : R}.

Import ContSeg_quot.

Fail Check (pseudoMetric_normed `C[r, s]) : normedModType R.
HB.instance Definition _ :=
  PseudoMetric.copy `C([r, s] W) (pseudoMetric_normed `C([r, s] W)).
HB.instance Definition _ := isPointed.Build `C([r, s] W) 0.

Lemma is_normZmod_contFunBallType : NormedZmod_PseudoMetric_eq R `C([r, s] W).
Proof. by constructor. Qed.

Fail Check `C([r, s] W) : pseudoMetricNormedZmodType R.

HB.instance Definition _ := is_normZmod_contFunBallType.

Check `C([r, s] W) : PseudoMetricNormedZmod0.type R.

(* NB: new since MCA 1.17.0 *)
HB.instance Definition _ := isPseudoMetricNormedZmodule.Build R `C([r, s] W).

Check `C([r, s] W) : pseudoMetricNormedZmodType R.

Import Quotient.
Open Scope quotient_scope.
Definition cont_scale (k : R) (f : `C([r, s] W)) : `C[r, s] :=
  \pi_`C[r, s] (k *: repr f).

Let cont_scalerA a b f : cont_scale a (cont_scale b f) = cont_scale (a * b) f.
Proof.
rewrite /cont_scale.
have [-> | a0] := eqVneq a 0; first by rewrite !(scale0r, mul0r).
apply/eqmodP; rewrite /equiv_equiv/= /equiv/=.
rewrite -scalerA -scalerBr.
rewrite inE.
apply/funext => x/=.
rewrite /patch; case: ifPn => // xrs.
rewrite !fctE.
apply/eqP; rewrite scaler_eq0.
rewrite (negPf a0)/= subr_eq0.
apply/eqP.
case: piP => g.
rewrite mem_setE in xrs.
by move/eqmod_on_itv => /(_ _ xrs) <-.
Qed.

Let cont_scale1r : left_id 1 cont_scale.
Proof.
move=> v.
rewrite /cont_scale/=.
rewrite [RHS](_ : _ = (\pi_`C[r, s] (repr v))%qT); first by rewrite reprK.
apply/eqmodP.
by rewrite scale1r.
Qed.

Let cont_scalerDr : right_distributive cont_scale +%R.
Proof.
move=> k b c.
rewrite /cont_scale/=.
have [-> | k0] := eqVneq k 0.
  by rewrite !scale0r piE//= add0r.
rewrite /cont_scale/=.
rewrite piE/=.
apply/eqmodP.
rewrite /equiv_equiv /equiv/=.
rewrite -scalerDr.
rewrite -scalerBr.
rewrite inE.
apply/funext => x/=.
rewrite /patch; case: ifPn => // xrs.
rewrite !fctE.
apply/eqP; rewrite scaler_eq0 (negPf k0)/=.
rewrite subr_eq0.
apply/eqP.
have := @eqmod_on_itv _ _ _ _ (repr (b + c)) (repr b + repr c).
move=> ->//; last by rewrite mem_setE in xrs.
rewrite pi_add//=.
by rewrite !reprK.
Qed.

Let cont_scalerDl v : {morph cont_scale^~ v: a b / a + b}.
Proof.
move=> a b.
rewrite /cont_scale piE/=.
apply/eqmodP; rewrite /equiv_equiv/= /equiv/=.
rewrite -scalerDl subrr.
rewrite inE/=.
by apply/funext => x; rewrite /patch; case: ifP.
Qed.

HB.instance Definition _ :=
  @GRing.Zmodule_isLmodule.Build R `C([r, s] W) cont_scale cont_scalerA cont_scale1r
  cont_scalerDr cont_scalerDl.

Local Lemma repr_mult l (x : `C[r, s]) a : a \in `[r, s]%R ->
  repr (l *: x) a = l *: (repr x a).
Proof.
move=> ars.
have : repr (l *: x) = l *: repr x %[mod `C[r, s]].
  by case: piP.
move/(@eqmod_on_itv _ _ _ _ (repr (l *: x)) (l *: repr x)).
by move/(_ _ ars).
Qed.

Lemma is_pmnormedZmod_contFunBallType :
  PseudoMetricNormedZmod_Lmodule_isNormedModule R `C([r, s] W).
Proof.
constructor => l x.
rewrite /Num.norm/= /infty_norm /pre_infty_norm /=.
have [rs|sr] := leP r s; last first.
  rewrite /=.
  have rs1 : `[r, s] = set0 by rewrite set_itv_ge// bnd_simp -ltNge.
  rewrite (_ : [set (normr \o repr x) x0 | x0 in `[r, s]] = set0).
    rewrite -(image_set0 (normr \o repr x)).
    by rewrite -rs1.
  rewrite (_ : [set (normr \o repr (l *: x)) x0 | x0 in `[r, s]] = set0).
    rewrite -(image_set0 (normr \o repr (l *: x))).
    by rewrite -rs1.
  by rewrite !sup0 mulr0.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_sup.
    exists `|repr (l *: x) r|, r => //=.
    by rewrite bound_itvE.
  move=> _/= [a ars] <-.
  rewrite repr_mult; first by rewrite inE.
  rewrite normrZ ler_wpM2l// ub_le_sup//.
    apply: (normr_has_sup _ _ _).2 => //.
    exact: segment_compact.
    by exists a.
  by exists a.
rewrite -ge0_supZl/=.
  by rewrite normr_ge0.
apply sup_le; [ | | apply normr_has_sup]; last first.
- by exists r =>/=; rewrite bound_itvE.
  exact: segment_compact.
- exists `|l *: x r|, `|repr x r|.
    by exists r => //=; rewrite bound_itvE.
  by rewrite normrZ.
- move => _  [_ [x0 x0rs] <- <-].
  exists (`|l| * `|repr x x0|); split=> //=; exists x0.
    by rewrite inE.
  rewrite repr_mult; first by rewrite inE.
  by rewrite normrZ.
Qed.

HB.instance Definition _ := is_pmnormedZmod_contFunBallType.
End quot_contSeg_normedtype.

From mathcomp Require Import algebra.
From mathcomp Require Import matrix_topology.

Section completeness.
Context {R : realType} {W : completeNormedModType R}.
Variables a b : R.

Import ContSeg_quot.

Check (`C([a, b] W) : pseudoMetricType R).
Check (`C([a, b] W) : normedModType R).

Definition lim_fun (F : set_system `C[a, b]) (FF : ProperFilter F) (Fc : cauchy F) :
  subspace `[a, b] -> W :=
  fun t => lim (@^~ t @ F).

Lemma lim_fun_is_fun (F : set_system `C[a, b]) (FF : ProperFilter F) (Fc : cauchy F) :
  @isFun (subspace `[a, b]) W `[a, b] [set: W] (@lim_fun F FF Fc).
Proof. by constructor. Qed.

HB.instance Definition _ F FF Fc := (@lim_fun_is_fun F FF Fc).

Lemma lim_fun_cvg_pt (F : set_system `C[a, b]) (FF: ProperFilter F) (Fc : cauchy F) :
  forall e : R, e > 0 -> forall t, t \in `[a, b]%R ->
  \forall f \near F, `|lim_fun FF Fc t - (f : `C[a, b]) t| <= e.
Proof.
have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :
    forall t : R, t \in `[a, b]%R ->
      cauchy (fmap (fun h : `C[a, b] => h t) (fun A : set `C[a, b] => nbhs F (fun g => A g))).
  move=> t tab A /=.
  rewrite -entourage_ballE => -[e /= e0 eA].
  rewrite near_simpl -near2E near_map2.
  apply: Fc.
  rewrite -entourage_ballE /nbhs/= /entourage_/=.
  exists e => // -[f g]/= /infty_norm_lt => h.
  apply: eA => /=.
  rewrite -ball_normE /ball/=.
  rewrite -quot_contSeg_fctB//.
  exact: h.
have cvg_pt (t : R) : t \in `[a, b]%R ->
    x @[x --> fmap (fun h : `C[a, b] => h t) F] --> lim_fun FF Fc t.
  by move=> tab; exact/cvg_entourageP/cvF.
move=> e e0 t /cvg_pt /cvgrPdist_le.
exact.
Qed.

Lemma lim_fun_cvg_uniform (F : set_system `C[a, b]) (FF: ProperFilter F) (Fc : cauchy F) :
  forall e : R, e > 0 -> \forall f \near F, forall t, t \in `[a, b]%R ->
  `|lim_fun FF Fc t - (f : `C[a, b]) t| <= e.
Proof.
move=> e e0.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have [/= [A B] /= [n1 n2] H] := Fc _ (entourage_ball `C[a, b] (PosNum e20)).
near=> f.
move=> t tab.
near F => g.
rewrite -(subrKA (g t) (lim_fun FF Fc t)).
rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
  near: g.
  by apply: lim_fun_cvg_pt => //; rewrite divr_gt0.
have : ball f (e /2 ) g.
  by apply: (H (f, g)); split => //=; [near: f|near: g].
rewrite /ball /= /pseudoMetric_from_normedZmodType.ball /=.
rewrite distrC.
rewrite -quot_contSeg_fctB//.
by move/ltW/infty_norm_le; exact.
Unshelve. all: by end_near. Qed.

Lemma lim_fun_cont (F : set_system `C[a, b]) (FF : ProperFilter F) (Fc : cauchy F) :
  {within `[a, b], continuous (@lim_fun F FF Fc)}.
Proof.
have [ab|] := ltP a b; last first.
  rewrite le_eqVlt => /predU1P[<-|ab'].
    by rewrite set_itv1; exact: continuous_subspace1.
  rewrite set_itv_ge// ?bnd_simp -?ltNge//.
  exact: continuous_subspace0.
have H (e : R) : e > 0 -> forall t, t \in `[a, b]%R ->
    \forall t' \near t, t' \in `[a, b] ->
    `|lim_fun FF Fc t - lim_fun FF Fc t'| <= e.
  move=> e0 t tab.
  near F => f.
  have lim_fune2 : forall u, u \in `[a, b]%R -> `|lim_fun FF Fc u - f u| <= e / 2.
    by near: f; apply: lim_fun_cvg_uniform => //; rewrite divr_gt0.
  move/(continuous_within_itvP _ ab) : (@continuous_fun _ _ f ) => [mc lc rc].
  have : t \in `[a, b] by rewrite inE.
  rewrite -{1}(setUitv1 true)/=; first by rewrite bnd_simp ltW.
  rewrite -{1}(setU1itv false)/=; first by rewrite bnd_simp.
  rewrite inE/= in_itv/= => -[[->|tab']|->].
  - near=> t' => t'ab.
    rewrite -(subrKA (f a) (lim_fun FF Fc a)).
    rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
    + by rewrite lim_fune2// bound_itvE ltW.
    + rewrite -(subrKA (f t') (f a)).
      rewrite (le_trans (ler_normD _ _))// (splitr (e/2)) lerD//.
      * move: t'ab.
        rewrite -{1}(setU1itv false)/=; first by rewrite bnd_simp ltW.
        rewrite inE/= in_itv/= => -[-> | ].
          by rewrite subrr normr0 ltW// !divr_gt0.
        near: t'.
        move/cvgrPdist_le : lc => /( _ (e/ 2/ 2)).
        rewrite !divr_gt0// => /(_ isT)[e1 e10 eh].
        by exists e1 => // => x ae1x /andP [xa _]; exact: eh.
      * rewrite distrC.
        rewrite mem_setE in t'ab.
        move: (t') t'ab.
        near: f.
        by apply lim_fun_cvg_uniform; rewrite !divr_gt0.
  - near=> t' => t'ab.
    rewrite -(subrKA (f t) (lim_fun FF Fc t)).
    rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
      move: (t) tab.
      near: f.
      by apply: lim_fun_cvg_uniform => //; rewrite divr_gt0.
    rewrite -(subrKA (f t') (f t)).
    rewrite (le_trans (ler_normD _ _))// (splitr (e/2)) lerD//.
      near: t'.
      move /(_ _ tab') : mc => /cvgrPdist_le /=; apply.
      by rewrite !divr_gt0.
    rewrite distrC.
    rewrite mem_setE in t'ab.
    move: (t') t'ab.
    near: f.
    by apply: lim_fun_cvg_uniform; rewrite !divr_gt0.
  - near=> t' => t'ab.
    rewrite -(subrKA (f b) (lim_fun FF Fc b)).
    rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
      by rewrite lim_fune2// bound_itvE ltW.
    rewrite -(subrKA (f t') (f b)).
    rewrite (le_trans (ler_normD _ _))// (splitr (e / 2)) lerD//.
      move: t'ab.
      rewrite -{1}(setUitv1 true)/=; first by rewrite bnd_simp ltW.
      rewrite inE/= in_itv/= => -[ | -> ]; last first.
        by rewrite subrr normr0 ltW// !divr_gt0.
      near: t'.
      move/cvgrPdist_le : rc => /( _ (e / 2 / 2)).
      rewrite !divr_gt0// => /(_ isT)[e1 e10 eh].
      by exists e1 => // x be1x /andP [_ xb]; exact: eh.
    rewrite distrC.
    rewrite mem_setE in t'ab.
    move: (t') t'ab.
    near: f.
    by apply: lim_fun_cvg_uniform; rewrite !divr_gt0.
apply/continuous_within_itvP => //; split.
- move=> t tab; apply/cvgrPdist_le => /= e e0.
  near=> t'.
  have : t' \in `[a, b].
    rewrite inE; apply: subset_itv_oo_cc.
    by near: t'; exact/at_right_in_segment/open_itvcc_subset.
  near: t'.
  apply: H => //.
  by rewrite inE; exact: subset_itv_oo_cc.
- apply/cvgrPdist_le => /= e e0.
  near=> t'.
  have : t' \in `[a,b].
    rewrite inE/= in_itv/=.
    by apply/andP; split; near: t'; [exact: nbhs_right_ge|exact: nbhs_right_le].
  near: t'.
  apply/(cvg_at_right_filter cvg_id)/H => //.
  by rewrite bound_itvE// ltW.
- apply/cvgrPdist_le => /= e e0.
  near=> t'.
  have : t' \in `[a,b].
    rewrite inE /= in_itv/=.
    by apply/andP; split; near: t'; [exact: nbhs_left_ge|exact: nbhs_left_le].
  near: t'.
  apply/(cvg_at_left_filter cvg_id)/H => //.
  by rewrite bound_itvE/= ltW.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ F FF Fc :=
  isContinuous.Build (subspace `[a, b]) W
  (@lim_fun F FF Fc : subspace `[a, b] -> W) (@lim_fun_cont F FF Fc).

Fail Check (V : completeType).

Lemma cvg_V_entourageP (F : set_system `C([a, b] W)) (FF : Filter F) (f : `C[a, b]) :
  F --> f <-> forall A, entourage A ->
              \forall g \near F, {in `[a, b]%R, forall t : R, A (f t, (g : `C[a, b]) t)}.
Proof.
split => [/cvg_entourageP /= Ff A|/=Ff].
  rewrite -entourage_ballE => -[eps eps0 /= H].
  apply: (Ff [set fg : `C[a, b] * `C[a, b] |
    {in `[a, b]%R, forall t : R, A (fg.1 t, fg.2 t)}]).
  exists eps => //.
  rewrite /pseudoMetric_from_normedZmodType.ball /=.
  move=> /= x bx t tab.
  apply: H => /=.
  rewrite -ball_normE /ball/=.
  rewrite -quot_contSeg_fctB//.
  exact: infty_norm_lt.
apply/cvg_entourageP => /= A [e e0 sPA].
have e20 : 0 < e / 2 by rewrite divr_gt0.
have e2 : e / 2 < e by rewrite gtr_pMr// invf_lt1// ltr1n.
near=> g.
apply: sPA => /=.
apply/le_lt_trans/e2.
apply/infty_norm_le2; first exact: ltW.
move => //= t tab.
rewrite quot_contSeg_fctB// ltW//.
suff: ball (f t) (e / 2) (g t) by rewrite -ball_normE.
move: t tab.
near: g.
exact: (Ff [set xy : W * W | ball xy.1 (PosNum e20)%:num xy.2] (entourage_ball _ _)).
Unshelve. all: by end_near. Qed.

Lemma quot_cont_on_segType_cauchy_cvg (F : set_system `C([a, b] W)) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF Fc.
have /(_ _ _)/cauchy_cvg/cvg_app_entourageP cvF :
    forall t, t \in `[a, b]%R ->
    cauchy (fmap (fun h : `C[a, b] => h t) (fun A : set `C[a, b] => nbhs F (fun g => A g))).
  move=> t tab A/=.
  rewrite -entourage_ballE => -[e e0 ee]; rewrite near_simpl -near2E near_map2.
  apply: Fc.
  exists e => //= -[f g].
  move/infty_norm_lt => h.
  apply: ee => /=.
  rewrite -ball_normE /ball_/=.
  by rewrite -quot_contSeg_fctB// h.
apply/cvg_ex; exists (pi `C[a, b] (@lim_fun F FF Fc : continuousSubspaceType `[a, b] [set: W])).
apply/cvg_V_entourageP => /=.
move=> A /= entA.
near=> f.
move=> t tab.
near F => g.
apply: (entourage_split (g t)) => //.
  by rewrite eval_mod_on_itv => //; first by near: g; exact: cvF.
move: (t) (tab); near: g; near: f; apply: nearP_dep; apply: Fc.
rewrite /nbhs /=.
have := entourage_split_ent entA.
rewrite -entourage_ballE => -[e e0 ee].
rewrite -entourage_ballE.
exists e => // -[/= f1 f2].
move/infty_norm_lt => h t tab.
apply: ee => /=.
rewrite -ball_normE /ball_ /=.
rewrite distrC.
by rewrite -quot_contSeg_fctB// h.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Uniform_isComplete.Build `C[a, b]
  quot_cont_on_segType_cauchy_cvg.

Check (`C[a, b] : completeType).
End completeness.
