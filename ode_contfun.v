From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum matrix interval.
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
(*   infty_norm f := infty_norm0 (repr f)                                     *)
(*   quot_contSeg := quotient of continuous functions over a closed interval  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Module ContSeg_zlmodType.
Section contSeg_zlmodtype.
Context {R : realType} {V : normedModType R} (a b : R).

HB.instance Definition _ := GRing.isZmodClosed.Build _ _
  (@cont_on_seg_zmod_closed R V a b).

Fail Check continuousFunType `[a, b] [set: V] : zmodType.

HB.instance Definition _ :=
  [SubChoice_isSubZmodule of continuousFunType `[a, b] [set: V] by <:].

Check continuousFunType `[a, b] [set: V] : zmodType.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (cont_on_seg a b) (@contfun_scaler_closed R V a b).

Fail Check @continuousFunType R V `[a, b] [set: V] : lmodType _.

HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of continuousFunType `[a, b] [set: V] by <:].

Check continuousFunType `[a, b] [set: V] : lmodType _.

End contSeg_zlmodtype.
End ContSeg_zlmodType.

Section submod_contSeg.
Context {R : realType} {V : normedModType R} (a b : R).
Local Notation T := (continuousFunType `[a, b] [set: V]).

(* NB: point does not need to be 0, so rewrite f \_ K explicitly *)
Definition patch_contSeg0 (ab : a <= b) : {pred T} :=
  [pred f : T | patch 0 `[a, b] f == 0].

End submod_contSeg.
Arguments patch_contSeg0 {R} V {a b} ab.

Module ContSeg_submod.
Export ContSeg_zlmodType.

Section submod_definition.
Context {R : realType} {V : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.

Lemma submod_closed_contSeg : submod_closed (patch_contSeg0 V ab).
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

Check (patch_contSeg0 V ab) : zmodClosed _.

End submod_definition.
End ContSeg_submod.

Section contSeg_seminorm.
Context {R : realType} {W : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.
Let K := `[a, b].
Local Notation T := (continuousFunType K [set: W]).

Import ContSeg_zlmodType.

(* NB: require Nmodule properties *)
Lemma infty_norm0_eq0 : infty_norm0 (0 : T) = 0.
Proof.
rewrite /infty_norm0 -(sup1 0); congr sup.
apply: eq_set => /= z.
apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
have [c Kc] := seg_nonempty ab.
by exists c => //; rewrite normr0.
Qed.

(* NB: require Nmodule properties *)
Lemma infty_norm0rMn (f : T) n : infty_norm0 (f *+ n) = infty_norm0 f *+ n.
Proof.
rewrite /infty_norm0 -sup_Mn; last exact: normr_has_sup.
rewrite image_comp/=; congr (sup _).
apply: eq_imagel => z Kz /=; rewrite -normrMn /=.
have /(congr1 (@^~ z)) <- := natmulfctE f n.
congr (normr (_ z)).
(* NB: investigate *)
elim: n f => //= n IH f.
by rewrite !mulrS -IH.
Qed.

Lemma infty_norm0N (f : T) : infty_norm0 (- f) = infty_norm0 f.
Proof.
rewrite /infty_norm0; congr sup; apply: eq_set => /= x0.
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
Context {R : realType} {W : normedModType R} (a b : R).
Hypothesis ab : a <= b.

(*Definition eq_seg (f g : continuousFunType a b) := `[< {in `[a, b], f =1 g} >].

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

Definition quot_contSeg := {quot (@patch_contSeg0 _ W _ _ ab)}.
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

Lemma eqmod_on_itv f g : f = g %[mod T] -> {in `[a, b], f =1 g}.
Proof.
move=> /eqmodP + x xab.
move/set_mem => abfg0.
apply: subr0_eq.
move/(congr1 (fun z => z x)) : abfg0.
by rewrite /patch xab.
Qed.

Lemma eval_mod_on_itv f x : x \in `[a, b] -> (\pi_T f : T) x = f x.
Proof.
move => xab.
apply: (@eqmod_on_itv (repr (\pi_T f)) f) => //.
by rewrite reprK.
Qed.

Lemma quot_contSeg_fctB (f g : T) t : t \in `[a, b] ->
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

Section zmodule_normed.
Context {R : realType} {W : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.
Let K := `[a, b].

Import ContSeg_quot.

Local Notation V := (@quot_contSeg R W a b ab).

Definition infty_norm (f : V) := infty_norm0 (repr f).

Local Open Scope quotient_scope.

Lemma ler_infty_normD (x y : V) :
  infty_norm (x + y) <= infty_norm x + infty_norm y :> R.
Proof.
rewrite /infty_norm/= -sup_sumE; [|exact: normr_has_sup..].
apply: sup_le.
- move=> A -[s sab] <-{A}.
  rewrite /down/=.
  eexists.
  split.
    exists `|repr x s|.
      by exists s.
    exists `|repr y s|.
      by exists s.
    reflexivity.
  suff  -> : repr (x + y) s = repr x s + repr y s by exact: ler_normD.
  suff : repr (x + y) = repr x + repr y %[mod V].
    move=> /eqmod_on_itv ->.
      by [].
    by rewrite inE.
  by rewrite Quotient.pi_add !reprK.
- exact: (normr_has_sup _ _).1.
- split.
  + exists (`|x a| + `|repr y a|)=> /=.
    exists (`|repr x a|) => //; [exists a => //; by rewrite in_itv/= lexx ab|].
    by exists `|repr y a| => //; exists a => //; rewrite bound_itvE.
  + exists (sup [set `|repr x r| | r in K] + sup [set `|repr y r| | r in K]).
    apply ubP => _ [x0 xs] [y0 ys] <-.
    rewrite lerD// ub_le_sup//.
      exact: (normr_has_sup x _).2.
    exact: (normr_has_sup y _).2.
Qed.

Lemma infty_normr0_eq0 (x : V) : infty_norm x = 0 -> x = 0.
Proof.
rewrite /infty_norm /infty_norm0 /= => H.
rewrite -(reprK x) -(reprK 0).
apply/eqquotP.
rewrite Quotient.equivE inE; apply: funext => x0 /=.
rewrite /patch; case : ifPn => // /set_mem in_itv.
rewrite 2!fctE.
have -> : {in K, repr (0 : V) =1 (0 : @continuousFunType R W K setT)}.
- apply/eqmod_on_itv.
  by rewrite reprK /GRing.zero /= /Quotient.zero /= -lock.
- rewrite [LHS]subr0.
  apply/eqP; rewrite -normr_le0.
  have := sup_upper_bound (normr_has_sup x ab).
  rewrite H /ubound /=.
  apply.
  by exists x0.
- by rewrite inE.
Qed.

Lemma infty_normrMn (x : V) n : infty_norm (x *+ n) = infty_norm x *+ n.
Proof.
rewrite /infty_norm -infty_norm0rMn => //.
apply: infty_norm0_itv_eq => r rab.
suff : repr (x *+ n) = repr x *+ n %[mod V] by move=> /eqmod_on_itv ->.
elim n; [rewrite !mulr0n // reprK /GRing.zero /= /Quotient.zero /= -lock // | ].
move => n' IHn'; rewrite reprK !mulrS.
rewrite reprK in IHn'.
rewrite Quotient.pi_add reprK.
by move : IHn' <-.
Qed.

Let infty_norm_pi0 x : infty_norm (\pi_V x) = infty_norm0 x.
Proof.
rewrite /infty_norm /=.
have /eqmod_on_itv Heq : repr (\pi_V x) = x %[mod V] by rewrite reprK.
exact: infty_norm0_itv_eq.
Qed.

Lemma infty_normrN (x : V) : infty_norm (- x) = infty_norm x.
Proof.
rewrite -(reprK x) /GRing.opp /= -Quotient.pi_opp !infty_norm_pi0 /infty_norm /infty_norm0.
congr sup.
apply eq_set => /= x0.
apply propext; split => [[x1 in_itv] | [x1 in_itv]] H; exists x1 =>//.
  by rewrite -normrN.
by rewrite normrN.
Qed.
(* TODO: dev the theory of sup following the theory of ess_sup *)

Fail Check V : normedZmodType R.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R V
  infty_norm ler_infty_normD infty_normr0_eq0 infty_normrMn infty_normrN.

Lemma infty_norm_pi x : `|\pi_V x| = infty_norm0 x.
Proof. by rewrite /Num.norm /= infty_norm_pi0. Qed.

Lemma infty_norm_lt (f : V) e :
  `| f | <  e -> {in `[a, b], forall x : R, `|f x| < e}.
Proof.
rewrite -{1}(reprK f) infty_norm_pi => h x xab.
exact/le_lt_trans/h/infty_norm0_ge.
Qed.

Lemma infty_norm_leP (f : V) e :
  `| f | <=  e <-> {in `[a, b], forall x : R, `|f x| <= e}.
Proof.
split.
  rewrite -{1}(reprK f) infty_norm_pi => h x xab.
  exact/le_trans/h/infty_norm0_ge.
by move => h; by rewrite -(reprK f) infty_norm_pi infty_norm0_le.
Qed.

Check V : normedZmodType R.

Check (pseudoMetric_normed V) : pseudoMetricType R.
Check (pseudoMetric_normed V) : normedZmodType R.

Fail Check (pseudoMetric_normed V) : normedModType R.

End zmodule_normed.

Section quot_continuousFunType_normedtype.
Context {R : realType} {W : normedModType R} {r s : R} (rs : r <= s).

Import ContSeg_quot.

Local Notation V := (@quot_contSeg R W r s rs).

Fail Check (pseudoMetric_normed V) : normedModType R.
HB.instance Definition _ := PseudoMetric.copy V (pseudoMetric_normed V).
HB.instance Definition _ := isPointed.Build V 0.

Lemma is_normZmod_contFunBallType : NormedZmod_PseudoMetric_eq R V.
Proof. by constructor. Qed.

Fail Check V : pseudoMetricNormedZmodType R.

HB.instance Definition _ := is_normZmod_contFunBallType.

Check V : pseudoMetricNormedZmodType R.
Import Quotient.
Open Scope quotient_scope.
Definition cont_scale (k : R) (v : V) : V := \pi_V (k *: repr v).

Let cont_scalerA a b v : cont_scale a (cont_scale b v) = cont_scale (a * b) v.
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
case: piP => f.
by move/eqmod_on_itv => /(_ _ xrs) <-.
Qed.

Let cont_scale1r : left_id 1 cont_scale.
Proof.
move=> v.
rewrite /cont_scale/=.
rewrite [RHS](_ : _ = (\pi_V (repr v))%qT); last by rewrite reprK.
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
have := @eqmod_on_itv _ _ _ _ rs (repr (b + c)) (repr b + repr c).
move=> ->//.
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
  @GRing.Zmodule_isLmodule.Build R V cont_scale cont_scalerA cont_scale1r
  cont_scalerDr cont_scalerDl.

Local Lemma repr_mult l (x : V) a : a \in `[r, s] ->
  repr (l *: x) a = l *: (repr x a).
Proof.
move =>ars.
have : repr (l *: x) = l *: repr x %[mod V].
  by case: piP.
move/(@eqmod_on_itv _ _ _ _ rs (repr (l *: x)) (l *: repr x)).
by move/(_ _ ars).
Qed.

Lemma is_pmnormedZmod_contFunBallType :
  PseudoMetricNormedZmod_Lmodule_isNormedModule R V.
Proof.
constructor => l x.
rewrite /Num.norm/= /infty_norm /infty_norm0 /=.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_sup.
    exists `|repr (l *: x) r|, r => //=.
    by rewrite bound_itvE.
  move=> _/= [a ars] <-.
  rewrite repr_mult; last by rewrite inE.
  rewrite normrZ ler_wpM2l// ub_le_sup//.
    exact: (normr_has_sup _ _).2.
  by exists a.
rewrite -sup_mult => //; last by apply normr_has_sup.
apply sup_le; [ | | by apply normr_has_sup].
  move => _  [_ [x0 x0rs] <- <-].
  exists (`|l| * `|repr x x0|); split=> //=; exists x0.
    by rewrite inE.
  rewrite repr_mult; last by rewrite inE.
  by rewrite normrZ.
exists `|l *: x r|, `|repr x r|.
  by exists r => //=; rewrite bound_itvE.
by rewrite normrZ.
Qed.

HB.instance Definition _ := is_pmnormedZmod_contFunBallType.
End quot_continuousFunType_normedtype.

From mathcomp Require Import all_algebra.
From mathcomp Require Import matrix_topology.

Section completeness.
Context {R : realType} {W : completeNormedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.

Import ContSeg_quot.

Notation V := (@quot_contSeg R W _ _ ab).

Check (V : pseudoMetricType R).
Check (V : normedModType R).

Definition lim_fun (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  subspace `[a, b] -> W :=
  fun t => lim (@^~ t @ F).

Lemma lim_fun_is_fun (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  @isFun (subspace `[a, b]) W `[a, b] [set: W] (@lim_fun F FF Fc).
Proof. by constructor. Qed.

HB.instance Definition _ F FF Fc := (@lim_fun_is_fun F FF Fc).

Lemma lim_fun_cvg_pt (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall e : R, e > 0 -> forall t, t \in `[a,b] ->
  \forall f \near F, `|lim_fun FF Fc t - (f : V) t| <= e.
Proof.
have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :
    forall t : R, t \in `[a,b] ->
      cauchy (fmap (fun h : V => h t) (fun A : set V => nbhs F (fun g => A g))).
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
have cvg_pt (t : R) : t \in `[a,b] ->
    x @[x --> fmap (fun h : V => h t) F] --> lim_fun FF Fc t.
  move=> tab.
  apply/cvg_entourageP.
  exact: cvF.
move=> e e0 t /cvg_pt /cvgrPdist_le.
exact.
Qed.

Lemma lim_fun_cvg_uniform (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall e : R, e > 0 -> \forall f \near F, forall t, t \in `[a, b] ->
  `|lim_fun FF Fc t - (f : V) t| <= e.
Proof.
move=> e e0.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have := Fc _ (entourage_ball V (PosNum e20)).
move => [/= [A B] /= [n1 n2]] H.
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
by move/ltW/infty_norm_leP; exact.
Unshelve. all: by end_near. Qed.

Lemma lim_fun_cont (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  {within `[a, b], continuous (@lim_fun F FF Fc)}.
Proof.
move: ab; rewrite le_eqVlt => /predU1P[<-| ab'].
  by rewrite set_itv1; exact: continuous_subspace1.
have H (e : R) : e > 0 -> forall t, t \in `[a, b] ->
    \forall t' \near t, t' \in `[a, b] ->
    `|lim_fun FF Fc t - lim_fun FF Fc t'| <= e.
  move=> e0 t tab.
  near F => f.
  have lim_fune2 : forall u, u \in `[a, b] -> `|lim_fun FF Fc u - f u| <= e / 2.
    by near: f; apply: lim_fun_cvg_uniform => //; rewrite divr_gt0.
  move/(continuous_within_itvP _ ab') : (@cts_fun _ _ f ) => [mc lc rc].
  move: (tab).
  rewrite -{1}setUitv1/=; last by rewrite bnd_simp ltW.
  rewrite -{1}setU1itv/=; last by rewrite bnd_simp.
  rewrite inE/= in_itv/= => -[[->|tab']|->].
  - near=> t' => t'ab.
    rewrite -(subrKA (f a) (lim_fun FF Fc a)).
    rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
    + by rewrite lim_fune2// inE/= bound_itvE ltW.
    + rewrite -(subrKA (f t') (f a)).
      rewrite (le_trans (ler_normD _ _))// (splitr (e/2)) lerD//.
      * move: t'ab.
        rewrite -{1}setU1itv/=; last by rewrite bnd_simp.
        rewrite inE/= in_itv/= => -[-> | ].
          by rewrite subrr normr0 ltW// !divr_gt0.
        near: t'.
        move/cvgrPdist_le : lc => /( _ (e/ 2/ 2)).
        rewrite !divr_gt0// => /(_ isT)[e1 e10 eh].
        by exists e1 => // => x ae1x /andP [xa _]; exact: eh.
      * rewrite distrC.
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
    move: (t') t'ab.
    near: f.
    by apply: lim_fun_cvg_uniform; rewrite !divr_gt0.
  - near=> t' => t'ab.
    rewrite -(subrKA (f b) (lim_fun FF Fc b)).
    rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
      by rewrite lim_fune2// inE/= bound_itvE ltW.
    rewrite -(subrKA (f t') (f b)).
    rewrite (le_trans (ler_normD _ _))// (splitr (e / 2)) lerD//.
      move: t'ab.
      rewrite -{1}setUitv1/=; last by rewrite bnd_simp ltW.
      rewrite inE/= in_itv/= => -[ | -> ]; last first.
        by rewrite subrr normr0 ltW// !divr_gt0.
      near: t'.
      move/cvgrPdist_le : rc => /( _ (e / 2 / 2)).
      rewrite !divr_gt0// => /(_ isT)[e1 e10 eh].
      by exists e1 => // x be1x /andP [_ xb]; exact: eh.
    rewrite distrC.
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
  by rewrite inE/= bound_itvE// ltW.
- apply/cvgrPdist_le => /= e e0.
  near=> t'.
  have : t' \in `[a,b].
    rewrite inE /= in_itv/=.
    by apply/andP; split; near: t'; [exact: nbhs_left_ge|exact: nbhs_left_le].
  near: t'.
  apply/(cvg_at_left_filter cvg_id)/H => //.
  by rewrite inE /= bound_itvE/= ltW.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ F FF Fc :=
  isContinuous.Build (subspace `[a, b]) W
  (@lim_fun F FF Fc : subspace `[a, b] -> W) (@lim_fun_cont F FF Fc).

Fail Check (V : completeType).

Lemma cvg_V_entourageP  (F : set_system V) (FF : Filter F) (f : V) :
  F --> f <-> forall A, entourage A ->
              \forall g \near F, {in `[a, b], forall t : R, A (f t, (g : V) t)}.
Proof.
split => [/cvg_entourageP /= Ff A|/=Ff].
  rewrite -entourage_ballE => -[eps eps0 /= H].
  apply: (Ff [set fg : V * V| {in `[a, b], forall t : R, A (fg.1 t, fg.2 t)}]).
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
apply: sPA.
apply/le_lt_trans/e2/infty_norm_leP => /= t tab.
rewrite quot_contSeg_fctB// ltW//.
suff: ball (f t) (e / 2) (g t) by rewrite -ball_normE.
move: t tab.
near: g.
exact: (Ff [set xy : W * W | ball xy.1 (PosNum e20)%:num xy.2] (entourage_ball _ _)).
Unshelve. all: by end_near. Qed.

Lemma quot_cont_on_segType_cauchy_cvg (F : set_system V) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF Fc.
have /(_ _ _)/cauchy_cvg/cvg_app_entourageP cvF :
    forall t, t \in `[a, b] ->
    cauchy (fmap (fun h : V => h t) (fun A : set V => nbhs F (fun g => A g))).
  move=> t tab A/=.
  rewrite -entourage_ballE => -[e e0 ee]; rewrite near_simpl -near2E near_map2.
  apply: Fc.
  exists e => //= -[f g].
  move/infty_norm_lt => h.
  apply: ee => /=.
  rewrite -ball_normE /ball_/=.
  by rewrite -quot_contSeg_fctB// h.
apply/cvg_ex; exists (pi V (@lim_fun F FF Fc : continuousFunType `[a, b] [set: W])).
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

HB.instance Definition _ := Uniform_isComplete.Build V
  quot_cont_on_segType_cauchy_cvg.

Check (V : completeType).
End completeness.

(* Section vector_contseg. *)

(* Context {R : realType}. *)
(* Variables  (a b : R). *)
(* Hypothesis ab : a <= b. *)

(* Notation V := (quot_contFunType (seg_nonempty ab) (@segment_compact R _ _)). *)

(* Definition Vn n := {ffun 'I_n -> V}. *)
(* Check V : normedZmodType R. *)
(* Check (V : pseudoMetricType R). *)
(* Check (V : normedModType R). *)
(* Check (Vn 2 : normedZmodType R). *)
(* Check (Vn 2 : pseudoMetricType R). *)
(*  Check (Vn 2 : completeType). *)
(* Fail Check (Vn 2 : normedModType R). *)
(* End vector_contseg. *)
(* (* not neeeded anymore *) *)

(* Section lip_implies_cont. *)
(* Context {R : realType}. *)
(* Local Notation mu := lebesgue_measure. *)
(* Variables (f : R -> R -> R) (t0 t1 : R). *)
(* Hypothesis t01 : t0 < t1. *)
(* Variable k : R. *)
(* Hypothesis k1 : k > 0. *)
(* Variables (u0 : R) (r : {posnum R}). *)
(* Let B := closed_ball u0 r%:num. *)

(* Hypothesis lip2 : {in `[t0, t1]%R, forall x, k.-lipschitz_B (f x)}. *)

(* Lemma cont2 : {in `[t0, t1]%R, forall x, {within B, continuous f x}}. *)
(* Proof. *)
(* move=> x xt01. *)
(* rewrite [B]closed_ball_itv//. *)
(* apply/continuous_within_itvP; first by rewrite ltrD2l gtrN. *)
(* split. *)
(* - move=> y yt01. *)
(*   move: (xt01); have := @lip2 x => /[apply] kfx. *)
(*   rewrite /continuous_at. *)
(*   apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: kfx => /(_ (y, y'))/=. *)
(*     have By : B y. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       exact: subset_itv_oo_cc yt01. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split. *)
(*         near: y'. *)
(*         exists (y - (u0 - r%:num)). *)
(*           by move: yt01; rewrite in_itv/= -subr_gt0 => /andP[]. *)
(*         move=> z/=. *)
(*         rewrite ltr_distlC. *)
(*         by rewrite opprB addrCA subrr addr0 => /andP[/ltW]. *)
(*       near: y'. *)
(*       exists ((u0 + r%:num) - y). *)
(*         by move: yt01; rewrite in_itv/= -(subr_gt0 y) => /andP[]. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC => /andP[_]. *)
(*       by rewrite addrCA subrr addr0 => /ltW. *)
(*    move=> /(_ (conj By By')). *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k). *)
(*     by rewrite divr_gt0//. *)
(*   by move=> z/= => /ltW. *)
(* - apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: (xt01); have := @lip2 x => /[apply]. *)
(*   move=> /(_ (u0 - r%:num, y'))/=. *)
(*     have Bu0r : B (u0 - r%:num). *)
(*       rewrite /B closed_ball_itv//=. *)
(*       by rewrite in_itv/= lexx/= lerD2l gerN. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split => //. *)
(*       near: y'. *)
(*       exists r%:num => //=. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC. *)
(*       rewrite subrK => /andP[_ /ltW + _] => /le_trans; apply. *)
(*       by rewrite lerDl. *)
(*    move=> /(_ (conj Bu0r By')). *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k) => /=. *)
(*     by rewrite divr_gt0//. *)
(*   by move=> z/= => /ltW. *)
(* - apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: (xt01); have := @lip2 x => /[apply]. *)
(*   move=> /(_ (y', u0 + r%:num))/=. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split => //. *)
(*       near: y'. *)
(*       exists r%:num => //=. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC addrK => /andP[/ltW + _ _]. *)
(*       rewrite lerBlDl => /le_trans; apply. *)
(*       by rewrite lerDr. *)
(*     have Bu0r : B (u0 + r%:num). *)
(*       rewrite /B closed_ball_itv//=. *)
(*       by rewrite in_itv/= lexx/= lerD2l andbT gerN. *)
(*   move=> /(_ (conj By' Bu0r)). *)
(*   rewrite distrC. *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k) => /=. *)
(*     by rewrite divr_gt0//. *)
(*   move=> z/= => /ltW. *)
(*   by rewrite distrC. *)
(* Unshelve. all: end_near. Qed. *)

(* End lip_implies_cont. *)
