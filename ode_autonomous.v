From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import archimedean generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
Require Import ode_common ode_contfun ode.
(**md**************************************************************************)
(* # Proofs of properties of autonomous ODEs                                  *)
(*                                                                            *)
(* TODO: fill                                                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.


Section picard_autonomous.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : U -> U) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : k.-lipschitz_B phi.

Definition phi_ (t : R) x := phi x.

Definition is_sol_sym u0 t0 d (sol : R -> U):=
   sol t0 = u0 /\ {in `]t0-d,t0+d[,
        forall x, derivable sol x 1 /\ sol^`() x = phi_ x (sol x)}.

Lemma phi_lip2 a b:  {in `[a, b]%R, forall x, k.-lipschitz_B (phi_ x)}.
Proof. by move => x abx; exact: lip2. Qed.

Lemma phi_cont1 a b : {in B, forall y, {within `[a, b], continuous phi_ ^~ y}}.
Proof. by move => /= x Bx; exact: cst_continuous_subspace. Qed.


Let rho : {posnum R} := (2^-1)%:pos.

Let rho1 : rho%:num < 1.
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Local Lemma cauchy_lipschitz_autofwd a : exists f delta,
  delta > 0 /\ is_sol_on (phi_) u0 a (BLeft (a + delta)) f /\
  {in `[a, a + delta], forall t, closed_ball u0 r%:num (f t)}.
Proof.
have aa1 : a < a + 1 by rewrite ltrDl.
have [d0 [solf cball]] :=
  cauchy_lipschitz_local aa1 k0 (@phi_lip2 a (a + 1)) (@phi_cont1 a (a + 1)) rho1.
exists (@cauchy_lipschitz_local_f R n phi_ a _ k u0 r aa1 k0
  (@phi_lip2 a (a + 1)) (@phi_cont1 a (a + 1)) rho rho1).
by exists (safe_dist phi_ a (a + 1) k u0 r rho).
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
Lemma within_continuous_minus  (f : R -> U) (a b : R) :
  {within `[-b,-a], continuous f} -> {within `[a,b], continuous f \o -%R}.
Proof.
have [ab|ba _ |-> _] := ltgtP a b; last 2 first.
  by rewrite set_itv_ge ?bnd_simp -?ltNge//; exact: continuous_subspace0.
  by rewrite set_itv1; exact: continuous_subspace1.
move/continuous_within_itvP; rewrite ltrN2 => /(_ ab)[cf fb fa].
apply/(continuous_within_itvP _ ab); split.
- move=> t tab.
  apply: (@cvg_comp _ _ _ -%R f); first exact: oppr_continuous.
  by apply: cf; rewrite oppr_itvoo !opprK.
- by rewrite -{1}(opprK a); apply/cvg_at_leftNP; exact: fa.
- by rewrite -{1}(opprK b); apply/cvg_at_rightNP; exact: fb.
Qed.

Local Lemma phi_lip2' a b:  {in `[a, b]%R, forall x, k.-lipschitz_B (-phi_ x)}.
Proof.
move => y _ x B12.
rewrite /= -normrN opprD !opprK /Algebra.opp /=.
exact: (lip2 B12).
Qed.

Local Lemma phi_cont1' a b : {in B, forall y, {within `[a, b], continuous -phi_ ^~ y}}.
Proof. 
  move => y _.     
  move => t.
  apply: continuousN.
  exact: cst_continuous_subspace.
Qed.
(* TODO: extending in both directions should be generalized to non-autonomous *)
Lemma cauchy_lipschitz_autonomous a : exists f delta, delta > 0 /\ is_sol_sym u0 a delta f.
Proof.
have  [fplus [dplus [dplus0 [solplus cplus]]]] := cauchy_lipschitz_autofwd a.
have amin1 : -a < -a + 1 by rewrite ltrDl.
have [dminus0 [solminus cminus]] :=
  cauchy_lipschitz_local amin1 k0
    (@phi_lip2' (-a) (-a + 1)) (@phi_cont1' (-a) (-a + 1)) rho1.

set fminus0 :=
  @cauchy_lipschitz_local_f R n (fun t x => - phi x) (-a) _ k u0 r
    amin1 k0 (@phi_lip2' (-a) (-a + 1)) (@phi_cont1' (-a) (-a + 1)) rho rho1.
set dminus := safe_dist (fun t x => - phi x) (-a) (-a + 1) k u0 r rho.
set fminus := fminus0 \o -%R.
set r2 := (r%:num/2)%:pos.
set r4 := (r%:num/4)%:pos.
have ler4 : r4%:num <= r%:num. 
  by rewrite /r4/= ler_pdivrMr // ler_pMr // lerDl.
have ler42 : r4%:num <= r2%:num. 
  by rewrite /r4/r2/= ler_pdivrMr// -mulrA ler_pMr // ler_pdivlMl // mulr1 lerD // lerDl.
have adplus : a < a + dplus by rewrite ltrDl dplus0.
have cfplus := And33 solplus.
rewrite closure_neitv_oo in cfplus; last by rewrite ltrDl.
have [rpos hropos] := ode.continuous_confined (a:=a) (b:=a + dplus) (u0:=u0) r4 adplus cfplus (And31 solplus).
have amind : -a < -a + dminus by rewrite ltrDl dminus0.
have cfminus' := And33 solminus.
rewrite closure_neitv_oo in cfminus'; last by rewrite ltrDl.
have cfminus : {within `[a-dminus, a], continuous fminus}.
  rewrite /fminus.
  apply: within_continuous_minus.
  apply /continuous_subspaceW/cfminus'.
  apply: subset_itvl.
  rewrite -/dminus.
  by rewrite bnd_simp/= opprD opprK.
have [rneg hrneg] := ode.continuous_confined (a:=-a) (b:=-a + dminus) (u0:=u0) r4 amind cfminus' (And31 solminus).
set dboth := Num.min dplus (Num.min dminus (Num.min rneg%:num rpos%:num)).
have dboth0 : 0 < dboth.
  rewrite lt_min  dplus0 //= lt_min dminus0 //=.
pose f := patch fplus `[a - dboth, a] fminus.
set uneg := f (a - dboth).
have Buneg : closed_ball uneg (r%:num/2) `<=` closed_ball u0 r%:num.
  rewrite /uneg/f patch_in/f/=;last first.
    by rewrite inE/=in_itv/= gerBl lexx ltW. 
  move => /=x xb.
  apply: (closed_ball_split _ xb) => //.
  suff : fminus (a - dboth) \in closed_ball u0 (r%:num/4).
    rewrite !inE.
    apply le_closed_ball.
    rewrite ler_pdivrMr//= -mulrA /=ler_peMr//.
    by rewrite ler_pdivlMl //= mulr1 ltW // ler_ltD //= ltrDl.
  apply hrneg.
    rewrite inE/=in_itv/= opprB lerDr ltW //= addrC lerD //.
    by rewrite /dboth ge_min; do 2 (apply /orP; right; rewrite ge_min);apply /orP;left.
have f01intersect : fminus a = fplus a.
  by rewrite /fminus/= (And31 solminus) (And31 solplus).
have fa : f a = u0.
   rewrite /f patch_in /fminus /=. 
   apply solminus.
   by rewrite inE/=in_itv/= lexx gerBl ltW.
set B' := closed_ball uneg (r2%:num).
have lip2' : k.-lipschitz_B' phi.
  move => /= [x1 x2] [Bx1 Bx2].
  apply lip2.
  by split;apply Buneg.
have contf_minus :   {within `[a - dboth, a], continuous fminus}.
  apply /continuous_subspaceW/cfminus.
  apply: subset_itvr.
  by rewrite bnd_simp /= lerD //= lerNr opprK ge_min; apply /orP;right; rewrite ge_min lexx.

have contf_plus :   {within `[a, a+dboth], continuous fplus}.
  apply /continuous_subspaceW/cfplus.
  apply: subset_itvl.
  by rewrite bnd_simp /= lerD //= ge_min lexx.
have contf :   {within `[a - dboth, (a + dboth)%E], continuous f}.
  apply : within_continuous_patch => //.
  by rewrite gtrBl.
  by rewrite ltrDl.
have r42 : r4%:num = (r2%:num / 2).
  rewrite /r4/r2/=.
  rewrite -mulrA.
  apply congr2 => //.
  by rewrite -invfM -natrM.
have fc : {in `[a-dboth, (a + dboth)], forall t : R,  closed_ball (fminus (a - dboth)) r2%:num (f t)}.
  move => t tad.
  rewrite /f/=/patch/=.
   have : (closed_ball (fminus (a-dboth)) (r4%:num)) u0.
     suff:  (fminus (a-dboth)) \in closed_ball u0 (r4%:num). 
       by rewrite inE/= !closed_ballE/closed_ball_/= // distrC .
     apply: hrneg.
     rewrite !inE/=!in_itv/= lerNr lerNl opprD !opprK gerBl ltW //= lerB //.
     by do 2 (rewrite ge_min;apply /orP;right); rewrite ge_min lexx.
  rewrite r42.
  move => c1.
  case : ifP => ht.
  - have  : (fminus t) \in closed_ball u0 (r4%:num).
     apply: hrneg.
     move : ht.
     rewrite !inE/=!in_itv/= lerNr lerNl opprD !opprK => /andP[h1 ->//=].
     apply: (le_trans _ h1).
     by rewrite lerB //; do 2 (rewrite ge_min;apply /orP;right); rewrite ge_min lexx.
   rewrite inE.
   rewrite !r42.
   move => c2.
   apply: (closed_ball_split _ c2) =>//.
  - have  : (fplus t) \in closed_ball u0 (r4%:num).
     have ht' : t \in `[a, a + dboth].
       have := tad.
       rewrite !inE /=!in_itv/= => /andP[h1 ->]; apply /andP; split => //.
       have [hat | hat] := lerP a t => //.
       rewrite -ht.
       by rewrite inE/=in_itv/= h1//= ltW.
     apply: hropos.
       move : ht'.
       rewrite !inE/= !in_itv/= => /andP[-> h1//=].
       apply: (le_trans h1).
       by rewrite lerD //;  do 3 (rewrite ge_min;apply /orP;right).
     rewrite inE.
     rewrite !r42.
     move => c2.
     apply: (closed_ball_split _ c2) =>//.
exists f, dboth.
split => //.
suff  h: is_sol_on phi_ (f (a-dboth)) (a-dboth) (BLeft (a+dboth)) f.
  by split => //;apply:(And32 h).  

have kn0 : k != 0 by apply lt0r_neq0.
apply /(integral_sol_iff_sol (r := r2) kn0) => //.
  by rewrite ler_ltD // gtrN.
  move => x _; exact: cst_continuous_subspace.
  move => _ [t tp] <-.
  rewrite {1}/f patch_in;last first.
    by rewrite inE/=in_itv/= lexx //= gerBl ltW.
  by apply fc; rewrite inE.
apply solution_extends => //.
- by rewrite gtrBl.
- apply : (within_continuous_lipschitz _ kn0 (u0 := u0) (r:=r)).
    exact: contf_minus.
    by move => x _.
    move => x _ ;exact: cst_continuous_subspace.
    move => _ [/= t' tp] <-.
    apply (le_closed_ball (e1:=r4%:num)) => //.
    suff : (fminus t') \in closed_ball u0 r4%:num by rewrite inE.
    apply hrneg.
    move : tp.
    rewrite in_itv/=inE/=in_itv/= lerNl opprK => /andP[h0 ->//=].
    rewrite lerNl opprD opprK //=.
    apply: (le_trans _ h0).
    by rewrite lerB //; do 2 (rewrite ge_min;apply /orP;right); rewrite ge_min lexx.
- apply : (within_continuous_lipschitz _ kn0 (u0 := u0) (r:=r)).
    exact: contf_plus.
    by move => x _.
    move => x _ ;exact: cst_continuous_subspace.
    move => _ [/= t' tp] <-.
    apply (le_closed_ball (e1:=r4%:num)) => //.
    suff : (fplus t') \in closed_ball u0 r4%:num by rewrite inE.
    apply hropos.
    move : tp.
    rewrite in_itv/=inE/=in_itv/= => /andP[-> h0 //=].
    apply: (le_trans h0).
    by rewrite lerD //=; do 3 (rewrite ge_min;apply /orP;right).
- apply /(integral_sol_iff_sol (r:=r2) kn0).
  + by rewrite gtrBl.
  + move=>x _; exact: lip2'.
  + move=>x _; exact: cst_continuous_subspace.
  + by [].
  + move => _ [t tp] <-.
    rewrite {1}/f patch_in;last first.
      by rewrite inE/=in_itv/= lexx //= gerBl ltW.
    have tin : t \in `[a-dboth, a+dboth].
      move : tp.
      rewrite !inE/=!in_itv/= => /andP[-> h1//=].
      by apply (le_trans h1); rewrite lerDl ltW.
    have := fc _ tin.
    rewrite {1}/f patch_in; last by rewrite inE.
    apply.
    split.
      * by rewrite /f patch_in; last rewrite inE/=in_itv/= lexx //= gerBl ltW.
      *  move => t tad.
         case : (And32 solminus (-t)).
           move : tad.
           rewrite -/dminus !inE/=!in_itv/= ltrNr ltrNl opprD !opprK => /andP[h1 ->//=].
           apply: (le_lt_trans _ h1).
           by rewrite lerD// lerNl opprK; rewrite ge_min;apply /orP;right;rewrite ge_min lexx.
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
      by rewrite mulrN1 opprK.
      apply h1.
      by move /derivable_mxP: h1.
      * by rewrite closure_neitv_oo; last rewrite gtrBl.
- apply /(integral_sol_iff_sol (r:=r2) kn0).
  + by rewrite ltrDl.
  +  move=>x _.
     rewrite /fminus/=.
     rewrite (And31 solminus).
     move => [x1 x2] [ Bx1 Bx2].
     apply: lip2.
     split => /=.
     rewrite /B.
     apply: (le_closed_ball _ Bx1). 
     by rewrite ler_pdivrMr // ler_pMr // lerDr.
     apply: (le_closed_ball _ Bx2). 
     by rewrite ler_pdivrMr // ler_pMr // lerDr.
  + move=>x _; exact: cst_continuous_subspace.
  + by [].
  + move => _ [t tp] <-.
    rewrite /fminus /=(And31 solminus).
    apply : (le_closed_ball ler42).
    suff :  fplus t \in closed_ball u0 r4%:num by rewrite inE.
    apply hropos.
    move : tp.
    rewrite !inE/=!in_itv/= => /andP[-> h0]//=.
    apply (le_trans h0).
    by rewrite lerD //=; do 3 (rewrite ge_min;apply /orP;right).
    rewrite /fminus /=(And31 solminus).
    split.
    apply solplus.
    move => t tad.
    apply solplus.
    move : tad.
    rewrite !inE/=!in_itv/= => /andP[-> h0]//=.
    apply (lt_le_trans h0).
    by rewrite lerD //= ge_min lexx. 
    apply /continuous_subspaceW/cfplus.
    rewrite closure_neitv_oo;last by rewrite ltrDl.
    apply subset_itvl.
    rewrite bnd_simp /=.
    by rewrite lerD //= ge_min lexx.
Qed.
End picard_autonomous.

Definition locally_lipschitz {R : realType} n (U := 'rV[R]_n) (phi : U -> U) :=
 forall x, exists r k : {posnum R}, k%:num.-lipschitz_(closed_ball x r%:num) phi.

(* Section locally_lipschitz. *)
(* Context {R : realType} {n : nat}. *)
(* Notation U := 'rV[R]_n. *)
(* Variables phi : U -> U. *)

(* Hypothesis phi_locally_lipschitz : locally_lipschitz phi. *)

(* Theorem cauchy_lipschitz_ll u0 a : exists f delta r, *)
(*   delta > 0 /\ is_sol_sym phi u0 a (a + delta) f /\ *)
(*   {in `[a, a + delta], forall t, closed_ball u0 r (f t)}. *)
(* Proof. *)
(* have [/= r [k lip]] := phi_locally_lipschitz u0. *)
(* have [//|f [delta [delta_ft0 [solf cball]]]] := cauchy_lipschitz_autonomous  _ lip a. *)
(* by exists f, delta, r%:num. *)
(* Qed. *)

(* End locally_lipschitz. *)

Section uniqueness.
Context {R : realType} {n : nat} (a b : R).
Notation U := 'rV[R]_n.
Variable phi : U -> U.
Hypothesis ab : a < b.

Hypothesis phi_locally_lipschitz : locally_lipschitz phi.

Variables (u0 : U) (f : R -> U) (f' : R -> U).
Hypothesis sol1 : is_sol_on (fun=> phi) u0 a (BLeft b) f.
Hypothesis sol2 : is_sol_on (fun=> phi) u0 a (BLeft b) f'.

Lemma locally_unique_extends t : a <= t < b -> f' t = f t ->
  exists Delta : {posnum R}, {in `[t, t + Delta%:num], f =1 f'}.
Proof.
move=> /andP[ta tb] eq.
have taab : `[t, b] `<=` `[a, b].
  by move=> ?/=; apply: subset_itvr; rewrite bnd_simp.
have [r [k L]] := phi_locally_lipschitz (f t).
have cf0 : {within `[t, b], continuous f}.
  have := And33 sol1.
  rewrite closure_neitv_oo//; exact: continuous_subspaceW.
have cf'0 : {within `[t, b], continuous f'}.
  have := And33 sol2.
  by rewrite closure_neitv_oo//; exact: continuous_subspaceW.
have sol10 : is_sol_on (fun => phi) (f t) t (BLeft b) f.
  split => //; last by rewrite closure_neitv_oo.
  move=> t0 tab.
  apply sol1.
  by move: tab; rewrite !inE/=; apply: subset_itvr; rewrite bnd_simp.
have sol20 : is_sol_on (fun => phi) (f t) t (BLeft b) f'.
  split => //; last by rewrite closure_neitv_oo.
  move=> t0 tab.
  apply sol2.
  by move: tab; rewrite !inE/=; apply: subset_itvr; rewrite bnd_simp.
have lip20 : {in `[t, b]%R, forall x,  k%:num.-lipschitz_(closed_ball (f t) r%:num) phi}.
  by move => ? _; apply L.
have k0 : 0 < k%:num by [].
have cont1 : {in closed_ball (f t) r%:num,
  forall y : 'rV_n, {within `[t, b], continuous fun=> phi y}}.
  by move => y _; exact: cst_continuous_subspace.
have [D [P1 P2]] := initial_solution_unique tb k0 lip20 cont1 cf0 sol10 cf'0 sol20.
by exists D.
Qed.

Lemma solution_unique :  {in `[a, b], f =1 f'}.
Proof.
set E := [set t | t \in `[a, b]%R /\ {in `[a, t], f =1 f'}].
suff : E b by case.
have Enonempty : E !=set0.
  exists a; split; first by rewrite in_itv/= lexx ltW.
  rewrite set_itv1 => t; rewrite inE/= => ->.
  by rewrite (And31 sol1) (And31 sol2).
have mon c : E c -> forall c', a <= c' <= c -> E c'.
  move=> -[+ h c'] /andP[ac' cc'].
  rewrite in_itv/= => /andP[ac cb].
  split.
    by rewrite in_itv/= ac' (le_trans cc').
  move => t tac'.
  apply: h.
  by move: tac'; rewrite !inE/=; apply: subset_itvl; rewrite bnd_simp.
have monC c c' : a <= c' -> E c -> ~ E c' -> c < c'.
  move => ac' Ec nEc'.
  rewrite ltNge; apply/negP => c'c.
  apply/nEc'/(mon c) => //.
  by rewrite ac'.
have [hP|hP] := lem (has_sup E); last first.
  have /(has_supPn Enonempty) := hP.
  move=> /(_ b)[x Ex bx].
  apply/(mon x) => //.
  by rewrite !ltW.
have Eclosed : closed E.
  rewrite closedE/= => p pn.
  suff : forall x, ~ E x -> \forall y \near x, ~ E y.
    move => H.
    apply/not_notP => Ec.
    apply: pn.
    exact: H.
  move=> x Ex1.
  have [xab|xnab] := boolP (x \in `[a, b]%R); last first.
    suff : \forall y \near x, ~ (y \in `[a,b]%R).
      move=> h.
      near=> y.
      rewrite not_andP;left.
      near: y.
      exact: h.
    move: xnab; rewrite in_itv/= negb_and/= -!ltNge => /orP[xa|xb].
      near=> y.
      apply/negP; rewrite in_itv/= negb_and/= -!ltNge; apply/orP; left.
      by near: y; exact: lt_nbhsl.
    near=>y.
    apply/negP.
    rewrite in_itv/=negb_and/= -!ltNge; apply/orP; right.
    by near: y; exact: lt_nbhsr.
  rewrite not_andP in Ex1.
  case: Ex1 => // {}Ex1.
  have [t Et] : exists t, t \in `[a, x] /\ ~ (f t = f' t).
     rewrite not_existsP => h.
     apply Ex1 => t tax.
     have := h t.
     by rewrite not_andP => -[//|/contrapT].
  have [xt|xt]:= eqVneq x t.
    subst t.
    set g := fun x => `|f x - f' x|.
    have contg : {within `[a,b], continuous g}.
      apply: (within_continuous_comp_norm (ltW ab)) => t.
      apply: continuousB.
      - have := And33 sol1.
        rewrite closure_neitv_oo//.
        exact.
      - have := And33 sol2.
        rewrite closure_neitv_oo//.
        exact.
    have g0x : g x > 0.
      rewrite normr_gt0 subr_eq0.
      by apply/eqP; case: Et.
    have g0 t : t \in `[a, b]%R -> g t > 0 -> ~  {in `[a, t], f =1 f'}.
      move => tab gt Et'.
      move : gt.
      suff -> : g t = 0 by rewrite ltxx.
      apply/normr0P.
      rewrite Et' ?subrr//.
      by move: tab; rewrite inE/= !in_itv/= lexx => /andP[->].
    suff hgx: \forall y \near x^'-, 0 < g y.
      near=>y.
      have [yx|xy Ey] := ltP y x; last first.
        have := mon _ Ey x.
        move: xab.
        by rewrite /=in_itv/= xy => /andP[-> _] // /(_ isT)[].
      apply/not_andP.
      rewrite -implyE => yab.
      apply g0 => //.
      by move: yx; near: y.
    apply: (@cvgr_gt R R (nbhs x^'-) _ g (g x)) => //.
    have xa : a < x.
      rewrite ltNge.
      apply: contra_notN Ex1.
      move: xab; rewrite in_itv/= => /andP[+ _] ax.
      move/(conj ax) => /andP; rewrite -eq_le => /eqP ->.
      rewrite set_itv1/= => y; rewrite inE/= => ->.
      by rewrite (And31 sol1) (And31 sol2).
    have /(continuous_within_itvP _ ab) := contg => -[h1 _ h2].
    move: xab; rewrite in_itv/= => /andP[_ ].
    rewrite le_eqVlt => /predU1P[-> //|xb].
    apply/cvg_at_left_filter/h1.
    by rewrite in_itv/= xb xa.
  have xt' : t < x.
    case: Et; rewrite inE/=in_itv/= => /andP[_ ].
    by rewrite le_eqVlt eq_sym (negbTE xt) .
  near=> y.
  move => Ey.
  have : ~ E t.
    rewrite not_andP.
    right.
    move=> /(_ t).
    case: Et; rewrite !inE/= !in_itv/= => /andP[-> _/=].
    by rewrite lexx => /[swap] => /(_ isT).
  have ta : a <= t.
    by case: Et; rewrite inE/= in_itv/= => /andP[].
  move/(monC y t ta Ey).
  apply/negP; rewrite -leNgt.
  by near: y; exact: nbhs_ge.
have supE : E (sup E).
  rewrite {1}(closure_id E).1 //.
  apply: closure_sup => //.
  by apply hP.
have sup_itv : a <= sup E.
  apply sup_upper_bound => //.
  split; first by rewrite in_itv/= lexx ltW.
  move => t.
  rewrite set_itv1 inE/= => ->.
  by rewrite (And31 sol1) (And31 sol2).
have supeq : f' (sup E) = f (sup E).
  apply/esym; apply supE.
  by rewrite inE/= in_itv/= lexx sup_itv.
have [h|h] := leP b (sup E).
  apply: (mon _ supE) => //.
  by rewrite (ltW ab).
have [|Delta Hdelta] := locally_unique_extends _ supeq; first by apply/andP.
have Delta0 : 0 < Delta%:num by [].
suff : Num.min b (sup E + Delta%:num) <= sup E.
  rewrite ge_min => /orP[bE|].
    by have := lt_le_trans h bE; rewrite ltxx.
  by rewrite gerDl leNgt Delta0.
apply: sup_upper_bound => //.
split.
  by rewrite in_itv/= le_min (ltW ab)/= ler_wpDr//= ge_min lexx.
move=> t.
rewrite inE/= in_itv/= => -/andP[t1 t2].
have [ht|ht] := leP t (sup E).
  by apply supE; rewrite inE/= in_itv/= t1 ht.
by apply: Hdelta; rewrite inE/= in_itv/= ltW// (le_trans t2)// ge_min lexx orbT.
Unshelve. all: by end_near. Qed.

End uniqueness.
