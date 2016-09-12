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

Require Import aux angle euclidean3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

(* OUTLINE:
 1. section vec_angle
    definition of vec_angle (restricted to [0,pi])
    (sample lemma: multiplication by a O_3[R] matrix preserves vec_angle)
 2. section colinear
    (simple definition using crossmul, but seemed clearer to me to have a dedicated definition)
 3. section normalize
    section axial_normal_decomposition.
    (easy definitions to construct frames out of already available points/vectors)
 4. section axial_normal_decomposition.
    axialcomp, normalcomp
 5. section line
*)

Lemma sqr_normr_cossin (R : rcfType) (v :'rV[R]_2) :
  norm v = 1 -> {a | v``_0 = cos a /\ v``_1 = sin a}.
Proof.
move=> v1.
have {v1}v1 : (`| v 0 0 +i* v 0 1 | = 1)%C.
 by rewrite normc_def /= -(sum2E (fun i => v``_i ^+ 2)) -sqr_norm sqrtr_sqr v1 normr1.
exists (arg (v 0 0 +i* v 0 1)%C).
rewrite /cos /sin expi_arg //; last by rewrite -normr_eq0 v1 oner_neq0.
by rewrite v1 divr1.
Qed.

Section vec_angle.

Variable (R : rcfType).
Implicit Types u v : 'rV[R]_3.

Definition vec_angle v w : angle R := arg (v *d w +i* norm (v *v w))%C.

Lemma vec_anglev0 v : vec_angle v 0 = vec_angle 0 0.
Proof. by rewrite /vec_angle 2!dotmulv0 2!crossmulv0. Qed.

Lemma vec_angle0v v : vec_angle 0 v = vec_angle 0 0.
Proof. by rewrite /vec_angle 2!dotmul0v 2!crossmul0v. Qed.

Definition vec_angle0 := (vec_anglev0, vec_angle0v).

Lemma vec_angleC v w : vec_angle v w = vec_angle w v.
Proof. by rewrite /vec_angle dotmulC crossmulC normN. Qed.

Lemma vec_anglevZ u v k : 0 < k -> vec_angle u (k *: v) = vec_angle u v.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0 k0]; first by rewrite scaler0 !vec_angle0.
by rewrite /vec_angle dotmulvZ linearZ normZ ger0_norm ?ltrW // complexZ argZ.
Qed.

Lemma vec_angleZv u v (k : R) : 0 < k -> vec_angle (k *: u) v = vec_angle u v.
Proof. move=> ?; rewrite vec_angleC vec_anglevZ; by [rewrite vec_angleC|]. Qed.

Lemma vec_anglevZN u v k : k < 0 -> vec_angle u (k *: v) = vec_angle u (- v).
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite 2!vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0 k0]; first by rewrite scaler0 oppr0 vec_angle0.
rewrite /vec_angle dotmulvZ linearZ /= normZ ltr0_norm //.
by rewrite mulNr complexZ argZ_neg // opp_conjc dotmulvN crossmulvN normN.
Qed.

Lemma vec_angleZNv u v k : k < 0 -> vec_angle (k *: u) v = vec_angle (- u) v.
Proof. move=> ?; rewrite vec_angleC vec_anglevZN; by [rewrite vec_angleC|]. Qed.

Lemma vec_anglevv u : u != 0 -> vec_angle u u = 0.
Proof.
move=> u0.
rewrite /vec_angle /= crossmulvv norm0 complexr0 dotmulvv arg_Re ?arg1 //.
by rewrite ltr_neqAle sqr_ge0 andbT eq_sym sqrf_eq0 norm_eq0.
Qed.

Lemma cos_vec_angleNv v w : v != 0 -> w != 0 ->
  cos (vec_angle (- v) w) = - cos (vec_angle v w).
Proof.
move=> a0 b0.
rewrite /vec_angle /cos crossmulNv normN expi_arg; last first.
  rewrite eq_complex /= negb_and.
  case/boolP : (v *d w == 0) => ab; last by rewrite dotmulNv oppr_eq0 ab.
  by rewrite dotmulNv (eqP ab) oppr0 eqxx /= norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite expi_arg; last first.
  rewrite eq_complex /= negb_and.
  by case/boolP : (_ == 0) => ab //=; rewrite norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite (_ : `|- v *d w +i* _| = `|v *d w +i* norm (v *v w)|)%C; last first.
  by rewrite 2!normc_def /= dotmulNv sqrrN.
by rewrite /= mul0r oppr0 mulr0 subr0 expr0n /= addr0 subr0 dotmulNv mulNr.
Qed.

Lemma cos_vec_anglevN v w : v != 0 -> w != 0 ->
  cos (vec_angle v (- w)) = - cos (vec_angle v w).
Proof.
move=> a0 b0.
rewrite /vec_angle /cos crossmulC crossmulNv opprK dotmulvN.
rewrite [in LHS]expi_arg; last first.
  rewrite eq_complex /= negb_and.
  case/boolP : (v *d w == 0) => vw; rewrite oppr_eq0 vw //=.
  by rewrite norm_eq0 dotmul_eq0_crossmul_neq0 // dotmulC.
rewrite expi_arg; last first.
  rewrite eq_complex /= negb_and.
  by case/boolP : (_ == 0) => ab //=; rewrite norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite (_ : `| _ +i* norm (w *v _)| = `|v *d w +i* norm (v *v w)|)%C; last first.
  by rewrite 2!normc_def /= sqrrN crossmulC normN.
by rewrite /= mul0r oppr0 mulr0 expr0n /= addr0 subr0 mulr0 subr0 mulNr.
Qed.

Lemma sin_vec_angle_ge0 u v (u0 : u != 0) (v0 : v != 0) : 
  0 <= sin (vec_angle u v).
Proof.
rewrite /sin /vec_angle expi_arg /=; last first.
  rewrite eq_complex /= negb_and norm_eq0.
  case/boolP : (u *d v == 0) => //=.
  move/dotmul_eq0_crossmul_neq0; by apply.
rewrite !(mul0r,oppr0,mulr0,add0r,expr0n,addr0) mulr_ge0 // ?norm_ge0 //.
by rewrite divr_ge0 // ?sqrtr_ge0 // sqr_ge0.
Qed.

Lemma sin_vec_anglevN u v : sin (vec_angle u (- v)) = sin (vec_angle u v).
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite oppr0 !vec_angle0.
rewrite /vec_angle dotmulvN crossmulvN normN.
case/boolP : (u *d v == 0) => [/eqP ->|uv]; first by rewrite oppr0.
rewrite /sin !expi_arg /=.
  by rewrite !(mul0r,oppr0,mulr0,add0r,expr0n,addr0,sqrrN).
by rewrite eq_complex /= negb_and uv orTb.
by rewrite eq_complex /= negb_and oppr_eq0 uv.
Qed.

Lemma sin_vec_angleNv u v : sin (vec_angle (- u) v) = sin (vec_angle u v).
Proof. by rewrite vec_angleC [in RHS]vec_angleC [in LHS]sin_vec_anglevN. Qed.

Lemma polarization_identity v u :
  v *d u = 1 / 4%:R * (norm (v + u) ^+ 2 - norm (v - u) ^+ 2).
Proof.
apply: (@mulrI _ 4%:R); first exact: pnatf_unit.
rewrite [in RHS]mulrA div1r divrr ?pnatf_unit // mul1r.
rewrite -2!dotmulvv dotmulD dotmulD mulr_natl (addrC (v *d v)).
rewrite (_ : 4 = 2 + 2)%N // mulrnDr -3![in RHS]addrA; congr (_ + _).
rewrite opprD addrCA 2!addrA -(addrC (v *d v)) subrr add0r.
by rewrite addrC opprD 2!dotmulvN dotmulNv opprK subrK -mulNrn opprK.
Qed.

Lemma dotmul_cos u v : u *d v = norm u * norm v * cos (vec_angle u v).
Proof.
wlog /andP[u0 v0] : u v / (u != 0) && (v != 0).
  case/boolP : (u == 0) => [/eqP ->{u}|u0]; first by rewrite dotmul0v norm0 !mul0r.
  case/boolP : (v == 0) => [/eqP ->{v}|v0]; first by rewrite dotmulv0 norm0 !(mulr0,mul0r).
  apply; by rewrite u0.
rewrite /vec_angle /cos. set x := (_ +i* _)%C.
case/boolP  : (x == 0) => [|x0].
  rewrite eq_complex /= => /andP[/eqP H1 H2].
  exfalso.
  move: H2; rewrite norm_eq0 => /crossmul0_dotmul/esym.
  rewrite H1 expr0n (_ : (_ == _)%:R = 0) // => /eqP.
  by rewrite 2!dotmulvv mulf_eq0 2!expf_eq0 /= 2!norm_eq0 (negbTE u0) (negbTE v0).
case/boolP : (u *d v == 0) => uv0.
  by rewrite (eqP uv0) expi_arg //= (eqP uv0) !mul0r -mulrN opprK mulr0 addr0 mulr0.
rewrite expi_arg //.
rewrite normc_def Re_scale; last first.
  rewrite sqrtr_eq0 -ltrNge -(addr0 0) ltr_le_add //.
    by rewrite exprnP /= ltr_neqAle sqr_ge0 andbT eq_sym -exprnP sqrf_eq0.
  by rewrite /= sqr_ge0.
rewrite /=.
rewrite norm_crossmul' addrC subrK sqrtr_sqr ger0_norm; last first.
  by rewrite mulr_ge0 // norm_ge0.
rewrite mulrA mulrC mulrA mulVr ?mul1r //.
by rewrite unitrMl // unitfE norm_eq0.
Qed.

Lemma dotmul0_vec_angle u v : u != 0 -> v != 0 ->
  u *d v = 0 -> `| sin (vec_angle u v) | = 1.
Proof.
move=> u0 v0 /eqP.
rewrite dotmul_cos mulf_eq0 => /orP [ | /eqP/cos0sin1 //].
by rewrite mulf_eq0 2!norm_eq0 (negbTE u0) (negbTE v0).
Qed.

Lemma triine u v : 
  (norm u * norm v * cos (vec_angle u v)) *+ 2 <= norm u ^+ 2 + norm v ^+ 2.
Proof.
move/eqP: (sqrrD (norm u) (norm v)); rewrite addrAC -subr_eq => /eqP <-.
rewrite ler_subr_addr -mulrnDl -{2}(mulr1 (norm u * norm v)) -mulrDr.
apply (@ler_trans _ (norm u * norm v * 2%:R *+ 2)).
  rewrite ler_muln2r /=; apply ler_pmul => //.
    by apply mulr_ge0; apply norm_ge0.
    rewrite -ler_subl_addr add0r; move: (cos_max (vec_angle u v)).
    by rewrite ler_norml => /andP[].
  rewrite -ler_subr_addr {2}(_ : 1 = 1%:R) // -natrB //. 
  move: (cos_max (vec_angle u v)); by rewrite ler_norml => /andP[].
rewrite sqrrD mulr2n addrAC; apply ler_add; last by rewrite mulr_natr.
by rewrite -subr_ge0 addrAC mulr_natr -sqrrB sqr_ge0.
Qed.

Lemma normB u v : norm (u - v) ^+ 2 =
  norm u ^+ 2 + norm u * norm v * cos (vec_angle u v) *- 2 + norm v ^+ 2.
Proof.
rewrite /norm dotmulD {1}dotmulvv sqr_sqrtr; last first.
  rewrite !dotmulvN !dotmulNv opprK dotmulvv dotmul_cos.
  by rewrite addrAC mulNrn subr_ge0 triine.
rewrite sqr_sqrtr ?le0dotmul // !dotmulvv !sqrtr_sqr normN dotmulvN dotmul_cos.
by rewrite ger0_norm ?norm_ge0 // ger0_norm ?norm_ge0 // mulNrn.
Qed.

Lemma normD u v : norm (u + v) ^+ 2 =
  norm u ^+ 2 + norm u * norm v * cos (vec_angle u v) *+ 2 + norm v ^+ 2.
Proof.
rewrite {1}(_ : v = - - v); last by rewrite opprK.
rewrite normB normN.
case/boolP: (u == 0) => [/eqP ->|u0].
  by rewrite !(norm0,expr0n,add0r,vec_angle0,mul0r,mul0rn,oppr0).
case/boolP: (v == 0) => [/eqP ->|v0].
  by rewrite !(norm0,expr0n,add0r,vec_angle0,mulr0,mul0r,mul0rn,oppr0).
by rewrite [in LHS]cos_vec_anglevN // mulrN mulNrn opprK.
Qed.

(*Lemma normD a b : norm (a + b) =
  Num.sqrt (norm a ^+ 2 + norm a * norm b * cos (vec_angle a b) *+ 2 + norm b ^+ 2).
Proof.
rewrite /norm dotmulD {1}dotmulvv sqr_sqrtr ?le0dotmul //.
by rewrite sqr_sqrtr ?le0dotmul // (dotmul_cos a b).
Qed.

Lemma normB a b : norm (a - b) =
  Num.sqrt (norm a ^+ 2 + norm a * norm b * cos (vec_angle a b) *- 2 + norm b ^+ 2).
Proof.
rewrite /norm dotmulD {1}dotmulvv sqr_sqrtr ?le0dotmul //.
rewrite sqr_sqrtr ?le0dotmul // !dotmulvv !sqrtr_sqr normN dotmulvN dotmul_cos.
by rewrite ger0_norm ?norm_ge0 // ger0_norm ?norm_ge0 // mulNrn.
Qed.*)

Lemma cosine_law' a b c :
  norm (b - c) ^+ 2 = norm (c - a) ^+ 2 + norm (b - a) ^+ 2 -
  norm (c - a) * norm (b - a) * cos (vec_angle (b - a) (c - a)) *+ 2.
Proof.
rewrite -[in LHS]dotmulvv (_ : b - c = b - a - (c - a)); last first.
  by rewrite -!addrA opprB (addrC (- a)) (addrC a) addrK.
rewrite dotmulD dotmulvv [in X in _ + _ + X = _]dotmulvN dotmulNv opprK.
rewrite dotmulvv dotmulvN addrAC (addrC (norm (b - a) ^+ _)); congr (_ + _).
by rewrite dotmul_cos mulNrn (mulrC (norm (b - a))).
Qed.

Lemma cosine_law a b c : norm (c - a) != 0 -> norm (b - a) != 0 ->
  cos (vec_angle (b - a) (c - a)) =
  (norm (b - c) ^+ 2 - norm (c - a) ^+ 2 - norm (b - a) ^+ 2) /
  (norm (c - a) * norm (b - a) *- 2).
Proof.
move=> H0 H1.
rewrite (cosine_law' a b c) -2!addrA addrCA -opprD subrr addr0.
rewrite -mulNrn -mulr_natr mulNr -mulrA -(mulrC 2%:R) mulrA.
rewrite -mulNrn -[in X in _ = - _ / X]mulr_natr 2!mulNr invrN mulrN opprK.
rewrite mulrC mulrA mulVr ?mul1r // unitfE mulf_eq0 negb_or pnatr_eq0 andbT.
by rewrite mulf_eq0 negb_or H0 H1.
Qed.

Lemma norm_crossmul u v :
  norm (u *v v) = norm u * norm v * `| sin (vec_angle u v) |.
Proof.
suff /eqP : (norm (u *v v))^+2 = (norm u * norm v * `| sin (vec_angle u v) |)^+2.
  rewrite -eqr_sqrt ?sqr_ge0 // 2!sqrtr_sqr ger0_norm; last by rewrite norm_ge0.
  rewrite ger0_norm; first by move/eqP.
  by rewrite -mulrA mulr_ge0 // ?norm_ge0 // mulr_ge0 // ? norm_ge0.
rewrite norm_crossmul' dotmul_cos !exprMn.
apply/eqP; rewrite subr_eq -mulrDr.
rewrite real_normK; first by rewrite addrC cos2Dsin2 mulr1.
rewrite /sin; case: (expi _) => a b /=; rewrite realE //.
case: (lerP 0 b) => //= b0; by rewrite ltrW.
Qed.

Lemma norm_dotmul_crossmul u v : u != 0 -> v != 0 ->
  (`|u *d v +i* norm (u *v v)| = (norm u * norm v)%:C)%C.
Proof.
move=> u0 v0 .
rewrite {1}dotmul_cos {1}norm_crossmul normc_def.
rewrite exprMn (@exprMn _ 2 _ `| sin _ |) -mulrDr.
rewrite sqrtrM ?sqr_ge0 // sqr_normr cos2Dsin2 sqrtr1 mulr1.
rewrite sqrtr_sqr normrM; by do 2 rewrite ger0_norm ?norm_ge0 //.
Qed.

Lemma vec_angle0_inv u v : u != 0 -> v != 0 ->
  vec_angle u v = 0 -> u = (norm u / norm v) *: v.
Proof.
move=> u1 v1; rewrite /vec_angle => uv.
move: (norm_dotmul_crossmul u1 v1) => /arg0_inv/(_ uv)/eqP.
rewrite eq_complex {1}rmorphM /= mulf_eq0 negb_or.
rewrite eq_complex /= eqxx norm_eq0 andbT u1 eq_complex eqxx norm_eq0 andbT v1.
move/(_ isT) => /andP[].
rewrite dotmul_cos -{2}(mulr1 (norm u * norm v)); move/eqP/mulrI.
rewrite unitfE mulf_eq0 negb_or 2!norm_eq0 u1 v1 => /(_ isT) => uv1 ?.
apply/eqP; rewrite -subr_eq0 -norm_eq0.
  rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr0n /= normB. 
  rewrite vec_anglevZ; last by rewrite divr_gt0 // norm_gt0.
rewrite uv1 mulr1 !normZ ger0_norm; last by rewrite divr_ge0 // norm_ge0.
by rewrite -!mulrA mulVr ?unitfE // ?norm_eq0 // mulr1 -expr2 addrAC -mulr2n subrr.
Qed.

Lemma vec_anglepi_inv u v : u != 0 -> v != 0 ->
  vec_angle u v = pi -> u = - (norm u / norm v) *: v.
Proof.
move=> u1 v1; rewrite /vec_angle => uv.
move: (norm_dotmul_crossmul u1 v1) => /argpi_inv/(_ uv)/eqP.
rewrite eq_complex {1}rmorphM /= mulf_eq0 negb_or.
rewrite eq_complex /= eqxx andbT norm_eq0 u1 eq_complex /= eqxx andbT norm_eq0 v1.
move/(_ isT) => /andP[].
rewrite dotmul_cos -{1}(mulrN1 (norm u * norm v)).
move/eqP/mulrI; rewrite unitfE mulf_eq0 negb_or 2!norm_eq0 u1 v1.
move/(_ isT) => uv1 ?.
apply/eqP; rewrite -subr_eq0 -norm_eq0.
rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr0n /= normB vec_anglevZN; last first.
  by rewrite oppr_lt0 divr_gt0 // norm_gt0.
rewrite scaleNr normN cos_vec_anglevN // uv1 opprK.
rewrite mulr1 !normZ ger0_norm; last by rewrite divr_ge0 // norm_ge0.
by rewrite -!mulrA mulVr ?unitfE // ?norm_eq0 // mulr1 -expr2 addrAC -mulr2n subrr.
Qed.

Lemma dotmul1_inv u v : norm u = 1 -> norm v = 1 -> u *d v = 1 -> u = v.
Proof.
move=> u1 v1; rewrite dotmul_cos u1 v1 2!mul1r => /cos1_angle0/vec_angle0_inv.
rewrite -2!norm_eq0 u1 v1 oner_neq0 div1r invr1 scale1r; by apply.
Qed.

Lemma dotmulN1_inv u v : norm u = 1 -> norm v = 1 -> u *d v = - 1 -> u = - v.
Proof.
move=> u1 v1; rewrite dotmul_cos u1 v1 2!mul1r => /cosN1_angle0/vec_anglepi_inv.
rewrite -2!norm_eq0 u1 v1 oner_neq0 div1r invr1 scaleN1r; by apply.
Qed.

Lemma cos_vec_angle a b : a != 0 -> b != 0 ->
  `| cos (vec_angle a b) | = Num.sqrt (1 - (norm (a *v b) / (norm a * norm b)) ^+ 2).
Proof.
move=> Ha Hb.
rewrite norm_crossmul mulrAC divrr // ?mul1r.
  by rewrite sqr_normr -cos2sin2 sqrtr_sqr.
by rewrite unitfE mulf_neq0 // norm_eq0.
Qed.

Lemma orth_preserves_vec_angle M : M \is 'O[R]_3 ->
  {mono (fun u => u *m M) : v w / vec_angle v w}.
Proof.
move=> MO v w; move/(proj2 (orth_preserves_dotmul _))/(_ v w) : (MO).
by rewrite /vec_angle => ->; rewrite orth_preserves_norm_crossmul.
Qed.

End vec_angle.

Section colinear.

Variable R : rcfType.
Implicit Types u v : 'rV[R]_3.

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

(* TODO: to be improved? *)
Lemma colinearP u v :
  reflect (v == 0 \/
           (v != 0 /\ exists k, `| k | = norm u / norm v /\ u = k *: v))
          (colinear u v).
Proof.
apply: (iffP idP); last first.
  case => [/eqP ->|]; first by rewrite colinear_sym colinear0.
  case => v0 [k [k0 ukv]].
  by rewrite /colinear ukv crossmulC linearZ /= crossmulvv scaler0 oppr0.
rewrite /colinear => uv.
case/boolP : (v == 0) => v0; [by left | right; split; first by done].
case/boolP : (u == 0) => u0.
  by exists (norm u / norm v); rewrite (eqP u0) norm0 mul0r normr0 scale0r.
have : vec_angle u v = 0 \/ vec_angle u v = pi.
  rewrite /vec_angle (eqP uv) norm0.
  case: (lerP 0 (u *d v)) => udv; [left | right].
    rewrite arg_Re // ltr_neqAle udv andbT eq_sym.
    apply/negP => /(dotmul_eq0_crossmul_neq0 u0 v0); by rewrite uv.
  by rewrite arg_Re_neg.
case => [ /(vec_angle0_inv u0 v0) | /(vec_anglepi_inv u0 v0)] ukv.
  exists (norm u / norm v); split => //.
  by rewrite ger0_norm // divr_ge0 // norm_ge0.
exists (- (norm u / norm v)); split => //.
by rewrite normrN ger0_norm // divr_ge0 // norm_ge0.
Qed.

Lemma colinear_sin u v (u0 : u != 0) (v0 : v != 0) : 
  (colinear u v) = (sin (vec_angle u v) == 0).
Proof.
apply/idP/idP.
- rewrite colinear_sym => /colinearP.
  rewrite (negbTE u0).
  case=> // -[_ [k [Hk1 Hk2]]].
  rewrite Hk2 /vec_angle crossmulvZ crossmulvv scaler0 norm0 complexr0.
  rewrite dotmulvZ dotmulvv /sin.
  have k0 : k != 0 by apply: contra v0 => /eqP k0; rewrite Hk2 k0 scale0r.
  rewrite expi_arg; last first.
    by rewrite eq_complex /= eqxx andbT mulf_neq0 // sqrf_eq0 norm_eq0.
  by rewrite ImZ mulf_eq0 mulf_eq0 (negbTE k0) sqrf_eq0 norm_eq0 (negbTE u0) /= mul0r oppr0.
- move=> [:H].
  rewrite /vec_angle /sin expi_arg; last first.
    rewrite eq_complex /= negb_and.
    abstract: H.
    case/boolP : (u *d v == 0) => [/eqP udv0/=|//].
    by rewrite norm_crossmul dotmul0_vec_angle // mulr1 mulf_neq0 // ?norm_eq0.
  rewrite /= !(mul0r,oppr0,mulr0,add0r,expr0n,addr0).
  set tmp := Num.sqrt _.
  move=> [:tmp0].
  rewrite (_ : tmp / tmp ^+ 2 = tmp ^-1); last first.
    rewrite expr2 invrM; last 2 first.
      abstract: tmp0.
      rewrite unitfE /tmp sqrtr_eq0 -ltrNge ltr_neqAle.
      rewrite addr_ge0 ?sqr_ge0 // andbT eq_sym.
      rewrite paddr_eq0 ?sqr_ge0 // negb_and !sqrf_eq0 norm_eq0 crossmulC oppr_eq0.
      by rewrite crossmulC oppr_eq0 -(norm_eq0 (_ *v _)).
      done.
    by rewrite mulrCA divrr ?mulr1.
  rewrite mulf_eq0 invr_eq0 => /orP[]; last first.
    move: tmp0.
    by rewrite unitfE => /negbTE ->.
  by rewrite norm_eq0.
Qed.

Lemma sin_vec_angle_iff (u v : 'rV[R]_3) (u0 : u != 0) (v0 : v != 0) : 
  0 <= sin (vec_angle u v) ?= iff (colinear u v).
Proof. split; [exact: sin_vec_angle_ge0|by rewrite colinear_sin]. Qed.

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
rewrite {1}/normalize normZ gtr0_norm // invrM ?unitfE ?gtr_eqF // ?norm_gt0 //.
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

Lemma axialcomp_crossmul (u v : 'rV[R]_3) : axialcomp (u *v v) u == 0.
Proof.
by rewrite /axialcomp -dotmul_crossmul2 crossmulC crossmulvv crossmulv0 oppr0.
Qed.

Lemma axialcompE (v u : 'rV[R]_3) : axialcomp v u = v *m u^T *m u.
Proof.
by rewrite /axialcomp dotmulC /dotmul (mx11_scalar (v *m _)) mul_scalar_mx mxE eqxx mulr1n.
Qed.

Lemma crossmul_axialcomp e p : e *v axialcomp p e = 0.
Proof. apply/eqP; by rewrite /axialcomp linearZ /= crossmulvv scaler0. Qed.

(* normal component of v w.r.t. u *)
Definition normalcomp v u := v - u *d v *: u.

Lemma normalcompN u v : normalcomp u (- v)  = normalcomp u v.
Proof. by rewrite /normalcomp dotmulNv scaleNr scalerN opprK. Qed.

Lemma normalcomp_colinear_helper v u : normalcomp v u = 0 -> colinear v u.
Proof.
by move/eqP; rewrite subr_eq0 => /eqP ->; rewrite colinearZv ?colinear_refl orbT.
Qed.

Lemma normalcomp_colinear u v (v1 : norm v = 1) : (normalcomp u v == 0) = colinear u v.
Proof.
apply/idP/idP => [/eqP|/colinearP]; first by apply: normalcomp_colinear_helper.
rewrite -norm_eq0 v1 -(negbK (1 == 0)) oner_neq0 => -[] // [] _ [k [Hk1 Hk2]].
by rewrite /normalcomp Hk2 dotmulvZ dotmulvv v1 expr1n mulr1 subrr.
Qed.

Lemma ortho_normalcomp u v : u *d v = 0 -> normalcomp u v = u.
Proof. by move=> uv0; rewrite /normalcomp dotmulC uv0 scale0r subr0. Qed.

Lemma normalcomp_mul_tr (u : 'rV[R]_3) (u1 : norm u = 1) : 
  normalcomp 'e_0 u *m u^T *m u == 0.
Proof.
rewrite /normalcomp mulmxBl -scalemxAl dotmul1 // dotmulC /dotmul.
by rewrite scalemx1 -(mx11_scalar (_ *m u^T)) subrr mul0mx.
Qed.

Lemma dotmul_normalcomp e p : norm e = 1 -> normalcomp p e *d e = 0.
Proof.
move=> e1.
by rewrite /normalcomp dotmulBl dotmulZv dotmulvv e1 expr1n mulr1 dotmulC subrr.
Qed.

Lemma axialnormal v e : norm e = 1 -> axialcomp v e *d normalcomp v e = 0.
Proof.
move=> ?.
by rewrite /axialcomp dotmulZv (dotmulC _ (normalcomp v e)) dotmul_normalcomp // mulr0.
Qed.

Lemma decomp v u : v = axialcomp v u + normalcomp v u.
Proof. by rewrite /axialcomp /normalcomp addrC subrK. Qed.

Definition orthogonalize v u := normalcomp v (normalize u).

Lemma dotmul_orthogonalize u v : u *d orthogonalize v u = 0.
Proof.
rewrite /normalcomp /normalize dotmulBr !(dotmulZv, dotmulvZ).
rewrite mulrACA -invfM -expr2 dotmulvv mulrCA.
have [->|u_neq0] := eqVneq u 0; first by rewrite dotmul0v mul0r subrr.
by rewrite mulVr ?mulr1 ?subrr // unitfE sqrf_eq0 norm_eq0.
Qed.

End axial_normal_decomposition.

Section line.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

Definition coplanar (p1 p2 p3 p4 : point) : bool :=
  (p1 - p3) *d ((p2 - p1) *v (p4 - p3)) == 0.

Record line := mkLine {
  line_point : point ;
  line_vector :> vector }.

Definition line_point2 (l : line) := line_point l + line_vector l.

Implicit Types l : line.

(*Definition line_point l : point := let: mkLine p1 _ := l in p1.
Definition line_vector l : vector := line_point2 l - line_point l.*)

(*Definition mkDline (p : point) (u : vector) (u0 : u != 0) : line.
apply (@mkLine p (p + u)).
apply: contra u0.
by rewrite addrC -subr_eq subrr eq_sym.
Defined.*)

Definition parallel : rel line := [rel l1 l2 |
  colinear (line_vector l1) (line_vector l2)].

Definition skew : rel line := [rel l1 l2 | 
  let: (p1, p2) := (line_point l1, line_point2 l1) in
  let: (p3, p4) := (line_point l2, line_point2 l2) in
  ~~ coplanar p1 p2 p3 p4].

Definition intersects : rel line :=
  [rel l1 l2 | ~~ skew l1 l2 && ~~ parallel l1 l2 ].

Definition distance_point_line (p : point) l : R :=
  norm ((p - line_point l) *v (line_vector l)) / norm (line_vector l).

Definition distance_between_lines l1 l2 : R :=
  if intersects l1 l2 then
    0
  else if parallel l1 l2 then
    distance_point_line (line_point l1) l2
  else (* skew lines *)               
    let n := line_vector l1 *v line_vector l2 in
    `| (line_point l2 - line_point l1) *d n | / norm n.

End line.
