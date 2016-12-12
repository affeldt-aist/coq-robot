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
 3. section axial_normal_decomposition.
    axialcomp, normalcomp
    (easy definitions to construct frames out of already available points/vectors)
 4. section line
 5. section line_line_intersection
 6. section line_distance
      distance_point_line
      distance_between_lines
*)

Lemma norm1_cossin (R : rcfType) (v :'rV[R]_2) :
  norm v = 1 -> {a | v``_0 = cos a /\ v``_1 = sin a}.
Proof.
move=> v1.
apply sqrD1_cossin.
by rewrite -(sum2E (fun i => v``_i ^+ 2)) -sqr_norm v1 expr1n.
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

Lemma colinearvv u : colinear u u.
Proof. by rewrite /colinear crossmulvv. Qed.

Lemma scale_colinear k v : colinear (k *: v) v.
Proof. by rewrite /colinear crossmulC linearZ /= crossmulvv scaler0 oppr0. Qed.

Lemma colinear_refl : reflexive colinear.
Proof. move=> ?; by rewrite /colinear crossmulvv. Qed.

Lemma colinear_sym : symmetric colinear.
Proof. by move=> u v; rewrite /colinear crossmulC -eqr_opp opprK oppr0. Qed.

Lemma colinear0v u : colinear 0 u.
Proof. by rewrite /colinear crossmul0v. Qed.

Lemma colinearv0 u : colinear u 0.
Proof. by rewrite colinear_sym colinear0v. Qed.

Definition colinear0 := (colinear0v, colinearv0).

Lemma colinear_trans v u w : u != 0 -> colinear v u -> colinear u w -> colinear v w.
Proof.
move=> u0.
rewrite /colinear => vu0 uw0.
move: (jacobi_crossmul u v w).
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

Lemma colinearvN u v : colinear u (- v) = colinear u v.
Proof. by rewrite colinear_sym colinearNv colinear_sym. Qed.

(* TODO: to be improved? *)
Lemma colinearP u v :
  reflect (v == 0 \/
           (v != 0 /\ exists k, `| k | = norm u / norm v /\ u = k *: v))
          (colinear u v).
Proof.
apply: (iffP idP); last first.
  case => [/eqP ->|]; first by rewrite colinear0.
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

Lemma colinearD u v w : colinear u w -> colinear v w ->
  colinear (u + v) w.
Proof.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite addr0.
case/colinearP => [/eqP -> _| [w0 [k [Hk1 Hk2]]]]; first by rewrite colinear0.
case/colinearP => [/eqP ->|[_ [k' [Hk'1 Hk'2]]]]; first by rewrite colinear0.
by rewrite Hk2 Hk'2 -scalerDl colinearZv colinear_refl orbT.
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

Lemma invariant_colinear (u : 'rV[R]_3) (M : 'M[R]_3) :
  u != 0 -> u *m M = u -> forall v, colinear u v -> v *m M = v.
Proof.
move=> u0 uMu v /colinearP[/eqP->|[v0 [k [Hk1 Hk2]]]]; first by rewrite mul0mx.
move: uMu; rewrite Hk2 -scalemxAl => /eqP.
rewrite -subr_eq0 -scalerBr scaler_eq0 -normr_eq0 Hk1 mulf_eq0 invr_eq0.
by rewrite 2!norm_eq0 (negbTE u0) (negbTE v0) /= subr_eq0 => /eqP.
Qed.

End colinear.

Section axial_normal_decomposition.

Variables (R : rcfType).
Let vector := 'rV[R]_3.
Implicit Types u v : vector.

(*Definition axialcomp v u := u *d v *: u.*)
Definition axialcomp v u := normalize u *d v *: normalize u.

Lemma colinear_axialcomp u v : colinear u (axialcomp v u).
Proof.
apply/eqP;
by rewrite /axialcomp linearZ /= crossmulvZ crossmulvv 2!scaler0.
Qed.

Lemma axialcomp_crossmul u v : axialcomp (u *v v) u == 0.
Proof.
rewrite /axialcomp -dotmul_crossmul2 !crossmulZv crossmulvZ crossmulvv.
by rewrite crossmul0v 2!scaler0.
Qed.

Lemma axialcompE v u : axialcomp v u = (norm u) ^- 2 *: (v *m u^T *m u).
Proof.
case/boolP : (u == 0) => [/eqP ->|u0].
  by rewrite /axialcomp /normalize norm0 invr0 mulmx0 !scaler0.
rewrite /axialcomp dotmulZv scalerA mulrAC dotmulP mul_scalar_mx dotmulC.
by rewrite -invrM ?unitfE ?norm_eq0 // -expr2 scalerA.
Qed.

Lemma crossmul_axialcomp u v : u *v axialcomp v u = 0.
Proof.
by apply/eqP; rewrite /axialcomp linearZ /= crossmulvZ crossmulvv 2!scaler0. 
Qed.

(* normal component of v w.r.t. u *)
(*Definition normalcomp v u := v - u *d v *: u.*)
Definition normalcomp v u := v - normalize u *d v *: normalize u.

Lemma normalcomp0v v : normalcomp 0 v = 0.
Proof. by rewrite /normalcomp dotmulv0 scale0r subrr. Qed.

Lemma normalcompv0 v : normalcomp v 0 = v.
Proof. by rewrite /normalcomp /normalize scaler0 dotmul0v scaler0 subr0. Qed.

Lemma normalcompvN v u : normalcomp v (- u) = normalcomp v u.
Proof. 
by rewrite /normalcomp normalizeN scalerN dotmulNv scaleNr opprK.
Qed.

Lemma normalcompNv v u : normalcomp (- v) u = - normalcomp v u.
Proof. by rewrite /normalcomp dotmulvN scaleNr opprK opprD opprK. Qed.

Lemma normalcomp_colinear_helper v u : normalcomp v u = 0 -> colinear v u.
Proof.
move/eqP; rewrite subr_eq0 => /eqP ->.
by rewrite !colinearZv ?colinear_refl 2!orbT.
Qed.

Lemma normalcomp_colinear u v (u0 : u != 0) :
  (normalcomp v u == 0) = colinear v u.
Proof.
apply/idP/idP => [/eqP|/colinearP]; first by apply: normalcomp_colinear_helper.
case; first by rewrite (negbTE u0).
case=> _ [k [Hk1 Hk2]].
rewrite /normalcomp Hk2 dotmulvZ dotmulZv dotmulvv (exprD _ 1 1) expr1.
rewrite (mulrA (_^-1)) mulVr ?unitfE ?norm_eq0 // mul1r.
by rewrite scalerA -mulrA divrr ?unitfE ?norm_eq0 // mulr1 subrr.
Qed.

Lemma normalcomp_mulO u p Q : Q \is 'O[R]_3 -> u *m Q = u ->
  normalcomp (p *m Q) u = normalcomp p u *m Q.
Proof.
move=> QO uQu.
rewrite /normalcomp mulmxBl; congr (_ - _).
rewrite -2!scalemxAl uQu; congr (_ *: _).
by rewrite 2!dotmulZv -{2}uQu (proj2 (orth_preserves_dotmul Q) QO u).
Qed.

Lemma crossmul_normalcomp u v : u *v normalcomp v u = u *v v.
Proof.
rewrite /normalcomp linearD /= crossmulvN dotmulC crossmulvZ.
by rewrite crossmulvZ crossmulvv 2!scaler0 subr0.
Qed.

Lemma dotmul_normalcomp u v : normalcomp v u *d u = 0.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite dotmulv0.
rewrite /normalcomp dotmulBl !dotmulZv dotmulvv (exprD _ 1 1) expr1.
rewrite (mulrA (_^-1)) mulVr ?unitfE ?norm_eq0 // mul1r mulrAC.
by rewrite mulVr ?unitfE ?norm_eq0 // mul1r dotmulC subrr.
Qed.

Lemma ortho_normalcomp u v : (v *d u == 0) = (normalcomp v u == v).
Proof. 
apply/idP/idP => [/eqP uv0|/eqP <-].
  by rewrite /normalcomp dotmulC dotmulvZ uv0 mulr0 scale0r subr0.
by rewrite dotmul_normalcomp.
Qed.

Lemma normalcomp_mul_tr u (u1 : norm u = 1) : normalcomp 'e_0 u *m u^T == 0.
Proof.
rewrite /normalcomp mulmxBl -scalemxAl -scalemxAl dotmul1 // dotmulC /dotmul.
by rewrite u1 invr1 scalemx1 scalemx1 normalizeI // {1}dotmulP subrr.
Qed.

Lemma axialnormal v u : axialcomp v u *d normalcomp v u = 0.
Proof.
by rewrite /axialcomp !dotmulZv (dotmulC _ (normalcomp v u))
  dotmul_normalcomp // !mulr0.
Qed.

Lemma decomp v u : v = axialcomp v u + normalcomp v u.
Proof. by rewrite /axialcomp /normalcomp addrC subrK. Qed.

Definition orthogonalize v u := normalcomp v (normalize u).

Lemma dotmul_orthogonalize u v : u *d orthogonalize v u = 0.
Proof.
rewrite /normalcomp /normalize dotmulBr !(dotmulZv, dotmulvZ).
rewrite mulrACA -invfM -expr2 dotmulvv mulrCA.
have [->|u_neq0] := eqVneq u 0; first by rewrite norm0 invr0 dotmul0v !mul0r subrr.
rewrite norm_normalize // expr1n invr1 mul1r.
rewrite (mulrC _ (u *d _)).
rewrite -mulrA (mulrA (_^-1)) -expr2 -exprMn mulVr ?expr1n ?mulr1 ?subrr //.
by rewrite unitfE norm_eq0.
Qed.

End axial_normal_decomposition.

Section law_of_sines.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Implicit Types a b c : point.
Implicit Types v : vector.

Definition tricolinear a b c := colinear (b - a) (c - a).

Lemma tricolinear_rot a b c : tricolinear a b c = tricolinear b c a.
Proof.
rewrite /tricolinear /colinear !linearD /= !crossmulDl !crossmulvN !crossmulNv.
rewrite !opprK !crossmulvv !addr0 -addrA addrC (crossmulC a c) opprK.
by rewrite (crossmulC b c).
Qed.

Lemma tricolinear_perm a b c : tricolinear a b c = tricolinear b a c.
Proof.
rewrite /tricolinear /colinear !linearD /= !crossmulDl !crossmulvN !crossmulNv.
rewrite !opprK !crossmulvv !addr0 -{1}oppr0 -eqr_oppLR 2!opprB.
by rewrite addrC (crossmulC a b) opprK.
Qed.

Lemma triangle_sin_vector_helper v1 v2 : ~~ colinear v1 v2 ->
  norm v1 ^+ 2 * sin (vec_angle v1 v2) ^+ 2 = norm (normalcomp v1 v2) ^+ 2.
Proof.
move=> H.
have v10 : v1 != 0 by apply: contra H => /eqP ->; rewrite colinear0.
have v20 : v2 != 0 by apply: contra H => /eqP ->; rewrite colinear_sym colinear0.
rewrite /normalcomp [in RHS]normB.
case/boolP : (0 < normalize v2 *d v1) => [v2v1|].
  rewrite normZ gtr0_norm // norm_normalize // mulr1 scalerA vec_anglevZ //; last first.
    by rewrite divr_gt0 // norm_gt0.
  rewrite dotmul_cos norm_normalize // mul1r vec_angleZv; last first.
    by rewrite invr_gt0 norm_gt0.
  rewrite [in RHS]mulrA (vec_angleC v1) -expr2 -mulrA -expr2 exprMn.
  by rewrite mulr2n opprD addrA subrK sin2cos2 mulrBr mulr1.
rewrite -lerNgt ler_eqVlt => /orP[|v2v1].
  rewrite {1}dotmul_cos norm_normalize // mul1r mulf_eq0 norm_eq0 (negbTE v10) /=.
  rewrite vec_angleZv => [/eqP Hcos|]; last by rewrite invr_gt0 norm_gt0.
  rewrite dotmulZv (_ : _ *d _ = 0); last by rewrite dotmul_cos Hcos mulr0.
  rewrite mulr0 scale0r norm0 mulr0 mul0r expr0n mul0rn addr0 subr0.
  by rewrite -(sqr_normr (sin _)) vec_angleC cos0sin1 ?expr1n ?mulr1.
rewrite vec_anglevZN // cos_vec_anglevN // ?normalize_eq0 //.
rewrite scalerA normZ ltr0_norm; last first.
  rewrite mulr_lt0 invr_eq0 norm_eq0 v20 /= ltr_eqF //=.
  by rewrite invr_lt0 (ltrNge (norm v2)) norm_ge0 addbF.
rewrite mulNr -(mulrA _ _ (norm v2)) mulVr ?mulr1 ?unitfE ?norm_eq0 //.
rewrite vec_anglevZ // ?invr_gt0 ?norm_gt0 // sqrrN mulrN mulNr mulrN opprK.
rewrite dotmul_cos norm_normalize // mul1r vec_angleZv ?invr_gt0 ?norm_gt0 //.
rewrite (vec_angleC v2) mulrA -expr2 exprMn addrAC -addrA -mulrA -mulrnAr.
rewrite -mulrBr -{2}(mulr1 (norm v1 ^+ 2)) -mulrDr; congr (_ * _).
by rewrite sin2cos2 -expr2 mulr2n opprD !addrA addrK.
Qed.

Lemma triangle_sin_vector v1 v2 : ~~ colinear v1 v2 ->
  sin (vec_angle v1 v2) = norm (normalcomp v1 v2) / norm v1.
Proof.
move=> H.
have v10 : v1 != 0 by apply: contra H => /eqP ->; rewrite colinear0.
have v20 : v2 != 0 by apply: contra H => /eqP ->; rewrite colinear_sym colinear0.
apply/eqP.
rewrite -(@eqr_expn2 _ 2) // ?divr_ge0 // ?norm_ge0 // ?sin_vec_angle_ge0 //.
rewrite exprMn -triangle_sin_vector_helper // mulrAC exprVn divrr ?mul1r //.
by rewrite unitfE sqrf_eq0 norm_eq0.
Qed.

Lemma triangle_sin_point p1 p2 p : ~~ tricolinear p1 p2 p ->
  let v1 := p1 - p in let v2 := p2 - p in
  sin (vec_angle v1 v2) = norm (normalcomp v1 v2) / norm v1.
Proof.
move=> H v1 v2; apply triangle_sin_vector; apply: contra H.
by rewrite tricolinear_perm 2!tricolinear_rot /tricolinear /v1 /v2 colinear_sym.
Qed.

Lemma law_of_sines_vector v1 v2 : ~~ colinear v1 v2 ->
  sin (vec_angle v1 v2) / norm (v2 - v1) = sin (vec_angle (v2 - v1) v2) / norm v1.
Proof.
move=> H.
move: (triangle_sin_vector H) => /= H1.
rewrite [in LHS]H1.
have H' : ~~ colinear v2 (v2 - v1).
  rewrite colinear_sym; apply: contra H => H.
  move: (colinear_refl v2); rewrite -colinearNv => /(colinearD H).
  by rewrite addrAC subrr add0r colinearNv.
have H2 : sin (vec_angle v2 (v2 - v1)) = norm (normalcomp (v2 - v1) v2) / norm (v2 - v1).
  rewrite vec_angleC; apply triangle_sin_vector; by rewrite colinear_sym.
rewrite [in RHS]vec_angleC [in RHS]H2.
have H3 : normalcomp v1 v2 = normalcomp (v1 - v2) v2.
  (* TODO: lemma? *)
  apply/eqP.
  rewrite /normalcomp subr_eq -addrA -scaleNr -scalerDl -dotmulvN -dotmulDr.
  rewrite opprB -(addrA v1) (addrCA v1) subrK dotmulC dotmul_normalize_norm.
  by rewrite norm_scale_normalize addrC addrK.
by rewrite H3 mulrAC -(opprB v2) normalcompNv normN.
Qed.

Lemma law_of_sines_point p1 p2 p : ~~ tricolinear p1 p2 p ->
  let v1 := p1 - p in let v2 := p2 - p in
  sin (vec_angle v1 v2) / norm (p2 - p1) =
  sin (vec_angle (p2 - p1) (p2 - p)) / norm (p1 - p).
Proof.
move=> H v1 v2.
rewrite (_ : p2 - p1 = v2 - v1); last by rewrite /v1 /v2 opprB addrA subrK.
apply law_of_sines_vector.
apply: contra H.
by rewrite tricolinear_perm 2!tricolinear_rot /tricolinear /v1 /v2 colinear_sym.
Qed.

End law_of_sines.

Module Line.
Section line_def.
Variable R : rcfType.
Record t := mk {
  point : 'rV[R]_3 ;
  vector :> 'rV[R]_3
}.
Definition point2 (l : t) := point l + vector l.
Lemma vectorE l : vector l = point2 l - point l.
Proof. by rewrite /point2 addrAC subrr add0r. Qed.
End line_def.
End Line.

Notation "'\pt(' l ')'" := (Line.point l) (at level 3, format "'\pt(' l ')'").
Notation "'\pt2(' l ')'" := (Line.point2 l) (at level 3, format "'\pt2(' l ')'").
Notation "'\vec(' l ')'" := (Line.vector l) (at level 3, format "'\vec(' l ')'").

Coercion line_pred (R : rcfType) (l : Line.t R) : pred 'rV[R]_3 :=
  [pred p | (p == \pt( l )) ||
    (\vec( l ) != 0) && colinear \vec( l ) (p - \pt( l ))].

Section line.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Implicit Types l : Line.t R.

Lemma line_point_in l : \pt( l ) \in (l : pred _).
Proof. by case: l => p v /=; rewrite inE /= eqxx. Qed.

Lemma lineP p l :
  reflect (exists k', p = \pt( l ) + k' *: \vec( l)) (p \in (l : pred _)).
Proof.
apply (iffP idP) => [|[k' ->]].
  rewrite inE.
  case/orP => [/eqP pl|]; first by exists 0; rewrite scale0r addr0.
  case/andP => l0 /colinearP[|[pl [k [Hk1 Hk2]]]].
    rewrite subr_eq0 => /eqP ->; exists 0; by rewrite scale0r addr0.
  have k0 : k != 0 by rewrite -normr_eq0 Hk1 mulf_neq0 // ?invr_eq0 norm_eq0.
  exists k^-1.
  by rewrite Hk2 scalerA mulVr ?unitfE // scale1r addrCA subrr addr0.
rewrite inE.
case/boolP : (\vec( l ) == 0) => [/eqP ->|l0 /=].
  by rewrite scaler0 addr0 eqxx.
by rewrite addrAC subrr add0r colinearvZ colinear_refl 2!orbT.
Qed.

Lemma mem_add_line l (p : point) (v : vector) : \vec( l ) != 0 ->
  colinear v \vec( l ) -> p + v \in (l : pred _) = (p \in (l : pred _)).
Proof.
move=> l0 vl.
apply/lineP/idP => [[] x /eqP|pl].
  rewrite eq_sym -subr_eq => /eqP <-.
  rewrite inE l0 /=; apply/orP; right.
  rewrite -!addrA addrC !addrA subrK colinear_sym.
  by rewrite colinearD // ?colinearZv ?colinear_refl ?orbT // colinearNv.
case/colinearP : vl => [|[_ [k [Hk1 ->]]]]; first by rewrite (negPf l0).
case/lineP : pl => k' ->.
exists (k' + k); by rewrite -addrA -scalerDl.
Qed.

Definition parallel : rel (Line.t R) :=
  [rel l1 l2 | colinear \vec( l1 ) \vec( l2 )].

Definition perpendicular : rel (Line.t R) :=
  [rel l1 l2 | \vec( l1 ) *d \vec( l2 ) == 0].

(* skew lines *)

Definition coplanar (p1 p2 p3 p4 : point) : bool :=
  (p1 - p3) *d ((p2 - p1) *v (p4 - p3)) == 0.

Definition skew : rel (Line.t R) := [rel l1 l2 |
  ~~ coplanar \pt( l1 ) \pt2( l1 ) \pt( l2 ) \pt2( l2) ].

Lemma skewE l1 l2 :
  skew l1 l2 = ~~ coplanar \pt( l1 ) \pt2( l1 ) \pt( l2 ) \pt2( l2).
Proof. by []. Qed.

End line.

Section line_line_intersection.

Variable R : rcfType.
Let point := 'rV[R]_3.
Implicit Types l : Line.t R.

Definition intersects : rel (Line.t R) :=
  [rel l1 l2 | ~~ skew l1 l2 && ~~ parallel l1 l2 ].

Definition is_interpoint p l1 l2 :=
  (p \in (l1 : pred _)) && (p \in (l2 : pred _)).

Definition interpoint_param x l1 l2 :=
  let v1 := \vec( l1 ) in let v2 := \vec( l2 ) in
  \det (col_mx3 (\pt( l2 ) - \pt( l1 )) x (v1 *v v2)) / norm (v1 *v v2) ^+ 2.

Lemma interpoint_param0 l1 l2 v : \pt( l1 ) = \pt( l2 ) ->
  interpoint_param v l1 l2 = 0.
Proof.
move=> p1p2.
by rewrite /interpoint_param p1p2 subrr -crossmul_triple dotmul0v mul0r.
Qed.

Definition interpoint_s l1 l2 := interpoint_param \vec( l1 ) l1 l2.

Definition interpoint_t l1 l2 := interpoint_param \vec( l2 ) l1 l2.

Lemma interparamP l1 l2 : intersects l1 l2 ->
  let v1 := \vec( l1 ) in let v2 := \vec( l2 ) in
  \pt( l1 ) + interpoint_t l1 l2 *: v1 = \pt( l2 ) + interpoint_s l1 l2 *: v2.
Proof.
move=> Hinter v1 v2.
rewrite /interpoint_t /interpoint_s /interpoint_param  -/v1 -/v2.
do 2 rewrite -crossmul_triple (dot_crossmulC (\pt( l2) - \pt( l1 ))).
apply/eqP; set v1v2 := v1 *v v2.
rewrite -subr_eq -addrA eq_sym addrC -subr_eq.
rewrite 2!(mulrC _ (_^-2)) -2!scalerA -scalerBr.
rewrite dotmulC dot_crossmulC (dotmulC _ v1v2) (dot_crossmulC).
rewrite -double_crossmul.
rewrite crossmulC double_crossmul dotmulC -{2}(opprB _ \pt( l2 )) dotmulNv.
case/andP: Hinter.
rewrite skewE negbK /coplanar -2!Line.vectorE => /eqP -> ?.
rewrite oppr0 scale0r add0r opprK dotmulvv scalerA mulVr ?scale1r //.
by rewrite unitfE sqrf_eq0 norm_eq0.
Qed.

Lemma intersects_interpoint l1 l2 : intersects l1 l2 ->
  {p | is_interpoint p l1 l2 /\
   p = \pt( l1 ) + interpoint_t l1 l2 *: \vec( l1 ) /\
   p = \pt( l2 ) + interpoint_s l1 l2 *: \vec( l2 )}.
Proof.
move=> Hinter.
case/boolP : (\pt( l1 ) == \pt( l2 )) => [/eqP|]p1p2.
  exists \pt( l1 ); split.
    rewrite /is_interpoint; apply/andP; split; by [
      rewrite inE eqxx !(orTb,orbT) | rewrite inE p1p2 eqxx orTb].
  rewrite /interpoint_t /interpoint_s interpoint_param0 //.
  by rewrite interpoint_param0 // 2!scale0r 2!addr0.
exists (\pt( l1) + interpoint_t l1 l2 *: \vec( l1 )).
split; last first.
  split=> //; exact: interparamP.
rewrite /is_interpoint; apply/andP; split.
  apply/lineP; by exists (interpoint_t l1 l2).
apply/lineP; eexists; exact: interparamP.
Qed.

Lemma interpoint_intersects l1 l2 : {p | is_interpoint p l1 l2} ->
  ~~ skew l1 l2.
Proof.
case=> p; rewrite /is_interpoint => /andP[H1 H2].
rewrite skewE negbK /coplanar -2!Line.vectorE.
case/lineP : (H1) => k1 /eqP; rewrite -subr_eq => /eqP <-.
case/lineP : (H2) => k2 /eqP; rewrite -subr_eq => /eqP <-.
rewrite opprB -addrA addrC addrA subrK dotmulDl !(dotmulNv,dotmulZv).
rewrite dot_crossmulC 2!dotmul_crossmul_shift 2!crossmulvv.
by rewrite !(dotmul0v,dotmulv0,mulr0,oppr0,addr0).
Qed.

Lemma interpointE p l1 l2 : ~~ parallel l1 l2 -> is_interpoint p l1 l2 ->
  let s := interpoint_s l1 l2 in let t := interpoint_t l1 l2 in
  let v1 := \vec( l1 ) in let v2 := \vec( l2 ) in
  \pt( l1 ) + t *: v1 = p /\ \pt( l2 ) + s *: v2 = p.
Proof.
move=> ?.
case/andP => /lineP[t' Hs] /lineP[s' Ht] s t.
move=> v1 v2.
have H (a b va vb : 'rV[R]_3) (k l : R) :
  a + k *: va = b + l *: vb -> k *: (va *v vb) = (b - a) *v vb.
  clear.
  move=> /(congr1 (fun x => x - a)).
  rewrite addrAC subrr add0r addrAC => /(congr1 (fun x => x *v vb)).
  by rewrite crossmulZv crossmulDl crossmulZv crossmulvv scaler0 addr0.
have Ht' : t' = interpoint_t l1 l2.
  have : t' *: (v1 *v v2) = (\pt( l2 ) - \pt( l1 )) *v v2.
    by rewrite (H \pt( l1 ) \pt( l2 ) _ _ _ s') // -Hs -Ht.
  move/(congr1 (fun x => x *d (v1 *v v2))).
  rewrite dotmulZv dotmulvv.
  move/(congr1 (fun x => x / (norm (v1 *v v2)) ^+ 2)).
  rewrite -mulrA divrr ?mulr1; last by rewrite unitfE sqrf_eq0 norm_eq0.
  by rewrite -dot_crossmulC crossmul_triple.
have Hs' : s' = interpoint_s l1 l2.
  have : s' *: (v1 *v v2) = (\pt( l2) - \pt( l1 )) *v v1.
    move: (H \pt( l2 ) \pt( l1 ) v2 v1 s' t').
    rewrite -Hs -Ht => /(_ erefl).
    rewrite crossmulC scalerN -opprB crossmulNv => /eqP.
    by rewrite eqr_opp => /eqP.
  move/(congr1 (fun x => x *d (v1 *v v2))).
  rewrite dotmulZv dotmulvv.
  move/(congr1 (fun x => x / (norm (v1 *v v2)) ^+ 2)).
  rewrite -mulrA divrr ?mulr1; last by rewrite unitfE sqrf_eq0 norm_eq0.
  by rewrite -dot_crossmulC crossmul_triple.
by rewrite /t /s -Ht' -Hs'.
Qed.

Lemma interpoint_unique p q l1 l2 : ~~ parallel l1 l2 ->
  is_interpoint p l1 l2 -> is_interpoint q l1 l2 -> p = q.
Proof.
by move=> l1l2 /interpointE => /(_ l1l2) [<- _] /interpointE => /(_ l1l2) [<- _].
Qed.

Definition intersection l1 l2 : option point :=
  if ~~ intersects l1 l2 then None
  else Some (\pt( l1 ) + interpoint_t l1 l2 *: \vec( l1 )).

End line_line_intersection.

Section distance_line.

Variable R : rcfType.
Let point := 'rV[R]_3.

Definition distance_point_line (p : point) l : R :=
  norm ((p - \pt( l )) *v \vec( l )) / norm \vec( l ).

Definition distance_between_lines (l1 l2 : Line.t R) : R :=
  if intersects l1 l2 then
    0
  else if parallel l1 l2 then
    distance_point_line \pt( l1 ) l2
  else (* skew lines *)
    let n := \vec( l1 ) *v \vec( l2 ) in
    `| (\pt( l2 ) - \pt( l1 )) *d n | / norm n.

End distance_line.
