From mathcomp Require Import all_ssreflect all_algebra ring.
Require Import ssr_ext euclidean rigid frame skew.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

(* to appear in MathComp 2.5.0 *)
Lemma lsubmx_const {R : nmodType} (r : R) m n1 n2 :
  lsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

(* to appear in MathComp 2.5.0 *)
Lemma rsubmx_const {R : nmodType} (r : R) m n1 n2 :
  rsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma sqr_inj {R : rcfType} : {in Num.nneg &, injective (fun x : R => x ^+ 2)}.
Proof.
by move=> x y x0 y0 /(congr1 (@Num.sqrt R)); rewrite !sqrtr_sqr! ger0_norm.
Qed.

(* PR to MathComp *)
Lemma char_poly2 (R : numFieldType) (M : 'M[R]_2) : char_poly M = 'X^2 - (\tr M)%:P * 'X + (\det M)%:P.
Proof.
set P := (RHS).
apply/polyP => -[|[|[|i]]]; last first.
- have := (rwP (leq_sizeP (char_poly M) i.+3)).2.
  rewrite size_char_poly => /(_ erefl) /(_ i.+3) => ->//.
  rewrite (rwP (leq_sizeP P i.+3)).2//.
  rewrite /P -addrA size_addl ?size_polyXn//.
  rewrite -mulNr size_MXaddC; case: ifPn => // _.
  by rewrite ltnS -polyCN size_polyC; case: (_ == _).
- rewrite /P -[in RHS]addrA [RHS]coefD coefXn/= coefD -mulrN coefCM coefC/= coefN coefX/= oppr0 mulr0 !addr0.
  rewrite /char_poly det_mx22//.
  rewrite /char_poly_mx !mxE/= mulr1n mulr0n sub0r mulNr opprK sub0r mulrN.
  rewrite coefD coefN coefCM coefC/= mulr0 subr0.
  by rewrite coefM sum3E !coefE/= !(subr0,mul0r,mulr0,addr0,mulr1,add0r).
- rewrite char_poly_trace//.
  by rewrite /P -addrA addrCA !coefD coefN coefCM coefX/= mulr1 coefC/= addr0 coefXn addr0.
- rewrite char_poly_det sqrrN expr1n mul1r.
  by rewrite /P !coefD coefC/= coefN coefCM coefX mulr0 subr0 coefXn/= add0r.
Qed.
