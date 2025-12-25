Require Export Omega.
Require Export CpdtTactics. 

Require Export Hfl.

Ltac hord :=
  match goal with
  | H0 : ord ?o ?x ?y, H1: ord ?o ?y ?z |- ord ?o ?x ?z => apply ord_trans with y; auto; intros
  | |- ord o _ _ => rewrite ord_exp0; auto; intros
  | |- ord (arint _) _ _ => rewrite ord_exp1; auto; intros
  | |- ord (ar _ _) _ _ => rewrite ord_exp2; auto; intros
  | |- ord ?t _ _ => (try unfold t); hord
  end.

Ltac last x :=
  match x with
  | _ -> ?c => last c
  | _ => apply x
  end.

Ltac hsubst x :=
  assert x as TMP; [omega |]; rewrite TMP; clear TMP.

