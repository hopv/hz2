
  Ltac rd_g_q1_1 :=
    apply FPg_q1_1; unfold g_q1_1gen.

  Ltac rd_g_q0_1 :=
    apply FPg_q0_1; unfold g_q0_1gen.

  Ltac rd_f_q0_1 :=
    apply FPf_q0_1; unfold f_q0_1gen.

  Ltac rd_g_q2_2 :=
    apply FPg_q2_2; unfold g_q2_2gen.

  Ltac hred :=
    first [red |
 rd_g_q1_1 |
 rd_g_q0_1 |
 rd_f_q0_1 |
 rd_g_q2_2 |
simpl]; simpl.

  Ltac pr_ex2_3_rec fst n :=
    match n with
| O => idtac ""
| S ?m => 
  auto; try omega;
  match goal with
  | |- _ \/ True => right; auto
  | |- True \/ _ => left; auto
  | |- _ \/ False => left; pr_ex2_3_rec fst m
  | |- False \/ _ => right; pr_ex2_3_rec fst m
  | H : _ /\ _ |- _ => decompose [and] H; clear H; pr_ex2_3_rec fst m
  | H : _ |- ?x => match fst with
                   | 1 => match x with
                          | (g_q1_1 _ _ ) => hred; pr_ex2_3_rec 2 m
                          | (g_q0_1 _ _ ) => hred; pr_ex2_3_rec 2 m
                          | (f_q0_1 _ _ ) => hred; pr_ex2_3_rec 2 m
                          | (g_q2_2 _ ) => hred; pr_ex2_3_rec 2 m
                          (* fix here *)
                          | _ => fail
                          end
                   | _ => fail
                   end
  | |- _ -> _ => intro; pr_ex2_3_rec fst m
  | |- _ /\ _ => split; pr_ex2_3_rec fst m



  | |- ord g_q2_2t _ g_q2_2 => apply GFPg_q2_2; (try unfold g_q2_2gen); pr_ex2_3_rec fst m
  | |- mono g_q2_2t (g_q2_2gen _) => unfold mono; rewrite mono_exp2 in Mg_q2_2gen; pr_ex2_3_rec fst m
  | |- mono ?t (?f) => (try unfold t); unfold f; unfold mono; pr_ex2_3_rec fst m
  | |- mono ?t (?f _) => (try unfold t); unfold f; unfold mono; pr_ex2_3_rec fst m
  | |- mono ?t (?f _ _) => (try unfold t); unfold f; unfold mono; pr_ex2_3_rec fst m
  | |- mono ?t (?f _ _ _) => (try unfold t); unfold f; unfold mono; pr_ex2_3_rec fst m
  | |- mono ?t (?f _ _ _ _) => (try unfold t); unfold f; unfold mono; pr_ex2_3_rec fst m
  | |- mono ?t (?f _ _ _ _ _) => (try unfold t); unfold f; unfold mono; pr_ex2_3_rec fst m
  | |- ord ?t _ _ => (try unfold t); hord; pr_ex2_3_rec fst m
  | |- ord _ _ _ => hord; pr_ex2_3_rec fst m
  | |- mono ?t _ => (try unfold t); unfold mono; pr_ex2_3_rec fst m
  | Hk : _ -> ?k _ |- ?k _ => apply Hk; pr_ex2_3_rec fst m
  | Hk : _ -> _ -> ?k _ |- ?k _ => apply Hk; pr_ex2_3_rec fst m
  | H : _ -> _ |- _ => last H; pr_ex2_3_rec fst m
  | |- ?H0 \/ ?H1 => (left; pr_ex2_3_rec fst m || right; pr_ex2_3_rec fst m)
  | _ => hred; pr_ex2_3_rec fst m
  end
end.

  Ltac hauto :=
    solve [pr_ex2_3_rec 1 30].
