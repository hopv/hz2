
  Ltac rd_input_q0_1 :=
    apply FPinput_q0_1; unfold input_q0_1gen.

  Ltac rd_repeat_q0_1 :=
    apply FPrepeat_q0_1; unfold repeat_q0_1gen.

  Ltac hred :=
    first [red |
 rd_input_q0_1 |
 rd_repeat_q0_1 |
simpl]; simpl.

  Ltac pr_repeat_call_rec fst n :=
    match n with
| O => idtac ""
| S ?m => 
  auto; try omega;
  match goal with
  | |- _ \/ True => right; auto
  | |- True \/ _ => left; auto
  | |- _ \/ False => left; pr_repeat_call_rec fst m
  | |- False \/ _ => right; pr_repeat_call_rec fst m
  | H : _ /\ _ |- _ => decompose [and] H; clear H; pr_repeat_call_rec fst m
  | H : _ |- ?x => match fst with
                   | 1 => match x with
| (input_q0_1 _ _ _ ) => hred; pr_repeat_call_rec 2 m
| (repeat_q0_1 _ _ _ ) => hred; pr_repeat_call_rec 2 m
                          (* fix here *)
                          | _ => fail
                          end
                   | _ => fail
                   end
  | |- _ -> _ => intro; pr_repeat_call_rec fst m
  | |- _ /\ _ => split; pr_repeat_call_rec fst m
| |- ord input_q0_1t _ input_q0_1 => apply LFPinput_q0_1; (try unfold input_q0_1gen); pr_repeat_call_rec fst m
| |- mono input_q0_1t (input_q0_1gen _) => unfold mono; rewrite mono_exp2 in Minput_q0_1gen; pr_repeat_call_rec fst m
| |- ord repeat_q0_1t _ repeat_q0_1 => apply LFPrepeat_q0_1; (try unfold repeat_q0_1gen); pr_repeat_call_rec fst m
| |- mono repeat_q0_1t (repeat_q0_1gen _) => unfold mono; rewrite mono_exp2 in Mrepeat_q0_1gen; pr_repeat_call_rec fst m
| |- ord ?t _ _ => (try unfold t); first [hord'; pr_repeat_call_rec fst m | hord; pr_repeat_call_rec fst m]
| |- mono ?t _ => (try unfold t); unfold mono; pr_repeat_call_rec fst m
  | Hk : _ -> ?k _ |- ?k _ => apply Hk; pr_repeat_call_rec fst m
  | Hk : _ -> _ -> ?k _ |- ?k _ => apply Hk; pr_repeat_call_rec fst m
  | H : _ -> _ |- _ => last H; pr_repeat_call_rec fst m
  | |- ?H0 \/ ?H1 => (left; pr_repeat_call_rec fst m || right; pr_repeat_call_rec fst m)
  | _ => hred; pr_repeat_call_rec fst m
  end
end.

  Ltac hauto :=
    solve [pr_repeat_call_rec 1 5].
