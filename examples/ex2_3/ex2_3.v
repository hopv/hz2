(*
({
f  x = a[(f x + 1), (g x)];
g  x = if =(x, 0) then c[(g 0)] else b[(g x - 1)];
main  = (f 0);
}, main)

{
{q0, q1, q2}
{(a -> 2), (b -> 1), (c -> 1)}
q0
{(q0, a) => {{(1, q0)}, {(2, q0)}},
(q1, a) => {{(1, q1)}, {(2, q1)}},
(q2, a) => {{(1, q1)}, {(2, q1)}},
(q0, b) => {{(1, q1)}},
(q1, b) => {{(1, q1)}},
(q2, b) => {{(1, q1)}},
(q0, c) => {{(1, q0)}},
(q1, c) => {{(1, q2)}},
(q2, c) => {{(1, q2)}}}
{(q0 -> 1), (q1 -> 1), (q2 -> 2)}
}
*)

Add LoadPath "../".
Require Import HflTactics.
Section ex2_3.
  
  Definition main_q0_0 :=
    (fun g'_q2_2:(nat -> dom o) => (fun f'_q0_1:((nat -> dom o) -> (nat -> dom o)) => (fun g'_q0_1:((nat -> dom o) -> (nat -> dom o)) => (fun f'_q0_0:((nat -> dom o) -> (((nat -> dom o) -> (nat -> dom o)) -> (((nat -> dom o) -> (nat -> dom o)) -> (nat -> dom o)))) => ((((f'_q0_0  g'_q2_2)  f'_q0_1)  g'_q0_1)  0))))).
  Definition f_q0_0 :=
    (fun g'_q2_2:(nat -> dom o) => (fun f'_q0_1:((nat -> dom o) -> (nat -> dom o)) => (fun g'_q0_1:((nat -> dom o) -> (nat -> dom o)) => (fun x_:nat => (((f'_q0_1  g'_q2_2)  (x_ + 1)) \/ ((g'_q0_1  g'_q2_2)  x_)))))).
  Definition g_q1_1t :=
    (ar (arint o) (arint o)).
  Definition g_q1_1gen :=
    (fun g_q1_1:(dom  g_q1_1t) => (fun g'_q2_2:(nat -> dom o) => (fun x_:nat => (((x_ = 0) /\ (g'_q2_2  0)) \/ (~(x_ = 0) /\ ((g_q1_1  g'_q2_2)  (x_ - 1))))))).
  Variable g_q1_1 : 
    (dom  g_q1_1t).
  Variable Mg_q1_1 : 
    mono g_q1_1t g_q1_1.
  Variable Mg_q1_1gen : 
    mono (ar g_q1_1t g_q1_1t) g_q1_1gen.
  Variable FPg_q1_1 : 
    forall arg1: (nat -> dom o), forall arg2: nat, ((mono  (arint o) arg1) -> ((g_q1_1  arg1 arg2) <-> (g_q1_1gen  g_q1_1 arg1 arg2))).
  Variable LFPg_q1_1 : 
    forall arg3: (dom  g_q1_1t),  mono g_q1_1t arg3
                                    -> ord g_q1_1t (g_q1_1gen arg3) arg3
                                    -> ord g_q1_1t g_q1_1 arg3.
  Definition g_q0_1t :=
    (ar (arint o) (arint o)).
  Definition g_q0_1gen :=
    (fun g_q0_1:(dom  g_q0_1t) => (fun g'_q2_2:(nat -> dom o) => (fun x_:nat => (((x_ = 0) /\ ((g_q0_1  g'_q2_2)  0)) \/ (~(x_ = 0) /\ ((g_q1_1  g'_q2_2)  (x_ - 1))))))).
  Variable g_q0_1 : 
    (dom  g_q0_1t).
  Variable Mg_q0_1 : 
    mono g_q0_1t g_q0_1.
  Variable Mg_q0_1gen : 
    mono (ar g_q0_1t g_q0_1t) g_q0_1gen.
  Variable FPg_q0_1 : 
    forall arg4: (nat -> dom o), forall arg5: nat, ((mono  (arint o) arg4) -> ((g_q0_1  arg4 arg5) <-> (g_q0_1gen  g_q0_1 arg4 arg5))).
  Variable LFPg_q0_1 : 
    forall arg6: (dom  g_q0_1t),  mono g_q0_1t arg6
                                    -> ord g_q0_1t (g_q0_1gen arg6) arg6
                                    -> ord g_q0_1t g_q0_1 arg6.
  Definition f_q0_1t :=
    (ar (arint o) (arint o)).
  Definition f_q0_1gen :=
    (fun f_q0_1:(dom  f_q0_1t) => (fun g'_q2_2:(nat -> dom o) => (fun x_:nat => (((f_q0_1  g'_q2_2)  (x_ + 1)) \/ ((g_q0_1  g'_q2_2)  x_))))).
  Variable f_q0_1 : 
    (dom  f_q0_1t).
  Variable Mf_q0_1 : 
    mono f_q0_1t f_q0_1.
  Variable Mf_q0_1gen : 
    mono (ar f_q0_1t f_q0_1t) f_q0_1gen.
  Variable FPf_q0_1 : 
    forall arg7: (nat -> dom o), forall arg8: nat, ((mono  (arint o) arg7) -> ((f_q0_1  arg7 arg8) <-> (f_q0_1gen  f_q0_1 arg7 arg8))).
  Variable LFPf_q0_1 : 
    forall arg9: (dom  f_q0_1t),  mono f_q0_1t arg9
                                    -> ord f_q0_1t (f_q0_1gen arg9) arg9
                                    -> ord f_q0_1t f_q0_1 arg9.
  Definition g_q2_2t :=
    (arint o).
  Definition g_q2_2gen :=
    (fun g_q2_2:(dom  g_q2_2t) => (fun x_:nat => (((x_ = 0) /\ (g_q2_2  0)) \/ (~(x_ = 0) /\ ((g_q1_1  g_q2_2)  (x_ - 1)))))).
  Variable g_q2_2 : 
    (dom  g_q2_2t).
  Variable Mg_q2_2 : 
    mono g_q2_2t g_q2_2.
  Variable Mg_q2_2gen : 
    mono (ar g_q2_2t g_q2_2t) g_q2_2gen.
  Variable FPg_q2_2 : 
    forall arg10: nat, ((g_q2_2  arg10) <-> (g_q2_2gen  g_q2_2 arg10)).
  Variable GFPg_q2_2 : 
    forall arg11: (dom  g_q2_2t),  mono g_q2_2t arg11
                                    -> ord g_q2_2t arg11 (g_q2_2gen arg11)
                                    -> ord g_q2_2t arg11 g_q2_2.
  Load "ex2_3_tactics.v". 

  Theorem ex2_3:
     ((((main_q0_0  g_q2_2)  f_q0_1)  g_q0_1)  f_q0_0).
  Proof.

  (* proof *)

  Qed.
End ex2_3.
