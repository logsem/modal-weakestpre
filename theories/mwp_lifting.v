From iris.program_logic Require Import ectxi_language ectx_language lifting.
From mwp.prelude Require Export reduction.
From mwp Require Export mwp.
From iris.proofmode Require Import tactics.

Section lifting.
Context `(mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx `{!mwpMSplitForStep mwpd idx}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → mwpC_Extra → iProp Σ.

Lemma mwp_lift_step E Φ e1 :
  to_val e1 = None →
   (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
      (∀ e2 σ2,
          ⌜prim_step e1 σ1 [] e2 σ2 []⌝ -∗
           mwpM_split_for_step_M2 E
           (mwpC_state_interp mwpd σ2 ∗
            MWP@{mwpd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }})))
    ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hnv) "H". rewrite mwp_eq /mwp_def.
  iIntros (σ1 σ2 v n) "Hr Ho"; iDestruct "Hr" as %Hr.
  iDestruct ("H" $! σ1 with "Ho") as "H".
  inversion Hr as [|k Hs2 [e' σ'] Hs4 Hs5 Hs6]; subst; simpl in *.
  { by rewrite to_of_val in Hnv. }
  iApply mwpM_split_for_step_split.
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iIntros "Hcont".
  iDestruct ("Hcont" $! e' σ' with "[]") as "Hrest"; first done.
  iApply mwpM_split_for_step_M2_mono; iFrame.
  iIntros "[Ho Hrest]".
  by iApply "Hrest".
Qed.

(** Derived lifting lemmas. *)

Lemma mwp_lift_pure_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  mwpM_split_for_step_M1 E
    (mwpM_split_for_step_M2 E
     (∀ σ1 e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
        MWP@{mwpd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }}))
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hnv Hpr) "H".
  iApply mwp_lift_step; auto.
  iIntros (σ1) "Hsi".
  iApply (mwpM_split_for_step_M1_mono with "[Hsi] H"); iFrame.
  iIntros "H".
  iIntros (e2 σ2 Hpstp).
  iApply (mwpM_split_for_step_M2_mono with "[Hsi] H"); iFrame.
  iIntros "H".
  iSpecialize ("H" with "[]"); eauto.
  iFrame.
  by rewrite (Hpr _ _ _ Hpstp).
Qed.

Lemma mwp_lift_atomic_step E Φ e1 :
  Atomic StronglyAtomic e1 →
  to_val e1 = None →
  (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
      (∀ v2 σ2,
          ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
           -∗ mwpM_split_for_step_M2 E
             (mwpC_state_interp mwpd σ2 ∗ mwpC_modality mwpd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hatomic Hnv) "H".
  iApply mwp_lift_step; auto.
  iIntros (σ1) "Hsi".
  iSpecialize ("H" with "Hsi").
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iIntros (e2 σ2 Hpstp).
  destruct (Hatomic _ _ _ _ _ Hpstp) as [v2 ?%of_to_val]; simplify_eq.
  iSpecialize ("H" with "[]"); eauto.
  iApply mwpM_split_for_step_M2_mono; iFrame.
  iIntros "[$ H]".
  by iApply mwp_value.
Qed.

Lemma mwp_lift_atomic_det_step E Φ e1 :
  Atomic StronglyAtomic e1 →
  to_val e1 = None →
  (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
        (∃ v2 σ2,
            ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                        σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                        mwpM_split_for_step_M2 E
                              (mwpC_state_interp mwpd σ2 ∗
                               mwpC_modality mwpd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hatomic Hnv) "H". iApply (mwp_lift_atomic_step); first done.
  iIntros (σ1) "Ho"; iSpecialize ("H" $! _ with "Ho").
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iDestruct 1 as (v2 σ2 Hdet) "H".
  iIntros (v3 σ3 Hrd).
  iApply mwpM_split_for_step_M2_mono; iFrame.
  iIntros "H".
  destruct (Hdet _ _ Hrd) as [? ?%of_to_val]; simplify_eq.
  iFrame.
Qed.

Lemma mwp_lift_pure_det_step E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  mwpM_split_for_step_M1 E
    (mwpM_split_for_step_M2 E (MWP@{mwpd, idx}
                               e2 @ E {{ v; n | [x], Φ v (S n) x }}))
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "?". iApply (mwp_lift_pure_step); eauto.
  - by intros; eapply Hpuredet.
  - iApply mwpM_split_for_step_M1_mono; iFrame. iIntros "?".
    iApply mwpM_split_for_step_M2_mono; iFrame. iIntros "?".
      by iIntros (e' σ σ' (->&->)%Hpuredet).
Qed.

Lemma mwp_pure_step `{!Inhabited (state Λ)} E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  Nat.iter n (λ P, mwpM_split_for_step_M1 E
     (mwpM_split_for_step_M2 E P))
           (MWP@{mwpd, idx} e2 @ E {{ v ; m | [x], Φ v (n + m) x }})
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH" forall (Φ); simpl; first done.
  iApply (mwp_lift_pure_det_step _ _ _ e2).
  - specialize (Hsafe inhabitant).
    eauto using reducible_no_obs_reducible, reducible_not_val.
  - intros ? ? ? Hpstp.
    by destruct (pure_step_det _ _ _ _ _ Hpstp) as (?&?&?&?); simplify_eq.
  - iApply mwpM_split_for_step_M1_mono; iFrame. iIntros "?".
    iApply mwpM_split_for_step_M2_mono; iFrame. iIntros "H".
    by iApply ("IH" with "[H]").
Qed.

Lemma mwp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ, mwpC_state_interp mwpd σ -∗
     mwpM_split_for_step_M1 E
     ⌜stuck e σ⌝)
  ⊢ MWP@{mwpd, idx} e @ E {{ Φ }}.
Proof.
  iIntros (Hnv) "H". rewrite mwp_eq /mwp_def.
  iIntros (σ1 σ2 v n) "Hr Hσ1"; iDestruct "Hr" as %Hr.
  iSpecialize ("H" $! _ with "Hσ1").
  inversion Hr as [|k Hs2 [e' σ'] Hs4 Hs5 Hs6]; subst; simpl in *.
  { by rewrite to_of_val in Hnv. }
  iApply mwpM_split_for_step_split.
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iIntros "[_ Hirr]"; iDestruct "Hirr" as %Hirr.
  by case: (Hirr [] e' σ' []).
Qed.

End lifting.


(** Some derived lemmas for ectx-based languages *)
Section mwp_ectx_lifting.

Context {Λ : ectxLanguage}.
Context `(mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx `{!mwpMSplitForStep mwpd idx}.

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → mwpC_Extra → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).
Hint Resolve head_prim_reducible head_reducible_prim_step
     nf_head_red_head_red nf_head_reducible_nf_reducible : core.

Lemma mwp_ectx_bind K E e idx' f g Φ :
  mwpC_modality_bind_condition mwpd idx idx' f g →
  MWP@{mwpd, idx'} e @ E {{ v ; n | [x],
    MWP@{mwpd, f x} fill K (of_val v) @ E {{ w; m | [y], Φ w (n + m) (g x y) }} }}
     ⊢ MWP@{mwpd, idx} fill K e @ E {{ Φ }}.
Proof. apply: mwp_bind. Qed.

Lemma not_ectx_prim_step e1 σ1 κ e2 σ2 efs :
  sub_redexes_are_values e1 →
  ectx_language.prim_step e1 σ1 κ e2 σ2 efs → head_step e1 σ1 κ e2 σ2 efs.
Proof.
  intros Hnctx Hps.
  inversion Hps. subst.
  erewrite (Hnctx K); eauto.
  - by rewrite !fill_empty.
  - by eapply val_head_stuck.
Qed.

Hint Resolve not_ectx_prim_step : core.

Lemma mwp_lift_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
             mwpM_split_for_step_M2 E
             (mwpC_state_interp mwpd σ2 ∗
               MWP@{mwpd, idx} e2 @ E {{  w; n | [x], Φ w (S n) x }})))
     ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hnv Hnctx) "H". iApply (mwp_lift_step mwpd); first done.
  iIntros (σ1) "Ho".
  iSpecialize ("H" with "Ho").
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iIntros (e2 σ2) "%".
  iSpecialize ("H" $! e2 σ2 with "[]"); eauto.
Qed.

Lemma mwp_lift_pure_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  mwpM_split_for_step_M1 E
    (mwpM_split_for_step_M2 E
      (∀ σ1 e2 σ2,
          ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
          MWP@{mwpd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }}))
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "H".
  iApply (mwp_lift_pure_step mwpd); eauto.
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iApply mwpM_split_for_step_M2_mono; iFrame.
  iIntros "H".
  iIntros (????). iApply "H"; eauto.
Qed.

Lemma mwp_lift_atomic_head_step E Φ e1:
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
           -∗ mwpM_split_for_step_M2 E
           (mwpC_state_interp mwpd σ2 ∗
            mwpC_modality mwpd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "H". iApply (mwp_lift_atomic_step mwpd); first done.
  iIntros (σ1) "Ho".
  iSpecialize ("H" with "Ho").
  iApply mwpM_split_for_step_M1_mono; iFrame.
  iIntros "H".
  iIntros (e2 σ2) "%".
  iSpecialize ("H" $! e2 σ2 with "[]"); auto.
Qed.

Lemma mwp_lift_pure_det_head_step E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  mwpM_split_for_step_M1 E
    (mwpM_split_for_step_M2 E
      (MWP@{mwpd, idx} e2 @ E {{  v; n | [x], Φ v (S n) x }}))
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof. intros. apply mwp_lift_pure_det_step; eauto. Qed.

Lemma head_pure_lang :
  (∀ (e1 : expr Λ) σ1 σ2 e2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  PureLang Λ.
Proof.
  intros Hh e1 σ1 σ2 e2 Hps; simpl in *.
  inversion Hps; simpl in *; simplify_eq.
  eapply Hh; eauto.
Qed.

End mwp_ectx_lifting.

Section mwp_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context `(mwpd : mwpData Λ Σ) `{!mwpC mwpd} idx `{!mwpMSplitForStep mwpd idx}.

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → mwpC_Extra → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).
Hint Resolve head_prim_reducible head_reducible_prim_step
     nf_head_red_head_red nf_head_reducible_nf_reducible : core.

Hint Resolve ectxi_language_sub_redexes_are_values : core.

Lemma mwp_lift_head_step' E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
             mwpM_split_for_step_M2 E
             (mwpC_state_interp mwpd σ2 ∗
              MWP@{mwpd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }})))
     ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (??); iApply mwp_lift_head_step; eauto. Qed.

Lemma mwp_lift_pure_head_step' E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  mwpM_split_for_step_M1 E
    (mwpM_split_for_step_M2 E
      (∀ σ1 e2 σ2,
          ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
          MWP@{mwpd, idx} e2 @ E {{ w; n | [x], Φ w (S n) x }}))
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (???); iApply mwp_lift_pure_head_step; eauto. Qed.

Lemma mwp_lift_atomic_head_step' E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpC_state_interp mwpd σ1 -∗
      mwpM_split_for_step_M1 E
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
           -∗ mwpM_split_for_step_M2 E
           (mwpC_state_interp mwpd σ2 ∗ mwpC_modality mwpd idx E 0 (λ x, Φ v2 1 x))))
    ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (???); iApply mwp_lift_atomic_head_step; eauto. Qed.

Lemma mwp_lift_pure_det_head_step' E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  mwpM_split_for_step_M1 E
    (mwpM_split_for_step_M2 E
      (MWP@{mwpd, idx} e2 @ E {{ v; n | [x], Φ v (S n) x }}))
  ⊢ MWP@{mwpd, idx} e1 @ E {{ Φ }}.
Proof. iIntros (???); iApply mwp_lift_pure_det_head_step; eauto. Qed.

End mwp_ectxi_lifting.
