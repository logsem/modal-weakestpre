From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From mwp.prelude Require Import base.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From mwp.mwp_modalities Require Import mwp_step_fupd mwp_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_left mwp_right
     mwp_logrel_fupd.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ni_logrel_lemmas.
  Context {Λ Σ} `{!invG Σ} (mwpD_SI mwpD_SI' : state Λ → iProp Σ).

  Implicit Types e : expr Λ.

  Lemma mwp_un_bi_lr e e' Φ E :
    MWP@{mwpd_step_fupd mwpD_SI} e @ E
      {{ v; m, MWP@{mwpd_step_fupd mwpD_SI'} e' @ E {{ w ; k, Φ v m (w, k)}} }} -∗
      MWP@{mwpd_left mwpD_SI mwpD_SI', e'} e @ E {{ Φ }}.
  Proof.
    do 2 rewrite mwp_eq /mwp_def /mwpC_modality /= /mwpC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI]".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI']".
    rewrite -Nat.add_sub_assoc // Nat.sub_diag Nat.add_0_r Nat.sub_diag /=.
    iModIntro; iFrame.
  Qed.

  Lemma mwp_un_bi_rl e e' Φ E :
    MWP@{mwpd_step_fupd mwpD_SI'} e' @ E
      {{ v; m, MWP@{mwpd_step_fupd mwpD_SI} e @ E {{ w ; k, Φ w k (v, m)}} }} -∗
      MWP@{mwpd_left mwpD_SI mwpD_SI', e'} e @ E {{ Φ}}.
  Proof.
    do 2 rewrite mwp_eq /mwp_def /mwpC_modality /= /mwpC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI']".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "Hics".
    iMod ("Hics") as "[Hics HSI]".
    rewrite minus_plus Nat.sub_diag /=.
    iModIntro; iFrame.
  Qed.

  Lemma mwp_double_atomic_lr a E1 E2 e e' Φ `{!Atomic a e, !Atomic a e'} :
    (|={E1,E2}=>
     MWP@{mwpd_step_fupd mwpD_SI} e @ E2
       {{ v; m,
             MWP@{mwpd_fupd mwpD_SI'}
               e' @ E2 {{ w ; k, |={E2,E1}=> Φ v m (w, k)}} }})
      -∗ MWP@{mwpd_left mwpD_SI mwpD_SI', e'} e @ E1 {{ Φ}}.
  Proof.
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd).
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd').
    destruct (n' + n) as [|m] eqn:Hnn; simpl in *.
    - assert (n = 0) as -> by lia.
      assert (n' = 0) as -> by lia.
      iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho").
      iMod "H" as "[H Ho]".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho'").
      iMod "H" as "[H Ho']".
      iMod "H".
      iModIntro.
      rewrite /mwpC_state_interp /=.
      iFrame.
    - iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho").
      destruct n as [|[]]; last lia; simpl in *.
      + iMod "H" as "[H Ho]".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho'").
        iMod "H" as "[H Ho']".
        iMod "H".
        iApply step_fupd_intro; first set_solver.
        iNext.
        iApply step_fupdN_intro. iModIntro.
        rewrite /mwpC_state_interp /=.
        iFrame.
      + iMod "H".
        iModIntro.
        iNext.
        iMod "H".
        iMod "H" as "[H Ho]".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho'").
        iMod "H" as "[H Ho']".
        iMod "H".
        iModIntro.
        iApply step_fupdN_intro. iModIntro.
        rewrite /mwpC_state_interp /=.
        iFrame.
  Qed.

  Lemma mwp_double_atomic_rl a E1 E2 e e' Φ `{!Atomic a e, !Atomic a e'} :
    (|={E1,E2}=>
     MWP@{mwpd_step_fupd mwpD_SI'} e' @ E2
       {{ v; m,
             MWP@{mwpd_fupd mwpD_SI}
               e @ E2 {{ w ; k, |={E2,E1}=> Φ w k (v, m)}} }})
      -∗ MWP@{mwpd_left mwpD_SI mwpD_SI', e'} e @ E1 {{ Φ }}.
  Proof.
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd).
    pose proof (nsteps_atomic _ _ _ _ _ _ _ _ Hrd').
    destruct (n' + n) as [|m] eqn:Hnn; simpl in *.
    - assert (n = 0) as -> by lia.
      assert (n' = 0) as -> by lia.
      iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho'").
      iMod "H" as "[H Ho']".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho").
      iMod "H" as "[H Ho]".
      iMod "H".
      iModIntro.
      rewrite /mwpC_state_interp /=.
      iFrame.
    - iMod "H".
      iSpecialize ("H" with "[]"); first done.
      iSpecialize ("H" with "Ho'").
      destruct n' as [|[]]; last lia; simpl in *.
      + iMod "H" as "[H Ho']".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho").
        iMod "H" as "[H Ho]".
        iMod "H".
        iApply step_fupd_intro; first set_solver.
        iNext.
        iApply step_fupdN_intro. iModIntro.
        rewrite /mwpC_state_interp /=.
        iFrame.
      + iMod "H".
        iModIntro.
        iNext.
        iMod "H".
        iMod "H" as "[H Ho']".
        iSpecialize ("H" with "[]"); first done.
        iSpecialize ("H" with "Ho").
        iMod "H" as "[H Ho]".
        iMod "H".
        iModIntro.
        iApply step_fupdN_intro. iModIntro.
        rewrite /mwpC_state_interp /=.
        iFrame.
  Qed.

  Lemma ni_logrel_fupd_ni_logrel E1 E2 e e' Φ  :
    ((∀ σ, mwpD_SI σ ={E1, ∅}=∗ ⌜reducible e σ⌝) ∨
     (∀ σ, mwpD_SI' σ ={E1, ∅}=∗ ⌜reducible e' σ⌝))
    ∧
    (|={E1,E2}=>
      ▷ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', e'} e @ E2 {{ v; m | [x], |={E2,E1}=> Φ v m x}})
      -∗ MWP@{mwpd_left mwpD_SI mwpD_SI', e'} e @ E1 {{ Φ }}.
  Proof.
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    destruct (n' + n) eqn:Hnn'; simpl in *.
    { apply Nat.eq_add_0 in Hnn' as [-> ->]; simpl in *.
      iDestruct "H" as "[[H|H] _]".
      - inversion Hrd; simplify_eq.
        iMod ("H" with "Ho") as %Hred%reducible_not_val.
        by rewrite to_of_val in Hred.
      - inversion Hrd'; simplify_eq.
        iMod ("H" with "Ho'") as %Hred'%reducible_not_val.
        by rewrite to_of_val in Hred'. }
    iDestruct "H" as "[_ H]".
    iMod "H".
    iMod (fupd_mask_subseteq ∅) as "Hcl"; first set_solver.
    iModIntro.
    iNext.
    iSpecialize ("H" with "[] Ho"); first done.
    iSpecialize ("H" with "[] Ho'"); first done.
    iMod "Hcl" as "_".
    iMod "H" as "[[H Ho] Ho']".
    iMod "H".
    iModIntro.
    iApply step_fupdN_intro.
    rewrite /mwpC_state_interp /mwpD_state_interp /=.
    by iModIntro; iFrame.
  Qed.

End ni_logrel_lemmas.
