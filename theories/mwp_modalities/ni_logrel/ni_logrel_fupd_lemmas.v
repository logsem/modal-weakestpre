From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From mwp.prelude Require Import base.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From mwp.mwp_modalities Require Import mwp_fupd.
From mwp.mwp_modalities.ni_logrel Require Import mwp_logrel_fupd.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section ni_logrel_fupd_lemmas.
  Context {Λ Σ} `{!invG Σ} (mwpD_SI mwpD_SI' : state Λ → iProp Σ).

  Implicit Types e : expr Λ.

  Lemma mwp_un_bi_fupd_lr e e' Φ E :
    MWP@{mwpd_fupd mwpD_SI} e @ E
      {{ v; m, MWP@{mwpd_fupd mwpD_SI'} e' @ E {{ w ; k, Φ v m (w, k)}} }} -∗
      MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', e'} e @ E {{ Φ }}.
  Proof.
    do 2 rewrite mwp_eq /mwp_def /mwpC_modality /= /mwpC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "[Hics HSI]".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "[Hics HSI']".
    iModIntro; iFrame.
  Qed.

  Lemma mwp_un_bi_fupd_rl e e' Φ E :
    MWP@{mwpd_fupd mwpD_SI'} e' @ E
      {{ v; m, MWP@{mwpd_fupd mwpD_SI} e @ E {{ w ; k, Φ w k (v, m)}} }} -∗
      MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', e'} e @ E {{ Φ }}.
  Proof.
    do 2 rewrite mwp_eq /mwp_def /mwpC_modality /= /mwpC_state_interp /=.
    iIntros "Hics" (σ1 σ2 v n Hrd) "HSI".
    iIntros (σ1' σ2' v' n' Hrd') "HSI'".
    iSpecialize ("Hics" with "[] HSI'"); first done.
    iMod ("Hics") as "[Hics HSI']".
    iSpecialize ("Hics" with "[] HSI"); first done.
    iMod ("Hics") as "[Hics HSI]".
    iModIntro; iFrame.
  Qed.

  Lemma mwp_ni_logrel_fupd_lr E1 E2 e e' Φ  :
    (|={E1,E2}=>
      MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', e'} e @ E2 {{ v; m | [x], |={E2,E1}=> Φ v m x}})
      -∗ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', e'} e @ E1 {{ Φ }}.
  Proof.
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros "H"; iIntros (σ1 σ2 v n Hrd) "Ho".
    rewrite mwp_eq /mwp_def /mwpC_modality /=.
    iIntros (σ1' σ2' v' n' Hrd') "Ho'".
    iMod "H".
    iSpecialize ("H" with "[] Ho"); first done.
    iSpecialize ("H" with "[] Ho'"); first done.
    by iMod "H" as "[[H $] $]".
  Qed.

End ni_logrel_fupd_lemmas.
