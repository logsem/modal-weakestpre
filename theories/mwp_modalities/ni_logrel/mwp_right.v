From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.
From mwp.prelude Require Import base.

Section mwp_right.
  Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

  Typeclasses Transparent mwpC_state_interp mwpC_modality.

  Definition mwpd_right : mwpData Λ Σ :=
    {| mwpD_state_interp := mwpD_SI;
       mwpD_Extra := [Prod];
       mwpD_modality_index := [Prod nat];
       mwpD_modality_bind_condition k k' f Ξ :=
         k' ≤ k ∧ (∀ x, f x = k - k') ∧ Ξ = λ _, id;
       mwpD_modality k E n Φ := (|={E}[∅]▷=>^(n + k) |={E}=> Φ tt)%I;
    |}.

  Global Instance mwpC_right : mwpC mwpd_right.
  Proof.
    split.
    - intros k E m n P Q HPQ; simpl.
      induction n; [induction k; first by apply fupd_ne|]; simpl.
      + by rewrite IHk.
      + by rewrite IHn.
    - iIntros (k E1 E2 n P Q HE) "HPQ HP"; simpl.
      iApply step_fupdN_mask_mono; first done.
      iApply (step_fupdN_wand with "HP").
      iIntros "H"; iApply fupd_mask_mono; last iApply "HPQ"; done.
    - intros k E n P; simpl.
      induction n; simpl; first done.
      iIntros "HP". iApply step_fupd_intro; first set_solver.
      by iNext; iApply IHn.
    - intros idx idx' f g E n m P (Hidx&Hf&->); simpl in *.
      iIntros "HP".
      rewrite Hf.
      replace (n + m + idx) with (n + idx' + (m + (idx - idx'))) by lia.
      rewrite -(step_fupdN_plus (n + idx')).
      iApply (step_fupdN_wand with "HP").
      iIntros "H".
      by destruct (m + (idx - idx')); simpl; iMod "H".
  Qed.

  Global Instance mwp_right_is_outer_fupd idx :
    mwpMIsOuterModal mwpd_right idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    destruct n; first destruct idx; iMod "H"; auto.
  Qed.

  Global Instance mwp_right_is_outer_bupd idx :
    mwpMIsOuterModal mwpd_right idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    destruct n; first destruct idx; iMod "H"; auto.
  Qed.

  Global Instance mwp_right_is_outer_except_0 idx :
    mwpMIsOuterModal mwpd_right idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    destruct n; first destruct idx; iMod "H"; auto.
  Qed.

  Global Instance mwp_right_is_inner_fupd idx :
    mwpMIsInnerModal mwpd_right idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    iApply (step_fupdN_wand with "H").
    by iIntros ">?".
  Qed.

  Global Instance mwp_right_is_inner_bupd idx :
    mwpMIsInnerModal mwpd_right idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    iApply (step_fupdN_wand with "H").
    by iIntros ">?".
  Qed.

  Global Instance mwp_right_is_inner_except_0 idx :
    mwpMIsInnerModal mwpd_right idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    iApply (step_fupdN_wand with "H").
    by iIntros ">>?".
  Qed.

  (* Global Instance mwp_right_SupportsAtomicShift idx : *)
  (*   mwpMSupportsAtomicShift mwpd_right idx. *)

  Global Program Instance mwp_right_SplitForStep idx :
    mwpMSplitForStep mwpd_right idx :=
    {|
      mwpM_split_for_step_M1 E P := |={E, ∅}=> ▷ P;
      mwpM_split_for_step_M2 E P := |={∅, E}=> P;
    |}%I.
  Next Obligation.
  Proof.
    iIntros (idx n E P) "HP /=".
    rewrite /mwpC_modality /mwpD_modality /=.
    destruct n; simpl.
    - by repeat iMod "HP".
    - by iMod "HP"; iModIntro; iNext; iMod "HP".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    by iMod "HP"; iModIntro; iApply "HPQ".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    iMod "HP"; iModIntro. by iApply "HPQ".
  Qed.

  Lemma mwp_right_bind K `{!LanguageCtx K} E e Φ n m k :
    n = m + k →
    MWP@{mwpd_right, m} e @ E {{ v; m,
      MWP@{mwpd_right, k} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ MWP@{mwpd_right, n} K e @ E {{ λ v n _, Φ v n }}.
  Proof.
    iIntros (?) "?".
    iApply (@mwp_bind _ _ _ mwpC_right K _ _ _ _ (λ _, id)); eauto.
    split_and!; simpl; auto with lia.
  Qed.

  Lemma mwpC_right_modality_le k k' E n Φ:
    k' ≤ k →
    mwpC_modality mwpd_right k' E n Φ ⊢ mwpC_modality mwpd_right k E n Φ.
  Proof.
    iIntros (Hk) "H".
    rewrite /mwpC_modality /=.
    replace (n + k) with (n + k' + (k - k')) by lia.
    rewrite -(step_fupdN_plus (n + k')).
    iApply step_fupdN_mono; last eauto.
    by iIntros "?"; iApply step_fupdN_intro.
  Qed.

  Lemma mwp_right_intro k k' E e Φ :
    k' ≤ k →
    MWP@{mwpd_right, k' } e @ E {{ Φ }} ⊢ MWP@{mwpd_right, k } e @ E {{ Φ }}.
  Proof.
    iIntros (?) "H".
    rewrite mwp_eq /mwp_def.
    iIntros (σ1 σ2 v n Hr) "Hi".
    iApply (mwpC_right_modality_le); first done.
    iApply "H"; eauto.
  Qed.

  Lemma mwp_indexed_step_fupd_index_step_fupd k k' E e Φ :
    (|={E}[∅]▷=>^k' MWP@{mwpd_right, k } e @ E {{ Φ }})%I
    ⊢ MWP@{mwpd_right, k' + k } e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    rewrite mwp_eq /mwp_def.
    iIntros (σ1 σ2 v n Hr) "Hi".
    rewrite /mwpC_modality /=.
    rewrite plus_comm -plus_assoc (plus_comm _ n).
    iApply step_fupdN_plus.
    iApply (step_fupdN_wand with "H").
    iIntros "H".
    iApply "H"; eauto.
  Qed.

End mwp_right.

Section lifting.

Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_fupd_lift_step  E Φ e1 n :
  to_val e1 = None →
    (∀ σ1, mwpD_SI σ1 -∗
      |={E, ∅}=>
     ▷ ∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
            (mwpD_SI σ2 ∗ MWP@{mwpd_right mwpD_SI, n}
                    e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (mwp_lift_step (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_right_lift_pure_step  E Φ e1 n :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_right mwpD_SI, n} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_step (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma mwp_right_lift_atommwp_step E Φ e1 n:
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        ▷ ∀ v2 σ2,
            ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
             ={∅, E}=∗ (mwpD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1))
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??).
  by iApply (mwp_lift_atommwp_step (mwpd_right mwpD_SI) n E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_right_lift_atommwp_det_step E Φ e1 n :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
     (▷ ∃ v2 σ2,
           ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                     σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                     |={∅, E}=> mwpD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1))
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_atommwp_det_step (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_right_lift_pure_det_step  E Φ e1 e2 k :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ MWP@{mwpd_right mwpD_SI, k} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_right mwpD_SI, k} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_det_step (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma mwp_right_pure_step `{!Inhabited (state Λ)}  E e1 e2 φ n Φ k :
  PureExec φ n e1 e2 →
  φ →
  ▷^n MWP@{mwpd_right mwpD_SI, k} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ MWP@{mwpd_right mwpD_SI, k} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (mwp_pure_step (mwpd_right mwpD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply step_fupd_intro; first set_solver.
  iNext.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

End lifting.

Section mwp_ectx_lifting.

Context {Λ : ectxLanguage}.
Context {Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_right_lift_head_step  E Φ e1 n:
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        ▷ ∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_right mwpD_SI, n}
                     e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (mwp_lift_head_step (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1).
 Qed.

Lemma mwp_right_lift_pure_head_step  E Φ e1 n:
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_right mwpD_SI, n} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_head_step (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

Lemma mwp_right_lift_atommwp_head_step  E Φ e1 n:
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
     ▷ ∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
          (mwpD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1))
     ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (mwp_lift_atommwp_head_step
              (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_right_lift_pure_det_head_step  E Φ e1 e2 n :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ MWP@{mwpd_right mwpD_SI, n} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_det_head_step
            (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply step_fupd_intro; first set_solver.
Qed.

End mwp_ectx_lifting.

Section mwp_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_right_lift_head_step' E Φ e1 n :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        ▷ (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_right mwpD_SI, n}
                     e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_head_step' (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_right_lift_pure_head_step'  E Φ e1 n :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
   ▷ (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       MWP@{mwpd_right mwpD_SI, n} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_head_step'
            (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply step_fupd_intro; first set_solver.
Qed.

Lemma mwp_right_lift_atommwp_head_step'  E Φ e1 n:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
      ▷ (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
          ={∅, E}=∗ (mwpD_SI σ2 ∗ |={E}[∅]▷=>^n |={E}=> Φ v2 1)))
    ⊢ MWP@{mwpd_right mwpD_SI, n} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???).
  by iApply (mwp_lift_atommwp_head_step'
               (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_right_lift_pure_det_head_step'  E Φ e1 e2 k:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  MWP@{mwpd_right mwpD_SI, k} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_right mwpD_SI, k} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_det_head_step'
            (mwpd_right mwpD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply step_fupd_intro; first set_solver.
Qed.

End mwp_ectxi_lifting.

Section basmwp_soundness.
Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Lemma mwp_right_adequacy_basic  E e σ Φ k :
  mwpD_SI σ ∗ MWP@{mwpd_right mwpD_SI, k} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ),
      |={E}[∅]▷=>^(nstps rd + k)
        |={E}=> mwpD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (mwp_adequacy_basic (mwpd_right mwpD_SI) k E e σ (λ v n _, Φ v n)).
Qed.

End basmwp_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ} {SI_data : Type} (mwpD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Program Instance right_Initialization SSI `{!InitData SSI} k :
  Initialization
    unit
    (λ x : invG_pack Σ SI_data, mwpd_right (mwpD_SI (PIG_cnt x)))
    (λ x, @mwpC_right Λ Σ _ (mwpD_SI (PIG_cnt x)))
    (λ _, k) :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x);
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_mwpCM_soundness_arg := unit;
  initialization_mwpCM_soundness_laters n _ := S (S n + k);
  initialization_modality_initializer _ _ := True;
  initialization_mwpCM_soundness_fun _ := tt;
  initialization_Ex_conv _ x := x;
|}%I.
Next Obligation.
Proof.
  intros; simpl.
  iApply (init_data (λ x, _ ∗ SSI (PIG_cnt x)))%I.
Qed.
Next Obligation.
Proof.
  iIntros (?? _ P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (?? k Hi P E n _) "[[Hs HE] [_ HP]]".
  iNext.
  rewrite /mwpC_modality /mwpD_modality /=.
  rewrite uPred_fupd_eq /uPred_fupd_def /=.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[_ HE]"; first set_solver.
  iInduction n as [] "IH".
  { simpl.
    iInduction k as [] "IH".
    {
      iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
        by iMod "HP". }
    simpl.
    iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
    iMod "HP"; iMod "Hs"; iMod "HE".
    iNext.
    iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
    iMod "HP"; iMod "Hs"; iMod "HE".
    iApply ("IH" with "Hs HP HE").
  }
  simpl.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iNext.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iApply ("IH" with "Hs HP HE").
Qed.

Lemma mwp_right_adequacy SSI `{!InitData SSI} (k : nat) E e σ (Ψ : val Λ → nat → Prop):
  (∀ (x : invG_pack Σ SI_data),
     SSI (PIG_cnt x) ⊢ |={⊤}=> mwpD_SI (PIG_cnt x) σ ∗
                              MWP@{mwpd_right (mwpD_SI (PIG_cnt x)), k}
                              e @ E {{ v ; n,  ⌜Ψ v n⌝ }})
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (mwp_adequacy _ _ _ _ (right_Initialization SSI k) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "? /="; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
