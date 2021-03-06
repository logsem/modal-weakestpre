From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Export ectxi_language ectx_language language.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From mwp.modalities Require Import future.

(************************************************************************)
(** The mwp_future constructed here out of mwp and the future modality **)
(** first appeared in our POPL'18 paper on the ST monad. There, it     **)
(** simply referred to as the ic/ic triple.                            **)
(**                                                                    **)
(** The mwp/mwp triple in this development is a generalization of that **)
(** idea which allows arbitrary modality in place of the future        **)
(** modality.                                                          **)
(************************************************************************)

Section mwp_future.
  Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

  Typeclasses Transparent mwpC_state_interp mwpC_modality.

  Definition mwpd_future : mwpData Λ Σ :=
    {| mwpD_state_interp := mwpD_SI;
       mwpD_Extra := [Prod];
       mwpD_modality_index := [Prod];
       mwpD_modality_bind_condition idx idx' f Ξ := Ξ = λ _, id;
       mwpD_modality idx E n Φ := (|≫{E}=[n]=> Φ tt)%I
    |}.

  Global Instance mwpC_future : mwpC mwpd_future.
  Proof.
    split.
    - intros idx E m n P Q HPQ; simpl. by apply future_ne.
    - iIntros (idx E1 E2 n P Q HE) "HPQ HP"; simpl.
      iApply future_mask_mono; first done.
      iApply (future_wand_l with "[HPQ $HP]"); eauto.
    - intros idx E n P; simpl.
      by iIntros ">?"; iModIntro.
    - intros idx idx' f E n m P ? ->; simpl. by rewrite future_plus.
  Qed.

  Global Instance mwp_future_is_outer_fupd idx :
    mwpMIsOuterModal mwpd_future idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_future_is_outer_bupd idx :
    mwpMIsOuterModal mwpd_future idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_future_is_outer_except_0 idx :
    mwpMIsOuterModal mwpd_future idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_future_is_inner_fupd idx :
    mwpMIsInnerModal mwpd_future idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">>H"; iModIntro.
  Qed.

  Global Instance mwp_future_is_inner_bupd idx :
    mwpMIsInnerModal mwpd_future idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">>H"; iModIntro.
  Qed.

  Global Instance mwp_future_is_inner_except_0 idx :
    mwpMIsInnerModal mwpd_future idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">>H"; iModIntro.
  Qed.

  Global Program Instance mwp_future_SplitForStep idx : mwpMSplitForStep mwpd_future idx :=
    {|
      mwpM_split_for_step_M1 E P := |={E, ∅}=> P;
      mwpM_split_for_step_M2 E P := |={∅, E}=> ▷ |={E}=> P;
    |}%I.
  Next Obligation.
  Proof.
    iIntros (idx n E P) "HP /=".
    rewrite /mwpC_modality /mwpD_modality /=.
    rewrite future_S.
    by repeat iMod "HP"; iModIntro; iNext; iMod "HP".
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

  Lemma mwp_future_bind K `{!LanguageCtx K} idx E e Φ :
    MWP@{mwpd_future, idx} e @ E {{ v; m,
      MWP@{mwpd_future, idx} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ MWP@{mwpd_future, idx} K e @ E {{ λ v n _, Φ v n }}.
  Proof.
    iIntros "?".
    by iApply (@mwp_bind _ _ _ mwpC_future K _ _ _ _ (λ _, id)); eauto.
  Qed.

End mwp_future.

Section lifting.

Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_future_lift_step  E Φ e1 :
  to_val e1 = None →
    (∀ σ1, mwpD_SI σ1 -∗
      |={E, ∅}=>
     (∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗ ▷ |={E}=>
            (mwpD_SI σ2 ∗ MWP@{mwpd_future mwpD_SI}
                    e2 @ E {{ w; n, Φ w (S n) }})
          )
     )
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (mwp_lift_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1).
 Qed.

Lemma mwp_future_lift_pure_step  E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  ▷ (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_future mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  by iNext; iModIntro.
 Qed.

Lemma mwp_future_lift_atomic_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        ∀ v2 σ2,
          ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
          ={∅, E}=∗ ▷ |={E}=> (mwpD_SI σ2 ∗ |={E}=> Φ v2 1))
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??). setoid_rewrite <- future_unfold_O at 2.
  by iApply (mwp_lift_atomic_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl.
Qed.

Lemma mwp_future_lift_atomic_det_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
     ∃ v2 σ2,
       ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                   σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                   |={∅, E}=> ▷ |={E}=> mwpD_SI σ2 ∗ |={E}=> Φ v2 1)
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??). setoid_rewrite <- future_unfold_O at 2.
  by iApply (mwp_lift_atomic_det_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_future_lift_pure_det_step  E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  ▷ MWP@{mwpd_future mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ (λ v n _, Φ v n) }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_det_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  by iNext; iModIntro.
Qed.

Lemma mwp_future_pure_step `{!Inhabited (state Λ)}  E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n MWP@{mwpd_future mwpD_SI} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (mwp_pure_step (mwpd_future mwpD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  iNext. iModIntro.
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

Lemma mwp_future_lift_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        ∀ e2 σ2,
          ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗ ▷ |={E}=>
          (mwpD_SI σ2 ∗ MWP@{mwpd_future mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (mwp_lift_head_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1).
 Qed.

Lemma mwp_future_lift_pure_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_future mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_head_step (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  by iNext; iModIntro.
Qed.

Lemma mwp_future_lift_atomic_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
      ∀ v2 σ2,
        ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗ ▷ |={E}=>
    (mwpD_SI σ2 ∗ |={E}=> Φ v2 1))
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  intros. setoid_rewrite <- future_unfold_O at 2.
  by iApply (mwp_lift_atomic_head_step
               (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_future_lift_pure_det_head_step  E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_future mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_det_head_step
            (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  by iNext; iModIntro.
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

Lemma mwp_future_lift_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             ▷ |={E}=> (mwpD_SI σ2 ∗ MWP@{mwpd_future mwpD_SI}
                              e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_head_step' (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_future_lift_pure_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
   ▷ (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       MWP@{mwpd_future mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_head_step'
            (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. iApply fupd_mask_intro_subseteq; first set_solver.
  by iNext; iModIntro.
Qed.

Lemma mwp_future_atomic_head_step'  E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝
          ={∅, E}=∗ ▷ |={E}=> (mwpD_SI σ2 ∗ |={E}=> Φ v2 1)))
    ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???). setoid_rewrite <- future_unfold_O at 2.
  by iApply (mwp_lift_atomic_head_step'
               (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_future_pure_det_head_step'  E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  MWP@{mwpd_future mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_future mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_det_head_step'
            (mwpd_future mwpD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. iApply fupd_mask_intro_subseteq; first set_solver.
  by iNext; iModIntro.
Qed.

End mwp_ectxi_lifting.

Section basmwp_soundness.
Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Lemma mwp_future_adequacy_basic  E e σ Φ :
  mwpD_SI σ ∗ MWP@{mwpd_future mwpD_SI} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ),
     |≫{E}=[nstps rd]=> mwpD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (mwp_adequacy_basic (mwpd_future mwpD_SI) _ E e σ (λ v n _, Φ v n)).
Qed.

End basmwp_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ} {SI_data : Type} (mwpD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Program Instance future_Initialization SSI `{!InitData SSI}:
  Initialization
    unit
    (λ H : invG_pack Σ SI_data, mwpd_future (mwpD_SI (PIG_cnt H)))
    (λ H, @mwpC_future Λ Σ _ (mwpD_SI (PIG_cnt H)))
    (λ _, tt) :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x);
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_mwpCM_soundness_arg := unit;
  initialization_mwpCM_soundness_laters n _ := S (S n);
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
  iIntros (?? P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (?? Hi P E n _) "[[Hs HE] [_ HP]]".
  iNext.
  rewrite /mwpC_modality /mwpD_modality /=.
  rewrite future_eq /future_def /=.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[_ HE]"; first set_solver.
  iInduction n as [] "IH"; simpl.
  { iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
    by iMod "HP". }
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  iMod "HP"; iMod "Hs"; iMod "HE".
  iNext.
  iApply ("IH" with "Hs HP HE").
Qed.

Lemma mwp_future_adequacy SSI `{!InitData SSI} E e σ (Ψ : val Λ → nat → Prop):
  (∀ (Hcnd : invG_pack Σ SI_data),
      SSI (PIG_cnt Hcnd) ⊢ |={⊤}=> (mwpD_SI (PIG_cnt Hcnd) σ ∗
                  MWP@{mwpd_future (mwpD_SI (PIG_cnt Hcnd))}
                  e @ E {{ v ; n, ⌜Ψ v n⌝ }}))
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (mwp_adequacy _ _ _ _ (future_Initialization SSI) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "?"; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
