From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section mwp_fupd.
  Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

  Definition mwpd_fupd : mwpData Λ Σ :=
    {|
      mwpD_state_interp := mwpD_SI;
      mwpD_Extra := [Prod];
      mwpD_modality_index := [Prod];
      mwpD_modality_bind_condition idx idx' f Ξ := Ξ = λ _, id;
      mwpD_modality idx E n Φ := (|={E}=> Φ tt)%I
    |}.

  Global Instance mwpC_fupd : mwpC mwpd_fupd.
  Proof.
    split.
    - by intros idx E m n ? ? ?; apply fupd_ne.
    - iIntros (idx E1 E2 n Φ Ψ HE) "HPQ HP".
      iSpecialize ("HPQ" $! tt).
      iApply (fupd_wand_r with "[$HPQ HP]").
      iApply fupd_mask_mono; eauto.
    - intros idx P E n. by iIntros "HP".
    - intros idx dx' f E n m P Ξ ->; simpl.
      by iIntros ">H".
  Qed.

  Global Instance mwp_fupd_is_outer_fupd idx :
    mwpMIsOuterModal mwpd_fupd idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_fupd_is_outer_bupd idx :
    mwpMIsOuterModal mwpd_fupd idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_fupd_is_outer_except_0 idx :
    mwpMIsOuterModal mwpd_fupd idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_fupd_is_inner_fupd idx :
    mwpMIsInnerModal mwpd_fupd idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_fupd_is_inner_bupd idx :
    mwpMIsInnerModal mwpd_fupd idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">H".
  Qed.

  Global Instance mwp_fupd_is_inner_except_0 idx :
    mwpMIsInnerModal mwpd_fupd idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    by iIntros (E n P) ">>H".
  Qed.

  Global Instance mwp_fupd_AlwaysSupportsShift idx : mwpMAlwaysSupportsShift mwpd_fupd idx.
  Proof.
    rewrite /mwpMAlwaysSupportsShift /mwpC_modality /mwpD_modality /=.
    iIntros (n E1 E2 P) "H".
    by repeat iMod "H".
  Qed.

  Global Program Instance mwp_fupd_SplitForStep idx : mwpMSplitForStep mwpd_fupd idx :=
    {|
      mwpM_split_for_step_M1 E P := |={E, ∅}=> P;
      mwpM_split_for_step_M2 E P := |={∅, E}=> P;
    |}%I.
  Next Obligation.
  Proof.
    iIntros (idx n E P) "HP /=".
    rewrite /mwpC_modality /mwpD_modality /=.
    iMod "HP". by destruct n; repeat iMod "HP".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    rewrite /mwpC_modality /mwpD_modality /=.
    by iApply "HPQ".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    iMod "HP"; iModIntro. by iApply "HPQ".
  Qed.

  Lemma mwp_fupd_bind K `{!LanguageCtx K} E e Φ :
    MWP@{mwpd_fupd} e @ E {{ v; m,
      MWP@{mwpd_fupd} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ MWP@{mwpd_fupd} K e @ E {{ w; n, Φ w n }}.
  Proof.
    iIntros "?".
    by iApply (@mwp_bind _ _ _ mwpC_fupd K _ _ _ _ (λ _, id)); eauto.
  Qed.

End mwp_fupd.

Section lifting.

Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpC_state_interp mwpC_modality.

Lemma mwp_fupd_lift_step E Φ e1 :
  to_val e1 = None →
    (∀ σ1, mwpD_SI σ1 -∗
      |={E, ∅}=>
     (∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
            (mwpD_SI σ2 ∗ MWP@{mwpd_fupd mwpD_SI}
                    e2 @ E {{ w; n, Φ w (S n) }})
          )
     )
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (?).
  by iApply (mwp_lift_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_fupd_lift_pure_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_fupd mwpD_SI} e2 @ E {{w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
 Qed.

Lemma mwp_fupd_lift_atomic_step E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        (∀ v2 σ2,
            ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
             ={∅, E}=∗ (mwpD_SI σ2 ∗ (|={E}=> Φ v2 1))))
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??).
  by iApply (mwp_lift_atomic_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_fupd_lift_atomic_det_step E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
     (∃ v2 σ2,
         ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                     σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                     |={∅, E}=> mwpD_SI σ2 ∗ |={E}=> Φ v2 1))
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_atomic_det_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_fupd_lift_pure_det_step E Φ e1 e2 :
    to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_fupd mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_det_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_fupd_pure_step `{!Inhabited (state Λ)} E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MWP@{mwpd_fupd mwpD_SI} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ (λ v n _, Φ v n) }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (mwp_pure_step (mwpd_fupd mwpD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

Lemma mwp_fupd_stuck E Φ e :
  to_val e = None →
  (∀ σ, mwpD_SI σ ={E, ∅}=∗ ⌜stuck e σ⌝)
  ⊢ MWP@{mwpd_fupd mwpD_SI} e @ E {{ (λ v n _, Φ v n) }}.
Proof.
  iIntros (?) "H".
  iApply (@mwp_lift_stuck _ _ _ _ _ _); first done.
  iExact "H".
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

Typeclasses Transparent mwpC_state_interp mwpC_state_interp mwpC_modality.

Lemma mwp_fupd_lift_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_fupd mwpD_SI}
                     e2 @ E {{ w; n, Φ w (S n) }})))
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (? ?); iApply (mwp_lift_head_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_fupd_lift_pure_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_fupd mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_head_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_fupd_lift_atomic_head_step E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
          (mwpD_SI σ2 ∗ |={E}=> Φ v2 1)))
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (mwp_lift_atomic_head_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
 Qed.

Lemma mwp_fupd_lift_pure_det_head_step E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_fupd mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_det_head_step (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1); simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

End mwp_ectx_lifting.

Section mwp_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent mwpC_state_interp mwpC_state_interp mwpC_modality.

Lemma mwp_fupd_lift_head_step' E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_fupd mwpD_SI}
                     e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??); iApply (mwp_lift_head_step' (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_fupd_lift_pure_head_step' E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
   (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       MWP@{mwpd_fupd mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_head_step' (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_fupd_lift_atomic_head_step' E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
            (mwpD_SI σ2 ∗ |={E}=> Φ v2 1)))
    ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???).
  by iApply (mwp_lift_atomic_head_step' (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma i_fupd_lift_pure_det_head_step' E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  MWP@{mwpd_fupd mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_fupd mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_det_head_step' (mwpd_fupd mwpD_SI) _ E (λ v n _, Φ v n) e1); eauto.
  simpl. by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

End mwp_ectxi_lifting.


Section basmwp_soundness.
Context {Λ Σ} `{!invG Σ} (mwpD_SI : state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Lemma mwp_fupd_adequacy_basic idx E e σ Φ :
  mwpD_SI σ ∗ MWP@{mwpd_fupd mwpD_SI, idx} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ),
      |={E}=> mwpD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (mwp_adequacy_basic (mwpd_fupd mwpD_SI) idx E e σ (λ v n _, Φ v n)).
Qed.

End basmwp_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ} {SI_data : Type} (mwpD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Program Instance fupd_Initialization SSI `{!InitData SSI} :
  Initialization
    unit
    (λ H : invG_pack Σ SI_data, mwpd_fupd (mwpD_SI (PIG_cnt H)))
    (λ H, @mwpC_fupd Λ Σ _ (mwpD_SI (PIG_cnt H)))
    (λ _, tt) :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x);
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_mwpCM_soundness_arg := unit;
  initialization_mwpCM_soundness_laters _ _ := 2;
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
  iIntros (? ? P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (? ? Hi P E n a) "[[Hs HE] [_ HP]]".
  iNext.
  rewrite /mwpC_modality /mwpD_modality /=.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[Hr HE]"; first set_solver.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & HP)".
  by iMod "HP".
Qed.

Lemma mwp_fupd_adequacy SSI `{!InitData SSI} E e σ (Ψ : val Λ → nat → Prop) :
  (∀ (Hcnd : invG_pack Σ SI_data),
      SSI (PIG_cnt Hcnd) ⊢
      |={⊤}=> (mwpD_SI (PIG_cnt Hcnd) σ ∗
              MWP@{mwpd_fupd (mwpD_SI (PIG_cnt Hcnd))} e @ E {{ v; n, ⌜Ψ v n⌝ }}))
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (mwp_adequacy _ _ _ _ (fupd_Initialization SSI) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "?"; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
