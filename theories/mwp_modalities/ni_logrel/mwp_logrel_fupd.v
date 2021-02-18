From iris.base_logic.lib Require Export fancy_updates wsat.
From iris.proofmode Require Import base tactics classes.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From mwp.mwp_modalities Require Import mwp_fupd.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section mwp_logrel_fupd.
  Context {Λ Σ} `{!invG Σ} (mwpD_SI mwpD_SI' : state Λ → iProp Σ).
  Typeclasses Transparent mwpC_state_interp mwpC_modality.

  Definition mwpd_logrel_fupd : mwpData Λ Σ :=
    {| mwpD_state_interp := mwpD_SI;
       mwpD_Extra := [Prod val Λ; nat];
       mwpD_modality_index := [Prod expr Λ];
       mwpD_modality_bind_condition e1 e2 f g :=
         ∃ K (_: LanguageCtx K),
           e1 = K e2 ∧ g = (λ x y, (y.1, x.2 + y.2)) ∧
           ∀ v k, f (v, k) = K (of_val v);
      mwpD_modality idx E n Φ :=
        MWP@{mwpd_fupd mwpD_SI'} idx @ E {{ w; k, Φ (w, k) }}%I;
    |}.

  Global Instance mwpC_logrel_fupd : mwpC mwpd_logrel_fupd.
  Proof.
    split.
    - intros idx E m n ? ? ?; simpl. apply mwp_ne.
      intros ? ? ?; auto.
    - intros idx E1 E2 n Φ Ψ HE; simpl.
      iIntros "HP Hic".
      iApply (mwp_strong_mono_wand _ _ _ _ _ _ (λ v m _, _)); eauto; iFrame.
      by iIntros (? ? ?) "?"; iApply "HP".
    - by iIntros (idx E n Φ) "H"; simpl.
    - intros e e' f g E n m Φ (K & HK & He & Hg & Hf); simplify_eq.
      iIntros "H"; simpl.
      iApply mwp_fupd_bind.
      iApply (mwp_strong_mono_wand _ _ _ _ _ (λ v m _, _)); eauto; iFrame.
      iIntros (v l _); rewrite Hf /=.
      iIntros "H".
      iApply (mwp_strong_mono_wand _ _ _ _ _ _ (λ v m _, _)); eauto; iFrame.
      by iIntros (? j _) "?".
  Qed.

  Global Instance mwpC_logrel_fupd_is_outer_fupd idx :
    mwpMIsOuterModal mwpd_logrel_fupd idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H". by iMod "H".
  Qed.

  Global Instance mwpC_logrel_fupd_is_outer_bupd idx :
    mwpMIsOuterModal mwpd_logrel_fupd idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H". by iMod "H".
  Qed.

  Global Instance mwpC_logrel_fupd_is_outer_except_0 idx :
    mwpMIsOuterModal mwpd_logrel_fupd idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsOuterModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H". by iMod "H".
  Qed.

  Global Instance mwpC_logrel_fupd_is_inner_fupd idx :
    mwpMIsInnerModal mwpd_logrel_fupd idx (λ E _ P, |={E}=> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    by iApply (mwp_fupd _ _ _ _ (λ v m _, _)).
  Qed.

  Global Instance mwpC_logrel_fupd_is_inner_bupd idx :
    mwpMIsInnerModal mwpd_logrel_fupd idx (λ _ _ P, |==> P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    by iApply (mwp_bupd _ _ _ _ (λ v m _, _)).
  Qed.

  Global Instance mwpC_logrel_fupd_is_inner_except_0 idx :
    mwpMIsInnerModal mwpd_logrel_fupd idx (λ _ _ P, ◇ P)%I.
  Proof.
    rewrite /mwpMIsInnerModal /mwpC_modality /mwpD_modality /=.
    iIntros (E n P) "H".
    by iApply (mwp_except_0 _ _ _ _ (λ v m _, _)).
  Qed.

  (* Global Instance mwpC_logrel_fupd_SupportsAtomicShift idx : *)
  (*   mwpMSupportsAtomicShift mwpd_logrel_fupd idx. *)
  (* Proof. *)
  (*   rewrite /mwpMSupportsAtomicShift /mwpC_modality /mwpD_modality /=. *)
  (*   iIntros (n E1 E2 Φ Hn) "H". *)
  (*   iApply (mwp_shift (mwpd_indexed_step_fupd mwpD_SI')); *)
  (*     eauto using mwp_indexed_step_fupd_AlwaysSupportsShift. *)
  (* Qed. *)

  Global Program Instance mwpC_logrel_fupd_SplitForStep idx :
    mwpMSplitForStep mwpd_logrel_fupd idx :=
    {|
      mwpM_split_for_step_M1 E P := |={E, ∅}=> P;
      mwpM_split_for_step_M2 E P := |={∅, E}=> P;
    |}%I.
  Next Obligation.
  Proof.
    iIntros (e n E P) "HP /=".
    by do 2 iMod "HP".
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

  Lemma mwp_logrel_fupd_strong_bind
        K `{!LanguageCtx K} K' `{!LanguageCtx K'} E e e' Φ :
    MWP@{mwpd_logrel_fupd, e'} e @ E {{ v; m | w ; k,
      MWP@{mwpd_logrel_fupd, K' (of_val w)}
        K (of_val v) @ E {{ w; n | u ; y, Φ w (m + n) (u, (k + y)) }} }}
    ⊢ MWP@{mwpd_logrel_fupd, K' e'} K e @ E {{ Φ }}.
  Proof.
    iIntros "H".
    iApply (@mwp_bind _ _ _ mwpC_logrel_fupd K _ _ e'
                     (λ '(v, k), K' (of_val v))
                     (λ x y, (y.1, x.2 + y.2))).
    { rewrite /mwpC_modality_bind_condition /=; eauto. }
    iApply mwp_mono; last eauto.
    intros ? ? []; auto.
  Qed.

Lemma mwp_logrel_fupd_change_of_index e1' e2' f E e Φ :
  (∀ Ψ n,
      MWP@{mwpd_fupd mwpD_SI', n}
        e1' @ E {{ v; n | [_], Ψ (f (v, n)) }} -∗
        MWP@{mwpd_fupd mwpD_SI', n}
        e2' @ E {{ v; n | [_], Ψ (v, n) }})
  -∗ MWP@{mwpd_logrel_fupd, e1'} e @ E {{ λ v n x, Φ v n (f x) }}
  -∗ MWP@{mwpd_logrel_fupd, e2'} e @ E {{ Φ }}.
Proof.
  iIntros "Hm H".
  iApply (mwp_change_of_index mwpd_logrel_fupd with "[Hm] H").
  iIntros (Ψ n) "H".
  by iApply "Hm".
Qed.

Lemma mwp_logrel_fupd_pure_step_index `{!Inhabited (state Λ)}  e1' e2' E e Φ φ n :
  PureExec φ n e2' e1' →
  φ →
  MWP@{mwpd_logrel_fupd, e1'} e @ E {{ v;k | w;m, Φ v k (w, n + m) }}
  ⊢ MWP@{mwpd_logrel_fupd, e2'} e @ E {{ v;m | [x], Φ v m x }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (mwp_logrel_fupd_change_of_index _ _ (λ '(v, m), (v, n + m))).
  - iIntros (? []) "H".
    by iApply mwp_fupd_pure_step.
  - iApply mwp_wand_r; iSplitL; first iApply "Hic".
    by iIntros (??[]) "Hic".
Qed.

End mwp_logrel_fupd.

Section lifting.

Context {Λ Σ} `{!invG Σ} (mwpD_SI mwpD_SI': state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → val Λ * nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_fupd_lift_step idx E Φ e1 :
  to_val e1 = None →
    (∀ σ1, mwpD_SI σ1 -∗
      |={E, ∅}=>
     ∀ e2 σ2,
         ⌜prim_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
            (mwpD_SI σ2 ∗ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
                    e2 @ E {{ v; n| [x], Φ v (S n) x }}))
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "?".
  iApply (mwp_lift_step (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E); simpl; auto.
Qed.

Lemma mwp_logrel_fupd_lift_pure_step idx E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
   (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e2 @ E
        {{ v; n | [x], Φ v (S n) x }})
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_step
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E);
    simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_logrel_fupd_lift_atomic_step idx E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        ∀ v2 σ2,
            ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
             ={∅, E}=∗ (mwpD_SI σ2 ∗
                        MWP@{mwpd_fupd mwpD_SI'}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }}))
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (??).
  by iApply (mwp_lift_atomic_step
               (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E).
Qed.

Lemma mwp_logrel_fupd_lift_atomic_det_step idx E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
     (∃ v2 σ2,
         ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                     σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                     |={∅, E}=> mwpD_SI σ2 ∗
                          MWP@{mwpd_fupd mwpD_SI'}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }}))
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_atomic_det_step
              (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1).
Qed.

Lemma mwp_logrel_fupd_lift_pure_det_step idx E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
    e2 @ E {{ v; n | [x], Φ v (S n) x }}
  ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_det_step
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1);
    simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_logrel_fupd_pure_step `{!Inhabited (state Λ)} idx E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
    e2 @ E {{ v ; m | [x], Φ v (n + m) x }}
  ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (mwp_pure_step (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply fupd_mask_intro_subseteq; first set_solver.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

End lifting.

Section mwp_ectx_lifting.

Context {Λ : ectxLanguage}.
Context {Σ} `{!invG Σ} (mwpD_SI mwpD_SI' : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → val Λ * nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_logrel_fupd_lift_head_step idx E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
         ∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
                          e2 @ E {{ w; n | [x], Φ w (S n) x }}))
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by intros;
    iApply (mwp_lift_head_step
              (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1).
Qed.

Lemma mwp_logrel_fupd_lift_pure_head_step idx E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
        e2 @ E {{ w; n| [x], Φ w (S n) x }})
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_head_step
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1);
    simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_logrel_fupd_lift_atomic_head_step idx E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
     ∀ v2 σ2,
       ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
          (mwpD_SI σ2 ∗ MWP@{mwpd_fupd mwpD_SI'}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }}))
     ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by intros;
    iApply (mwp_lift_atomic_head_step
              (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1).
Qed.

Lemma mwp_logrel_fupd_lift_pure_det_head_step idx E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
    e2 @ E {{ v; n | [x], Φ v (S n) x }}
  ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_det_head_step
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1);
    simpl; eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

End mwp_ectx_lifting.

Section mwp_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} `{!invG Σ} (mwpD_SI mwpD_SI' : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → val Λ * nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_logrel_fupd_lift_head_step' idx E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ ={∅, E}=∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
                            e2 @ E {{ w; n | [x], Φ w (S n) x }})))
     ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_head_step'
              (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1).
Qed.

Lemma mwp_logrel_fupd_lift_pure_head_step' idx E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
       MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
         e2 @ E {{ w; n | [x], Φ w (S n) x }})
     ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_head_step'
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1); eauto.
   by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

Lemma mwp_logrel_fupd_lift_atomic_head_step' idx E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 ={E, ∅}=∗
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ ={∅, E}=∗
           (mwpD_SI σ2 ∗ MWP@{mwpd_fupd mwpD_SI'}
                          idx @ E {{ v; n, Φ v2 1 (v, n) }})))
    ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???).
  by iApply (mwp_lift_atomic_head_step'
               (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1).
Qed.

Lemma mwp_logrel_fupd_lift_pure_det_head_step' idx E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx}
    e2 @ E {{ v; n | [x], Φ v (S n) x }}
  ⊢ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e1 @ E {{ Φ }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_det_head_step'
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E Φ e1); eauto.
  by iApply fupd_mask_intro_subseteq; first set_solver.
Qed.

End mwp_ectxi_lifting.

Section basmwp_soundness.
Context {Λ Σ} `{!invG Σ} (mwpD_SI mwpD_SI' : state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Lemma mwp_logrel_fupd_adequacy_basic idx E e σ Φ :
  mwpD_SI σ ∗ MWP@{mwpd_logrel_fupd mwpD_SI mwpD_SI', idx} e @ E {{ λ v n x, Φ v n x.1 x.2 }} -∗
    ∀ (rd : Reds e σ),
      MWP@{mwpd_fupd mwpD_SI'}
                          idx @ E {{ v; n, mwpD_SI (end_state rd) ∗
                                          Φ (end_val rd) (nstps rd) v n }}.
Proof.
  iApply (mwp_adequacy_basic
            (mwpd_logrel_fupd mwpD_SI mwpD_SI') idx E e σ (λ v n x, Φ v n x.1 x.2)).
Qed.

End basmwp_soundness.

Section soundness.
Context {Λ Σ} `{!invPreG Σ}
        {SI_data : Type} (mwpD_SI : SI_data → state Λ → iProp Σ)
          {SI_data' : Type} (mwpD_SI' : SI_data' → state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Program Instance left_Initialization
        SSI SSI' `{!InitData SSI} `{!InitData SSI'} e' σ' :
  Initialization
    (val Λ * nat)
    (λ x : invG_pack Σ (SI_data * SI_data'),
           mwpd_logrel_fupd (mwpD_SI (PIG_cnt x).1) (mwpD_SI' (PIG_cnt x).2))
    (λ x, @mwpC_logrel_fupd Λ Σ _ (mwpD_SI (PIG_cnt x).1) (mwpD_SI' (PIG_cnt x).2))
    (λ _, e') :=
{|
  initialization_modality Hi P := |={⊤}=> P;
  initialization_seed_for_modality _ := wsat ∗ ownE ⊤;
  initialization_seed_for_state_interp x := SSI (PIG_cnt x).1 ∗ SSI' (PIG_cnt x).2;
  initialization_residue _ := ▷ wsat ∗ ▷ ownE ⊤;
  initialization_elim_laters := 1;
  initialization_mwpCM_soundness_arg := Reds e' σ';
  initialization_mwpCM_soundness_laters n rd' := 2;
  initialization_modality_initializer x _ := mwpD_SI' (PIG_cnt x).2 σ';
  initialization_mwpCM_soundness_fun rd := (end_val rd, nstps rd);
  initialization_Ex_conv _ x := x;
|}%I.
Next Obligation.
Proof.
  intros; simpl.
  iApply init_data.
  apply (init_invGpack (λ x, SSI x.1 ∗ SSI' x.2))%I.
Qed.
Next Obligation.
Proof.
  iIntros (???? e' σ' P Hi) "[Hs HE] HP".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("HP" with "[$]") as "(Hs & HE & HP)".
  iModIntro. rewrite -!bi.later_sep.
  iMod "Hs"; iMod "HE"; iMod "HP". iNext.
  iFrame.
Qed.
Next Obligation.
Proof.
  simpl.
  iIntros (???? e' σ' Hi P E n rd) "[[Hs HE] [Hσ' HP]]".
  iNext.
  rewrite /mwpC_modality /mwpD_modality /=.
  iDestruct (mwp_fupd_adequacy_basic with "[Hσ' $HP]")
    as "HP"; eauto.
  iSpecialize ("HP" $! rd).
  rewrite uPred_fupd_eq /uPred_fupd_def /=.
  replace ⊤ with ((⊤ ∖ E) ∪ E) by by rewrite difference_union_L; set_solver.
  iDestruct (ownE_op with "HE") as "[_ HE]"; first set_solver.
  iMod ("HP" with "[$Hs $HE]") as "(Hs & HE & ? & HP)".
  by iMod "HP".
Qed.

Lemma mwp_logrel_fupd_adequacy SSI SSI' `{!InitData SSI} `{!InitData SSI'}
      E e σ (e' : expr Λ) σ' (Ψ : val Λ → nat → val Λ → nat → Prop) :
  (∀ (x : invG_pack Σ (SI_data * SI_data')),
      SSI (PIG_cnt x).1 ∗ SSI' (PIG_cnt x).2
          ⊢ |={⊤}=> (mwpD_SI (PIG_cnt x).1 σ ∗ mwpD_SI' (PIG_cnt x).2 σ' ∗
                  MWP@{mwpd_logrel_fupd (mwpD_SI (PIG_cnt x).1) (mwpD_SI' (PIG_cnt x).2), e'}
                    e @ E {{ v ; n| w; k,  ⌜Ψ v n w k⌝ }}))
  → ∀ (rd : Reds e σ) (rd' : Reds e' σ'),
    Ψ (end_val rd) (@nstps Λ _ _ rd) (end_val rd') (@nstps Λ _ _ rd').
Proof.
  intros Hic rd rd'.
  by apply (mwp_adequacy
              _ _ _ _ (left_Initialization SSI SSI' e' σ') E e σ
              (λ v n x, Ψ v n x.1 x.2) rd').
Qed.

End soundness.
