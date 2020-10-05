From iris.proofmode Require Import tactics classes.
From mwp Require Import mwp mwp_adequacy mwp_lifting.
From iris.program_logic Require Export ectxi_language ectx_language language.

Section mwp_id.
  Context {Λ Σ} (mwpD_SI : state Λ → iProp Σ).

  Definition mwpd_id : mwpData Λ Σ :=
    {| mwpD_state_interp := mwpD_SI;
       mwpD_Extra := [Prod];
       mwpD_modality_index := [Prod];
       mwpD_modality_bind_condition idx idx' f Ξ := Ξ = λ _, id;
       mwpD_modality idx E n Φ := Φ tt |}.

  Global Instance mwpC_id : mwpC mwpd_id.
  Proof.
    split.
    - by intros idx E m n P Q HPQ; simpl.
    - intros idx E1 E2 n P Q ?; simpl. by iIntros "H ?"; iApply "H".
    - by intros P E n.
    - by intros idx E n m P ? ? ? ->; simpl.
  Qed.

  Global Program Instance mwp_id_SplitForStep idx : mwpMSplitForStep mwpd_id idx :=
    {|
      mwpM_split_for_step_M1 E P := P;
      mwpM_split_for_step_M2 E P := P;
    |}%I.
  Next Obligation.
  Proof.
    by iIntros (idx [] E P) "HP /="; rewrite /mwpC_modality /mwpD_modality /=.
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    by iApply "HPQ".
  Qed.
  Next Obligation.
  Proof.
    iIntros (idx E P Q) "HPQ HP /=".
    by iApply "HPQ".
  Qed.

  Lemma mwp_id_bind K `{!LanguageCtx K} idx E e Φ :
    MWP@{mwpd_id, idx} e @ E {{ v; m,
      MWP@{mwpd_id, idx} K (of_val v) @ E {{ w; n, Φ w (m + n) }} }}
    ⊢ MWP@{mwpd_id, idx} K e @ E {{ λ v n _, Φ v n }}.
  Proof.
    iIntros "?".
    by iApply (@mwp_bind _ _ _ mwpC_id K _ _ _ _ (λ _, id)).
  Qed.

End mwp_id.

Section lifting.

Context {Λ Σ} (mwpD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_id_lift_step  E Φ e1 :
  to_val e1 = None →
    (∀ σ1, mwpD_SI σ1 -∗
     ∀ e2 σ2,
       ⌜prim_step e1 σ1 [] e2 σ2 []⌝ -∗
        (mwpD_SI σ2 ∗ MWP@{mwpd_id mwpD_SI}
                e2 @ E {{ w; n, Φ w (S n) }}))
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (mwp_lift_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_pure_step  E Φ e1 :
  to_val e1 = None →
  (∀ σ1 e2 σ2, prim_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜prim_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_id mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  intros.
  by iApply (mwp_lift_pure_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_atomic_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 -∗
     ∀ v2 σ2,
       ⌜prim_step e1 σ1 [] (of_val v2) σ2 []⌝
        -∗ (mwpD_SI σ2 ∗ Φ v2 1))
⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (??).
  by iApply (mwp_lift_atomic_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1); simpl.
Qed.

Lemma mwp_id_lift_atomic_det_step  E Φ e1 :
  to_val e1 = None →
  Atomic StronglyAtomic e1 →
  (∀ σ1, mwpD_SI σ1 -∗
     ∃ v2 σ2,
       ⌜∀ e2' σ2', prim_step e1 σ1 [] e2' σ2' [] →
                   σ2 = σ2' ∧ to_val e2' = Some v2⌝ ∧
                   mwpD_SI σ2 ∗ Φ v2 1)
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_atomic_det_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_pure_det_step  E Φ e1 e2 :
  to_val e1 = None →
  (∀ σ1 e2' σ2, prim_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_id mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(??) "H".
  iApply (mwp_lift_pure_det_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
Qed.

Lemma mwp_id_pure_step `{!Inhabited (state Λ)}  E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MWP@{mwpd_id mwpD_SI} e2 @ E {{ v ; m, Φ v (n + m) }}
  ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (Hexec Hφ) "Hic".
  iApply (mwp_pure_step (mwpd_id mwpD_SI) _); eauto.
  clear Hexec.
  iInduction n as [] "IH" forall (Φ); simpl; auto.
  iApply ("IH" $! (λ w k, Φ w (S k)) with "Hic").
Qed.

End lifting.

Section mwp_ectx_lifting.

Context {Λ : ectxLanguage}.
Context {Σ} (mwpD_SI : state Λ → iProp Σ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → iProp Σ.

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_id_lift_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
   (∀ σ1, mwpD_SI σ1 -∗
     ∀ e2 σ2,
       ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
        (mwpD_SI σ2 ∗ MWP@{mwpd_id mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }}))
     ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros; iApply (mwp_lift_head_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_pure_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_id mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  intros.
   by iApply (mwp_lift_pure_head_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_atomic_head_step  E Φ e1 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 -∗
     ∀ v2 σ2,
       ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ -∗
        (mwpD_SI σ2 ∗ Φ v2 1))
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by intros;
    iApply (mwp_lift_atomic_head_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_pure_det_head_step  E Φ e1 e2 :
  to_val e1 = None →
  sub_redexes_are_values e1 →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2')→
  MWP@{mwpd_id mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros(???) "H".
  iApply (mwp_lift_pure_det_head_step (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1);
    simpl; eauto.
Qed.

End mwp_ectx_lifting.

Section mwp_ectxi_lifting.

Context {Λ : ectxiLanguage}.
Context {Σ} (mwpD_SI : state Λ → iProp Σ).

Implicit Types P : iProp Σ.
Implicit Types Φ : (val Λ) → nat → iProp Σ.
Implicit Types v : (val Λ).
Implicit Types e : (expr Λ).

Typeclasses Transparent mwpC_state_interp mwpD_state_interp mwpC_modality.

Lemma mwp_id_lift_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
   (∀ σ1, mwpD_SI σ1 -∗
        (∀ e2 σ2,
            ⌜head_step e1 σ1 [] e2 σ2 []⌝ -∗
             (mwpD_SI σ2 ∗ MWP@{mwpd_id mwpD_SI}
                     e2 @ E {{ w; n, Φ w (S n) }})))
     ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  by iIntros (??);
    iApply (mwp_lift_head_step' (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_pure_head_step'  E Φ e1 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2 σ2, head_step e1 σ1 [] e2 σ2 [] → σ1 = σ2) →
  (∀ σ1 e2 σ2,
      ⌜head_step e1 σ1 [] e2 σ2 []⌝ →
      MWP@{mwpd_id mwpD_SI} e2 @ E {{ w; n, Φ w (S n) }})
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_head_step' (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1);
    eauto.
Qed.

Lemma mwp_id_lift_atomic_head_step'  E Φ e1:
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  Atomic StronglyAtomic e1 →
   (∀ σ1, mwpD_SI σ1 -∗
      (∀ v2 σ2,
          ⌜head_step e1 σ1 [] (of_val v2) σ2 []⌝ -∗ (mwpD_SI σ2 ∗ Φ v2 1)))
    ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???).
  by iApply (mwp_lift_atomic_head_step' (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1).
Qed.

Lemma mwp_id_lift_pure_det_head_step'  E Φ e1 e2 :
  to_val e1 = None →
  (∀ Ki e', e1 = fill_item Ki e' → is_Some (to_val e')) →
  (∀ σ1 e2' σ2, head_step e1 σ1 [] e2' σ2 [] → σ1 = σ2 ∧ e2 = e2') →
  MWP@{mwpd_id mwpD_SI} e2 @ E {{ v; n, Φ v (S n) }}
  ⊢ MWP@{mwpd_id mwpD_SI} e1 @ E {{ λ v n _, Φ v n }}.
Proof.
  iIntros (???) "?".
  iApply (mwp_lift_pure_det_head_step' (mwpd_id mwpD_SI) _ E (λ v n _, Φ v n) e1);
    eauto.
Qed.

End mwp_ectxi_lifting.

Section basmwp_soundness.
Context {Λ Σ} (mwpD_SI : state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Lemma mwp_id_adequacy_basic  E e σ Φ :
  mwpD_SI σ ∗ MWP@{mwpd_id mwpD_SI} e @ E {{ λ v n _, Φ v n }} -∗
    ∀ (rd : Reds e σ), mwpD_SI (end_state rd) ∗ Φ (end_val rd) (nstps rd).
Proof.
  iApply (mwp_adequacy_basic (mwpd_id mwpD_SI) _ E e σ (λ v n _, Φ v n)).
Qed.

End basmwp_soundness.

Section soundness.
Context {Λ Σ} {SI_data : Type} (mwpD_SI : SI_data → state Λ → iProp Σ).

Typeclasses Transparent mwpC_state_interp mwpC_modality.

Program Instance id_Initialization SSI `{!InitData SSI}:
  Initialization
    unit
    (λ x : SI_data, mwpd_id (mwpD_SI x))
    (λ x, mwpC_id (mwpD_SI x))
    (λ _, tt) :=
{|
  initialization_modality Hi P := |==> P;
  initialization_seed_for_modality _ := True;
  initialization_seed_for_state_interp x := SSI x;
  initialization_residue _ := True;
  initialization_elim_laters := 0;
  initialization_mwpCM_soundness_arg := unit;
  initialization_mwpCM_soundness_laters _ _ := 0;
  initialization_modality_initializer _ _ := True;
  initialization_mwpCM_soundness_fun _ := tt;
  initialization_Ex_conv _ x := x;
|}%I.
Next Obligation.
Proof.
  iIntros.
  iMod init_data as (?) "?".
  iModIntro; iExists _; iFrame.
Qed.
Next Obligation.
Proof.
  by iIntros (?? P Hi) "_ >HP"; iFrame.
Qed.
Next Obligation.
Proof.
  iIntros (?? Hi P E n _) "[_ [_ HP]]".
  by rewrite /mwpC_modality /mwpD_modality /=.
Qed.

Lemma mwp_id_adequacy SSI `{!InitData SSI} E e σ (Ψ : val Λ → nat → Prop):
  (∀ (x : SI_data),
  (SSI x ⊢ |==> (mwpD_SI x σ ∗ MWP@{mwpd_id (mwpD_SI x)} e @ E {{ v ; n, ⌜Ψ v n⌝ }})))
  → ∀ (rd : Reds e σ), Ψ (end_val rd) (@nstps Λ _ _ rd).
Proof.
  intros Hic rd.
  apply (mwp_adequacy _ _ _ _ (id_Initialization SSI) E e σ (λ v n _, Ψ v n) tt).
  by iIntros (?) "?"; iMod (Hic with "[$]") as "[$ $]".
Qed.

End soundness.
