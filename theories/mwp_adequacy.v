From mwp.prelude Require Import reduction.
From mwp Require Import mwp.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Import uPred.

Section adequacy.
Context {Λ Σ} (mwpd : mwpData Λ Σ) `{!mwpC mwpd}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → nat → mwpC_Extra → iProp Σ.
Implicit Types Ψ : val Λ → nat → Prop.

Record Reds e σ :=
{
  nstps : nat;
  end_val : val Λ;
  end_state : state Λ;
  reds : relations.nsteps pstep nstps (e, σ) (of_val end_val, end_state)
}.

Global Arguments nstps {_ _} _.
Global Arguments end_val {_ _} _.
Global Arguments end_state {_ _} _.
Global Arguments reds {_ _} _.

Lemma Reds_val_end_val {v σ} (rd : Reds (of_val v) σ) :
  nstps rd = 0 ∧ end_val rd = v ∧ end_state rd = σ.
Proof.
  destruct rd as [n w σ' Hstps]; simpl.
  by apply nsteps_val in Hstps as [? [?%of_val_inj ?]].
Qed.

Lemma mwp_adequacy_basic idx E e σ Φ :
  mwpC_state_interp mwpd σ ∗ MWP@{mwpd, idx} e @ E {{ Φ }} -∗
    ∀ (rd : Reds e σ),
      mwpC_modality mwpd idx E (nstps rd)
        (λ x, mwpC_state_interp mwpd (end_state rd) ∗ Φ (end_val rd) (nstps rd) x).
Proof.
  iIntros "[HPh Hic]" (rd).
  rewrite mwp_eq /mwp_def.
  iSpecialize("Hic" $! _ _ _ (nstps rd) with "[] HPh");
    first by (iPureIntro; eapply (reds rd)).
  iApply mwpC_modality_mono; last done; auto.
  iIntros (?) "[$ $]".
Qed.

End adequacy.

Class Initialization {Λ Σ} {InitCondition : Type} (Ex : Type)
      (f : InitCondition → mwpData Λ Σ)
      (mwpC : ∀ x : InitCondition, mwpC (f x))
      (idx : ∀ x : InitCondition, mwpC_modality_index) :=
{
  initialization_modality : InitCondition → iProp Σ → iProp Σ;
  initialization_seed_for_modality : InitCondition → iProp Σ;
  initialization_seed_for_state_interp : InitCondition → iProp Σ;
  initialization_residue : InitCondition → iProp Σ;
  initialization_alloc_seed :
    ⊢ |==> ∃ x : InitCondition, initialization_seed_for_modality x ∗
                               initialization_seed_for_state_interp x;
  initialization_elim_laters : nat;
  initialization_elim P Hcnd :
    ⊢ initialization_seed_for_modality Hcnd
       -∗ initialization_modality Hcnd P ==∗
       ▷^(initialization_elim_laters) P ∗ initialization_residue Hcnd;
  initialization_mwpCM_soundness_arg : Type;
  initialization_mwpCM_soundness_laters :
    nat → initialization_mwpCM_soundness_arg → nat;
  initialization_modality_initializer :
    InitCondition →
    initialization_mwpCM_soundness_arg → iProp Σ;
  initialization_mwpCM_soundness_fun : initialization_mwpCM_soundness_arg → Ex;
  initialization_Ex_conv : ∀ {x : InitCondition}, @mwpC_Extra _ _ _ (mwpC x) → Ex;
  initialization_mwpCM_soundness Hcnd (P : Ex → Prop) E n arg:
    initialization_residue Hcnd ∗ initialization_modality_initializer Hcnd arg ∗
      mwpC_modality (f Hcnd) (idx Hcnd) E n (λ x, ⌜P (initialization_Ex_conv x)⌝)
      ⊢ ▷^(initialization_mwpCM_soundness_laters n arg)
            ⌜P (initialization_mwpCM_soundness_fun arg)⌝
}.

Coercion initialization_modality : Initialization >-> Funclass.

Lemma mwp_adequacy {Λ Σ} {Condition : Type} Ex (f : Condition → mwpData Λ Σ)
      (mwpC : ∀ x : Condition, mwpC (f x))
      (idx : ∀ x : Condition, mwpC_modality_index)
      (SM : Initialization Ex f mwpC idx) E e σ
      (Ψ : val Λ → nat → Ex → Prop)
      (arg : initialization_mwpCM_soundness_arg):
  (∀ (Hcnd : Condition),
      initialization_seed_for_state_interp Hcnd ⊢
        SM Hcnd (mwpC_state_interp (f Hcnd) σ ∗
                 initialization_modality_initializer Hcnd arg ∗
                 MWP@{f Hcnd, idx Hcnd} e @ E {{ v ; n | [x],
                   ⌜Ψ v n (initialization_Ex_conv x)⌝ }}))
  → ∀ (rd : Reds e σ),
      Ψ (end_val rd) (@nstps Λ _ _ rd) (initialization_mwpCM_soundness_fun arg).
Proof.
  intros Hic rd.
  apply (@soundness (iResUR Σ) _
                    (initialization_elim_laters +
                     (initialization_mwpCM_soundness_laters (nstps rd) arg)));
    simpl.
  iMod initialization_alloc_seed as (Hcnd) "[HseedM HseedSI]".
  iPoseProof (Hic Hcnd with "[HseedSI]") as "Hic"; first done.
  iMod (initialization_elim with "HseedM Hic") as "[HP Hres]".
  rewrite laterN_plus. iNext.
  iDestruct "HP" as "[Hsi [Hinit Hic']]".
  iDestruct (mwp_adequacy_basic with "[$Hsi $Hic']") as "Hic'".
  iSpecialize ("Hic'" $! rd).
  iApply initialization_mwpCM_soundness; iFrame.
  iApply mwpC_modality_mono; last done; eauto.
  by iIntros (x) "[_ ?]".
Qed.
