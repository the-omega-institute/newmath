import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sameSig_trans_chain_witnesses_under_policy [AskSetup]
    {bundle : ProbeBundle ProbeName} {D : BHist -> Prop} (policy : AskPolicy D)
    {h k l s t u v : BHist} :
    D k -> SigRel bundle h s -> SigRel bundle k t -> hsame s t ->
      SigRel bundle k u -> SigRel bundle l v -> hsame u v ->
      exists _ : hsame t u, SameSig bundle h l := by
  intro hk hs ht hst hu hv huv
  have htu : hsame t u :=
    sig_deterministic
      (bundle := bundle)
      (D := D)
      (h := k)
      (s := t)
      (t := u)
      policy
      hk
      ht
      hu
  exact Exists.intro htu
    (Exists.intro s
      (Exists.intro v
        (And.intro hs
          (And.intro hv
            (hsame_trans hst (hsame_trans htu huv))))))

theorem sig_total_pair_from_policy [AskSetup] {bundle : ProbeBundle ProbeName} {D : BHist -> Prop}
    (policy : AskPolicy D) {h k : BHist} :
    D h -> D k ->
      exists s : BHist, exists t : BHist, SigRel bundle h s ∧ SigRel bundle k t := by
  intro dh dk
  cases sig_total_from_policy (bundle := bundle) (D := D) (h := h) policy dh with
  | intro s hs =>
      cases sig_total_from_policy (bundle := bundle) (D := D) (h := k) policy dk with
      | intro t ht =>
          exact ⟨s, t, hs, ht⟩

theorem signature_totality_witness_chain [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} (policy : AskPolicy D) {h k : BHist} :
    D h -> hsame h k -> D k ->
      exists s : BHist, exists t : BHist,
        SigRel bundle h s /\ SigRel bundle k t /\ hsame s t := by
  intro dh hhk dk
  cases sig_total_from_policy (bundle := bundle) (D := D) (h := h) policy dh with
  | intro s hs =>
      cases sig_total_from_policy (bundle := bundle) (D := D) (h := k) policy dk with
      | intro t ht =>
          exact Exists.intro s
            (Exists.intro t
              (And.intro hs
                (And.intro ht
                  (sig_respects_history
                    (bundle := bundle)
                    (D := D)
                    (h := h)
                    (k := k)
                    (s := s)
                    (t := t)
                    policy
                    hhk
                    hs
                    ht))))

theorem sameSig_three_step_witness_chain_under_policy [AskSetup]
    {bundle : ProbeBundle ProbeName} {D : BHist -> Prop} (policy : AskPolicy D)
    {h k l m : BHist} :
    D k -> D l -> SameSig bundle h k -> SameSig bundle k l -> SameSig bundle l m ->
      exists s : BHist, exists v : BHist,
        SigRel bundle h s /\ SigRel bundle m v /\ hsame s v := by
  intro dk dl hhk hkl hlm
  have hhl : SameSig bundle h l :=
    sameSig_trans (bundle := bundle) (D := D) (h := h) (k := k) (l := l)
      policy dk hhk hkl
  have hhm : SameSig bundle h m :=
    sameSig_trans (bundle := bundle) (D := D) (h := h) (k := l) (l := m)
      policy dl hhl hlm
  exact hhm

theorem sameSig_four_step_witness_chain_under_policy [AskSetup]
    {bundle : ProbeBundle ProbeName} {D : BHist -> Prop} (policy : AskPolicy D)
    {h k l m n : BHist} :
    D k -> D l -> D m -> SameSig bundle h k -> SameSig bundle k l ->
      SameSig bundle l m -> SameSig bundle m n ->
        exists s : BHist, exists v : BHist,
          SigRel bundle h s /\ SigRel bundle n v /\ hsame s v := by
  intro dk dl dm hhk hkl hlm hmn
  have hhl : SameSig bundle h l :=
    sameSig_trans (bundle := bundle) (D := D) (h := h) (k := k) (l := l)
      policy dk hhk hkl
  have hhm : SameSig bundle h m :=
    sameSig_trans (bundle := bundle) (D := D) (h := h) (k := l) (l := m)
      policy dl hhl hlm
  have hhn : SameSig bundle h n :=
    sameSig_trans (bundle := bundle) (D := D) (h := h) (k := m) (l := n)
      policy dm hhm hmn
  exact hhn

end BEDC.FKernel.Sig
