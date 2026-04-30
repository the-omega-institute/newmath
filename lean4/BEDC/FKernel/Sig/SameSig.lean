import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sameSig_left_witness [AskSetup] {bundle : ProbeBundle ProbeName} {h k : BHist} :
    SameSig bundle h k -> exists s : BHist, SigRel bundle h s := by
  intro hsameSig
  cases hsameSig with
  | intro s rest =>
      cases rest with
      | intro _ data =>
          exact Exists.intro s data.left

theorem sameSig_trans_with_middle_witness [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} (policy : AskPolicy D) {h k l : BHist} :
    D k -> SameSig bundle h k -> SameSig bundle k l ->
      exists s : BHist, exists v : BHist,
        SigRel bundle h s /\ SigRel bundle l v /\ hsame s v := by
  intro dk hhk hkl
  have composed : SameSig bundle h l :=
    sameSig_trans
      (bundle := bundle)
      (D := D)
      (h := h)
      (k := k)
      (l := l)
      policy
      dk
      hhk
      hkl
  cases composed with
  | intro s tail =>
      cases tail with
      | intro v data =>
          cases data with
          | intro hs rest =>
              cases rest with
              | intro hv hsv =>
                  exact Exists.intro s
                    (Exists.intro v
                      (And.intro hs
                        (And.intro hv hsv)))

theorem sameSig_middle_witnesses_hsame_under_policy [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} (policy : AskPolicy D) {h k l : BHist} :
    D k -> SameSig bundle h k -> SameSig bundle k l ->
      Exists (fun t : BHist => Exists (fun u : BHist =>
        And (SigRel bundle k t) (And (SigRel bundle k u) (hsame t u)))) := by
  intro dk hhk hkl
  cases hhk with
  | intro _ hhkTail =>
      cases hhkTail with
      | intro t hhkData =>
          cases hhkData with
          | intro _ hhkRest =>
              cases hhkRest with
              | intro htk _ =>
                  cases hkl with
                  | intro u hklTail =>
                      cases hklTail with
                      | intro _ hklData =>
                          cases hklData with
                          | intro huk _ =>
                              exact Exists.intro t
                                (Exists.intro u
                                  (And.intro htk
                                    (And.intro huk
                                      (sig_deterministic
                                        (bundle := bundle)
                                        (D := D)
                                        (h := k)
                                        (s := t)
                                        (t := u)
                                        policy
                                        dk
                                        htk
                                        huk))))

theorem signature_sameness_equivalence_total_determinacy [AskSetup]
    {bundle : ProbeBundle ProbeName} {D : BHist -> Prop}
    (total : SigTotalOn bundle D)
    (det : forall {h s t : BHist}, D h -> SigRel bundle h s -> SigRel bundle h t ->
      hsame s t) :
    (forall {h : BHist}, D h -> SameSig bundle h h) ∧
      (forall {h k : BHist}, SameSig bundle h k -> SameSig bundle k h) ∧
      (forall {h k l : BHist},
        D k -> SameSig bundle h k -> SameSig bundle k l -> SameSig bundle h l) := by
  constructor
  · intro h hd
    cases total h hd with
    | intro s hsig =>
        exact Exists.intro s
          (Exists.intro s
            (And.intro hsig
              (And.intro hsig (hsame_refl s))))
  · constructor
    · intro h k hhk
      cases hhk with
      | intro s hhkTail =>
          cases hhkTail with
          | intro t hhkData =>
              cases hhkData with
              | intro hs hhkRest =>
                  cases hhkRest with
                  | intro ht hst =>
                      exact Exists.intro t
                        (Exists.intro s
                          (And.intro ht
                            (And.intro hs (hsame_symm hst))))
    · intro h k l dk hhk hkl
      cases hhk with
      | intro s hhkTail =>
          cases hhkTail with
          | intro t hhkData =>
              cases hhkData with
              | intro hs hhkRest =>
                  cases hhkRest with
                  | intro htk hst =>
                      cases hkl with
                      | intro u hklTail =>
                          cases hklTail with
                          | intro v hklData =>
                              cases hklData with
                              | intro huk hklRest =>
                                  cases hklRest with
                                  | intro hvl huv =>
                                      have htu : hsame t u := det dk htk huk
                                      exact Exists.intro s
                                        (Exists.intro v
                                          (And.intro hs
                                            (And.intro hvl
                                              (hsame_trans hst
                                                (hsame_trans htu huv)))))

end BEDC.FKernel.Sig
