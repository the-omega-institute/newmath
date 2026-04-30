import BEDC.FKernel.Sig.SameSig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem proof_sprint_signature_sameness_equivalence_under_policy [AskSetup]
    {bundle : ProbeBundle ProbeName} {D : BHist → Prop} (policy : AskPolicy D) :
    (∀ {h : BHist}, D h → SameSig bundle h h) ∧
      (∀ {h k : BHist}, SameSig bundle h k → SameSig bundle k h) ∧
      (∀ {h k l : BHist},
        D k → SameSig bundle h k → SameSig bundle k l → SameSig bundle h l) := by
  constructor
  · intro h dh
    cases sig_total_from_policy (bundle := bundle) (D := D) (h := h) policy dh with
    | intro s hsig =>
        exact Exists.intro s
          (Exists.intro s
            (And.intro hsig
              (And.intro hsig (hsame_refl s))))
  · constructor
    · intro h k hsameSig
      cases hsameSig with
      | intro s hsameSigTail =>
          cases hsameSigTail with
          | intro t hsameSigData =>
              cases hsameSigData with
              | intro hs hsameSigRest =>
                  cases hsameSigRest with
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
                                      have htu : hsame t u :=
                                        sig_deterministic
                                          (bundle := bundle)
                                          (D := D)
                                          (h := k)
                                          (s := t)
                                          (t := u)
                                          policy
                                          dk
                                          htk
                                          huk
                                      exact Exists.intro s
                                        (Exists.intro v
                                          (And.intro hs
                                            (And.intro hvl
                                              (hsame_trans hst
                                                (hsame_trans htu huv)))))

end BEDC.FKernel.Sig
