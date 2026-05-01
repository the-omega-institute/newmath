import BEDC.FKernel.Sig.Totality
import BEDC.FKernel.Sig.Determinacy

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem bundle_local_sameSig_of_hsame [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist → Prop} {h k : BHist} :
    BundleAskPolicy bundle D → D h → D k → hsame h k → SameSig bundle h k := by
  intro policy dh dk hhk
  cases sig_total_from_bundle_policy (bundle := bundle) (D := D) (h := h) policy dh with
  | intro s hs =>
      cases sig_total_from_bundle_policy (bundle := bundle) (D := D) (h := k) policy dk with
      | intro t ht =>
          exact Exists.intro s
            (Exists.intro t
              (And.intro hs
                (And.intro ht
                  (sig_respects_history_from_bundle_policy
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

theorem bundle_local_signature_sameness_equivalence [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist -> Prop} :
    BundleAskPolicy bundle D ->
      (forall {h : BHist}, D h -> SameSig bundle h h) /\
        (forall {h k : BHist}, SameSig bundle h k -> SameSig bundle k h) /\
        (forall {h k l : BHist}, D k -> SameSig bundle h k -> SameSig bundle k l ->
          SameSig bundle h l) := by
  intro policy
  constructor
  · intro h dh
    cases sig_total_from_bundle_policy (bundle := bundle) (D := D) (h := h) policy dh with
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
                                        sig_deterministic_from_bundle_policy
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
