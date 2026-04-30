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

end BEDC.FKernel.Sig
