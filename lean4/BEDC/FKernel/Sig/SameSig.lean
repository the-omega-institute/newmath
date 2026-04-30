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

end BEDC.FKernel.Sig
