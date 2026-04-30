import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sig_cons_result_hsame_from_policy [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName}
    {D : BHist -> Prop} {h r r' : BHist} (policy : AskPolicy D) :
    D h -> SigRel (ProbeBundle.Bcons pi tail) h r ->
      SigRel (ProbeBundle.Bcons pi tail) h r' -> hsame r r' := by
  intro dh left right
  cases left with
  | cons _ _ _ s _ m _ leftAsk leftTail leftExt =>
      cases right with
      | cons _ _ _ t _ n _ rightAsk rightTail rightExt =>
          have tailSame : hsame s t :=
            sig_deterministic
              (bundle := tail)
              (D := D)
              (h := h)
              (s := s)
              (t := t)
              policy
              dh
              leftTail
              rightTail
          have markSame : msame m n := policy.deterministic leftAsk rightAsk
          exact ext_respects_sameness tailSame markSame leftExt rightExt

end BEDC.FKernel.Sig
