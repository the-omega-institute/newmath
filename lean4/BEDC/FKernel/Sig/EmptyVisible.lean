import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask

theorem sig_empty_visible_absurd [BEDC.FKernel.Ask.AskSetup] {h p : BHist} :
    (SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h (BHist.e0 p) -> False) ∧
      (SigRel (ProbeBundle.Bnil : ProbeBundle ProbeName) h (BHist.e1 p) -> False) := by
  constructor
  · intro generated
    exact BEDC.FKernel.Hist.not_hsame_e0_empty (sig_empty_inversion generated)
  · intro generated
    exact BEDC.FKernel.Hist.not_hsame_e1_empty (sig_empty_inversion generated)

end BEDC.FKernel.Sig
