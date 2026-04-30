import BEDC.FKernel.Sig

namespace BEDC.FKernel.Sig

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem sigRel_generation_cases [AskSetup] {bundle : ProbeBundle ProbeName} {h r : BHist} :
    SigRel bundle h r →
      (bundle = (ProbeBundle.Bnil : ProbeBundle ProbeName) ∧ hsame r BHist.Empty) ∨
        ∃ pi : ProbeName, ∃ tail : ProbeBundle ProbeName, ∃ s : BHist, ∃ m : BMark,
          ∃ delta : Evidence,
            bundle = ProbeBundle.Bcons pi tail ∧ Ask pi h m delta ∧ SigRel tail h s ∧
              Ext s m r := by
  intro hsig
  cases hsig with
  | empty h =>
      exact Or.inl (And.intro rfl rfl)
  | cons pi tail h s r m delta hask htail hext =>
      exact
        Or.inr
          (Exists.intro pi
            (Exists.intro tail
              (Exists.intro s
                (Exists.intro m
                  (Exists.intro delta
                    (And.intro rfl
                      (And.intro hask
                        (And.intro htail hext))))))))

end BEDC.FKernel.Sig
