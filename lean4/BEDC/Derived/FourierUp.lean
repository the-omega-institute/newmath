import BEDC.FKernel.Sig

namespace BEDC.Derived.FourierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Sig

theorem FourierFiniteObservation_carrier_obligation [AskSetup]
    {bundle : ProbeBundle ProbeName} {source observed : BHist} :
    SigRel bundle source observed ->
      (bundle = ProbeBundle.Bnil ∧ hsame observed BHist.Empty) ∨
        ∃ pi : ProbeName, ∃ tail : ProbeBundle ProbeName, ∃ obsPrefix : BHist,
          ∃ mark : BMark, ∃ evidence : Evidence,
            bundle = ProbeBundle.Bcons pi tail ∧
              Ask pi source mark evidence ∧
                SigRel tail source obsPrefix ∧ Ext obsPrefix mark observed := by
  intro observedRow
  cases observedRow with
  | empty h =>
      exact Or.inl (And.intro rfl (hsame_refl BHist.Empty))
  | cons pi tail h obsPrefix r mark evidence askRow tailRow extRow =>
      exact Or.inr
        (Exists.intro pi
          (Exists.intro tail
            (Exists.intro obsPrefix
              (Exists.intro mark
                (Exists.intro evidence
                  (And.intro rfl
                    (And.intro askRow (And.intro tailRow extRow))))))))

end BEDC.Derived.FourierUp
