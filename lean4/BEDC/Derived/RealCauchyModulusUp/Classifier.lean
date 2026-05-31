import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def RealCauchyModulusClassifier [AskSetup] [PackageSetup]
    (M S D Q E H C P N M' S' D' Q' E' H' C' P' N' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  RealCauchyModulusCarrier M S D Q E H C P N bundle pkg ∧
    RealCauchyModulusCarrier M' S' D' Q' E' H' C' P' N' bundle pkg ∧
      hsame M M' ∧ hsame S S' ∧ hsame D D' ∧ hsame Q Q' ∧ hsame E E' ∧
        hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N' ∧
          Cont M S D ∧ Cont D Q E

end BEDC.Derived.RealCauchyModulusUp
