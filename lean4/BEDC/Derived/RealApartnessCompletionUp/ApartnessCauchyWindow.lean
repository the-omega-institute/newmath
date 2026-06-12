import BEDC.Derived.RealApartnessCompletionUp

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def RealApartnessCompletionApartnessCauchyWindow [AskSetup] [PackageSetup]
    (apartness hausdorff completion stream regular dyadic sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig
  RealApartnessCompletionCarrier apartness hausdorff completion stream regular dyadic sealRow
    transport replay provenance localName bundle pkg ∧
    Cont apartness hausdorff completion ∧ Cont completion stream regular ∧
      Cont regular dyadic sealRow ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle localName pkg

end BEDC.Derived.RealApartnessCompletionUp
