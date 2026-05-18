import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def UniformCauchyCriterionCarrier [AskSetup] [PackageSetup]
    (index windows modulus tolerance tail sealRow transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
      provenance name bundle pkg ∧
    hsame transports (append tail routes)

end BEDC.Derived.UniformCauchyCriterionUp
