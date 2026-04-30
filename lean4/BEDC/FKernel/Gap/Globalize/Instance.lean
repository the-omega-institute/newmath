import BEDC.FKernel.Gap.Globalize

namespace BEDC.FKernel.Gap

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

def InternalizedConcreteGlobalizeInstance [AskSetup] [PackageSetup] [DomainSetup]
    (bundle : ProbeBundle ProbeName) (D : Domain) :
    (BHist → Pkg → Prop) × (Pkg → Pkg → Prop) × (Pkg → BHist → Prop) :=
  signature_globalization_instance bundle D

end BEDC.FKernel.Gap
