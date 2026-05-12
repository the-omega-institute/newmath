import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StoppingTimeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StoppingTimeSourcePacket [AskSetup] [PackageSetup]
    (prob process filtration horizon witness eventRead dependencyRead provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prob ∧ UnaryHistory process ∧ UnaryHistory filtration ∧
    UnaryHistory horizon ∧ UnaryHistory witness ∧ Cont process filtration dependencyRead ∧
      Cont dependencyRead witness eventRead ∧ Cont eventRead horizon provenance ∧
        PkgSig bundle provenance pkg

theorem StoppingTimeSourcePacket_filtration_prefix_stability [AskSetup] [PackageSetup]
    {prob process filtration horizon witness eventRead prefixEvent dependencyRead provenance
      prefixRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoppingTimeSourcePacket prob process filtration horizon witness eventRead dependencyRead
        provenance bundle pkg ->
      UnaryHistory prefixEvent ->
        Cont filtration prefixEvent prefixRoute ->
          Cont prefixRoute witness eventRead ->
            PkgSig bundle provenance pkg ->
              UnaryHistory prob ∧ UnaryHistory process ∧ UnaryHistory filtration ∧
                UnaryHistory witness ∧ UnaryHistory prefixEvent ∧ UnaryHistory prefixRoute ∧
                  UnaryHistory eventRead ∧ Cont filtration prefixEvent prefixRoute ∧
                    Cont prefixRoute witness eventRead ∧ PkgSig bundle provenance pkg := by
  intro packet prefixUnary prefixRow eventReadRow provenanceSig
  obtain ⟨probUnary, processUnary, filtrationUnary, _horizonUnary, witnessUnary,
    _dependencyRow, _eventReadOriginal, _provenanceRow, _pkgOriginal⟩ := packet
  have prefixRouteUnary : UnaryHistory prefixRoute :=
    unary_cont_closed filtrationUnary prefixUnary prefixRow
  have eventReadUnary : UnaryHistory eventRead :=
    unary_cont_closed prefixRouteUnary witnessUnary eventReadRow
  exact
    ⟨probUnary, processUnary, filtrationUnary, witnessUnary, prefixUnary,
      prefixRouteUnary, eventReadUnary, prefixRow, eventReadRow, provenanceSig⟩

end BEDC.Derived.StoppingTimeUp
