import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedCauchyIntegralUp [AskSetup] [PackageSetup]
    (regulated partition step windows readback realSeal transport replay provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regulated ∧ UnaryHistory partition ∧ UnaryHistory step ∧ UnaryHistory windows ∧
    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont regulated partition step ∧ Cont step windows readback ∧
          Cont readback realSeal replay ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

namespace RegulatedCauchyIntegralUp

theorem RegulatedCauchyIntegralCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {regulated partition step windows readback realSeal transport replay provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RegulatedCauchyIntegralUp regulated partition step windows readback realSeal
        transport replay provenance localName bundle pkg →
      UnaryHistory regulated ∧ UnaryHistory partition ∧ UnaryHistory step ∧
        UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
          Cont regulated partition step ∧ Cont step windows readback ∧
            Cont readback realSeal replay ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier
  obtain ⟨regulatedUnary, partitionUnary, stepUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    regulatedPartitionStep, stepWindowsReadback, readbackRealSealReplay, provenancePkg,
    localNamePkg⟩ := carrier
  exact
    ⟨regulatedUnary, partitionUnary, stepUnary, windowsUnary, readbackUnary, realSealUnary,
      regulatedPartitionStep, stepWindowsReadback, readbackRealSealReplay, provenancePkg,
      localNamePkg⟩

end RegulatedCauchyIntegralUp
end BEDC.Derived
