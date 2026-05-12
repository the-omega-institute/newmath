import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCauchyCriterionPacket [AskSetup] [PackageSetup]
    (index windows modulus tolerance tail sealRow transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont index windows modulus ∧ Cont modulus tolerance tail ∧
          Cont tail sealRow transports ∧ Cont transports routes provenance ∧
            PkgSig bundle name pkg

theorem UniformCauchyCriterionPacket_namecert_obligations [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
              UnaryHistory consumer ∧ Cont index windows modulus ∧
                Cont modulus tolerance tail ∧ Cont index tail consumer ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet indexTailConsumer consumerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed indexUnary tailUnary indexTailConsumer
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      consumerUnary, indexWindowsModulus, modulusToleranceTail, indexTailConsumer, namePkg,
      consumerPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
