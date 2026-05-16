import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_selector_seal_handoff_lock [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name selectorSeal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont sealRow transports selectorSeal ->
        PkgSig bundle selectorSeal pkg ->
          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
            UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
              UnaryHistory transports ∧ UnaryHistory selectorSeal ∧
                Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                  Cont tail sealRow transports ∧ Cont sealRow transports selectorSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle selectorSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sealTransportSelector selectorPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have selectorUnary : UnaryHistory selectorSeal :=
    unary_cont_closed sealRowUnary transportsUnary sealTransportSelector
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      transportsUnary, selectorUnary, indexWindowsModulus, modulusToleranceTail,
      tailSealRowTransports, sealTransportSelector, namePkg, selectorPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
