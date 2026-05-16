import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_root_seal_pullback_nonescape
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name rootRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail rootRead ->
        Cont rootRead sealRow completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
              UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                UnaryHistory rootRead ∧ UnaryHistory completionRead ∧
                  Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                    Cont index tail rootRead ∧ Cont rootRead sealRow completionRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet rootRoute completionRoute completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed indexUnary tailUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealRowUnary completionRoute
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      rootUnary, completionUnary, indexWindowsModulus, modulusToleranceTail, rootRoute,
      completionRoute, namePkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
