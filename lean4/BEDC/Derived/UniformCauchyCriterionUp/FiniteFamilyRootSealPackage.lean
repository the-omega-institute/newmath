import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_root_seal_package
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name rootRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail rootRead ->
        Cont tail sealRow sealRead ->
          PkgSig bundle rootRead pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                  UnaryHistory rootRead ∧ UnaryHistory sealRead ∧
                    Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                      Cont index tail rootRead ∧ Cont tail sealRow sealRead ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle rootRead pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet rootRoute sealRoute rootPkg sealPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed indexUnary tailUnary rootRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary sealRoute
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      rootUnary, sealUnary, indexWindowsModulus, modulusToleranceTail, rootRoute, sealRoute,
      namePkg, rootPkg, sealPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
