import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_window_seal_exhaustion [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead tail tailRead ->
          Cont tail sealRow sealRead ->
            PkgSig bundle tailRead pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory tail ∧
                  UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory sealRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index windows windowRead ∧
                        Cont windowRead tail tailRead ∧ Cont tail sealRow sealRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowRoute tailRoute sealRoute tailReadPkg sealReadPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary windowRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary tailUnary tailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary sealRoute
  exact
    ⟨indexUnary, windowsUnary, tailUnary, windowUnary, tailReadUnary, sealReadUnary,
      indexWindowsModulus, modulusToleranceTail, windowRoute, tailRoute, sealRoute,
      namePkg, tailReadPkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
