import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_seal_classifier_route [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      tailRead sealRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead classifierRead ->
              PkgSig bundle classifierRead pkg ->
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory tail ∧
                  UnaryHistory windowRead ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory classifierRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index windows windowRead ∧
                        Cont windowRead tail tailRead ∧ Cont tail sealRow sealRead ∧
                          Cont tailRead sealRead classifierRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowRoute tailRoute sealRoute classifierRoute classifierPkg
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
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed tailReadUnary sealReadUnary classifierRoute
  exact
    ⟨indexUnary, windowsUnary, tailUnary, windowUnary, tailReadUnary, sealReadUnary,
      classifierUnary, indexWindowsModulus, modulusToleranceTail, windowRoute, tailRoute,
      sealRoute, classifierRoute, namePkg, classifierPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
