import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_real_route_certificate [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow sealRead ->
          Cont tailRead sealRead terminalRead ->
            PkgSig bundle tailRead pkg ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle terminalRead pkg ->
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory terminalRead ∧ Cont index windows modulus ∧
                          Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                            Cont tail sealRow sealRead ∧ Cont tailRead sealRead terminalRead ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                                PkgSig bundle sealRead pkg ∧
                                  PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead tailSealTerminal tailReadPkg sealReadPkg
    terminalReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailSealTerminal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      tailReadUnary, sealReadUnary, terminalReadUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRead, tailSealRead, tailSealTerminal, namePkg, tailReadPkg, sealReadPkg,
      terminalReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
