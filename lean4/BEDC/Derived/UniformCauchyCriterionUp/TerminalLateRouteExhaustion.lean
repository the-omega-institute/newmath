import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_late_route_exhaustion [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name realRead
      regseqRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow realRead ->
        Cont tail realRead regseqRead ->
          Cont regseqRead sealRow terminalRead ->
            PkgSig bundle realRead pkg ->
              PkgSig bundle terminalRead pkg ->
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                  UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                    UnaryHistory realRead ∧ UnaryHistory regseqRead ∧
                      UnaryHistory terminalRead ∧ Cont index windows modulus ∧
                        Cont modulus tolerance tail ∧ Cont tail sealRow realRead ∧
                          Cont tail realRead regseqRead ∧
                            Cont regseqRead sealRow terminalRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle realRead pkg ∧
                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealReal tailRealRegseq regseqSealTerminal realPkg terminalPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed tailUnary realUnary tailRealRegseq
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed regseqUnary sealRowUnary regseqSealTerminal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary, realUnary,
      regseqUnary, terminalUnary, indexWindowsModulus, modulusToleranceTail, tailSealReal,
      tailRealRegseq, regseqSealTerminal, namePkg, realPkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
