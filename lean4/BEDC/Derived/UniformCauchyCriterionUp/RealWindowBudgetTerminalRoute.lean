import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_realwindowbudget_terminal_route [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name realWindow sealRead
      terminalRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tail realWindow ->
        Cont realWindow sealRow sealRead ->
          Cont sealRead provenance terminalRoute ->
            PkgSig bundle realWindow pkg ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle terminalRoute pkg ->
                  UnaryHistory realWindow ∧ UnaryHistory sealRead ∧
                    UnaryHistory terminalRoute ∧ Cont windows tail realWindow ∧
                      Cont realWindow sealRow sealRead ∧ Cont sealRead provenance terminalRoute ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle realWindow pkg ∧
                          PkgSig bundle sealRead pkg ∧ PkgSig bundle terminalRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet windowsTailReal realSealRead sealProvenanceTerminal realPkg sealPkg terminalPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have realUnary : UnaryHistory realWindow :=
    unary_cont_closed windowsUnary tailUnary windowsTailReal
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed realUnary sealRowUnary realSealRead
  have terminalUnary : UnaryHistory terminalRoute :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceTerminal
  exact
    ⟨realUnary, sealUnary, terminalUnary, windowsTailReal, realSealRead,
      sealProvenanceTerminal, namePkg, realPkg, sealPkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
