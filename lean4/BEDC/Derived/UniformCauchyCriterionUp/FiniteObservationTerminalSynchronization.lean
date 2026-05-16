import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_observation_terminal_synchronization
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name
      selectorWindow selectorTolerance selectorReadback selectorSeal terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      hsame windows selectorWindow →
        hsame tolerance selectorTolerance →
          hsame tail selectorReadback →
            hsame sealRow selectorSeal →
              Cont selectorReadback selectorSeal terminalRead →
                PkgSig bundle terminalRead pkg →
                  UnaryHistory selectorWindow ∧ UnaryHistory selectorTolerance ∧
                    UnaryHistory selectorReadback ∧ UnaryHistory selectorSeal ∧
                      UnaryHistory terminalRead ∧
                        Cont selectorReadback selectorSeal terminalRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro packet sameWindow sameTolerance sameTail sameSeal terminalCont terminalPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have selectorWindowUnary : UnaryHistory selectorWindow :=
    unary_transport windowsUnary sameWindow
  have selectorToleranceUnary : UnaryHistory selectorTolerance :=
    unary_transport toleranceUnary sameTolerance
  have selectorReadbackUnary : UnaryHistory selectorReadback :=
    unary_transport tailUnary sameTail
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_transport sealRowUnary sameSeal
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed selectorReadbackUnary selectorSealUnary terminalCont
  exact
    ⟨selectorWindowUnary, selectorToleranceUnary, selectorReadbackUnary, selectorSealUnary,
      terminalUnary, terminalCont, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
