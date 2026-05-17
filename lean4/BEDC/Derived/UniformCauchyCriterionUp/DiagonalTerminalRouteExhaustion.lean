import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_terminal_route_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead realRead budgetRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
        Cont diagonalRead tail tailRead ->
          Cont tail sealRow realRead ->
            Cont tailRead realRead budgetRead ->
              Cont budgetRead routes terminalRead ->
                PkgSig bundle budgetRead pkg ->
                  PkgSig bundle terminalRead pkg ->
                    UnaryHistory diagonalRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory realRead ∧ UnaryHistory budgetRead ∧
                        UnaryHistory terminalRead ∧ Cont index windows diagonalRead ∧
                          Cont diagonalRead tail tailRead ∧ Cont tail sealRow realRead ∧
                            Cont tailRead realRead budgetRead ∧
                              Cont budgetRead routes terminalRead ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsDiagonal diagonalTail tailSealReal tailReadRealBudget
    budgetRoutesTerminal _budgetPkg terminalPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsDiagonal
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed diagonalUnary tailUnary diagonalTail
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailReadUnary realReadUnary tailReadRealBudget
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetReadUnary routesUnary budgetRoutesTerminal
  exact
    ⟨diagonalUnary, tailReadUnary, realReadUnary, budgetReadUnary, terminalReadUnary,
      indexWindowsDiagonal, diagonalTail, tailSealReal, tailReadRealBudget,
      budgetRoutesTerminal, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
