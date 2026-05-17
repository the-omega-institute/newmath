import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_exit_route_consumer_coverage [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name diagonalRead
      tailRead realRead budgetRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows diagonalRead ->
        Cont diagonalRead tail tailRead ->
          Cont tail sealRow realRead ->
            Cont tailRead realRead budgetRead ->
              Cont budgetRead name consumerRead ->
                PkgSig bundle budgetRead pkg ->
                  PkgSig bundle consumerRead pkg ->
                    UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory tail ∧
                      UnaryHistory diagonalRead ∧ UnaryHistory tailRead ∧
                        UnaryHistory realRead ∧ UnaryHistory budgetRead ∧
                          UnaryHistory consumerRead ∧ Cont index windows diagonalRead ∧
                            Cont diagonalRead tail tailRead ∧ Cont tail sealRow realRead ∧
                              Cont tailRead realRead budgetRead ∧
                                Cont budgetRead name consumerRead ∧ PkgSig bundle name pkg ∧
                                  PkgSig bundle budgetRead pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexWindowsDiagonal diagonalTailRead tailSealReal tailReadRealBudget
    budgetNameConsumer budgetPkg consumerPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsDiagonal
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed diagonalUnary tailUnary diagonalTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailReadUnary realReadUnary tailReadRealBudget
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed budgetUnary nameUnary budgetNameConsumer
  exact
    ⟨indexUnary, windowsUnary, tailUnary, diagonalUnary, tailReadUnary, realReadUnary,
      budgetUnary, consumerUnary, indexWindowsDiagonal, diagonalTailRead, tailSealReal,
      tailReadRealBudget, budgetNameConsumer, namePkg, budgetPkg, consumerPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
