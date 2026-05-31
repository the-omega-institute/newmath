import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_window_budget_composition_surface [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetRequest budgetWindow budgetDyadic
      budgetRegseq budgetReplay budgetPkgName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      UnaryHistory budgetRequest ->
        UnaryHistory budgetWindow ->
          UnaryHistory budgetRegseq ->
            Cont budgetRequest budgetWindow budgetDyadic ->
              Cont budgetDyadic budgetRegseq budgetReplay ->
                PkgSig bundle budgetPkgName pkg ->
                  UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory radiusA ∧
                    UnaryHistory radiusB ∧ UnaryHistory observationA ∧
                      UnaryHistory observationB ∧ UnaryHistory product ∧
                        UnaryHistory classifier ∧ UnaryHistory budgetDyadic ∧
                          UnaryHistory budgetReplay ∧ Cont observationA observationB product ∧
                            Cont product ledger classifier ∧
                              Cont budgetRequest budgetWindow budgetDyadic ∧
                                Cont budgetDyadic budgetRegseq budgetReplay ∧
                                  PkgSig bundle name pkg ∧
                                    PkgSig bundle budgetPkgName pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist Cont UnaryHistory ProbeBundle Pkg
  intro packet budgetRequestUnary budgetWindowUnary budgetRegseqUnary requestWindowDyadic
    dyadicRegseqReplay budgetPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetDyadicUnary : UnaryHistory budgetDyadic :=
    unary_cont_closed budgetRequestUnary budgetWindowUnary requestWindowDyadic
  have budgetReplayUnary : UnaryHistory budgetReplay :=
    unary_cont_closed budgetDyadicUnary budgetRegseqUnary dyadicRegseqReplay
  exact
    ⟨windowAUnary, windowBUnary, radiusAUnary, radiusBUnary, observationAUnary,
      observationBUnary, productUnary, classifierUnary, budgetDyadicUnary,
      budgetReplayUnary, productRoute, classifierRoute, requestWindowDyadic,
      dyadicRegseqReplay, namePkg, budgetPkg⟩

end BEDC.Derived.CauchyProductUp
