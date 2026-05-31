import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_window_seal_compatibility [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier ledger realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
            UnaryHistory classifier ∧ UnaryHistory realSeal ∧ Cont windowA windowB transport ∧
              Cont observationA observationB product ∧ Cont product ledger classifier ∧
                Cont classifier ledger realSeal ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierLedgerRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary ledgerUnary classifierLedgerRealSeal
  exact
    ⟨windowAUnary, windowBUnary, productUnary, classifierUnary, realSealUnary,
      windowTransport, productRoute, classifierRoute, classifierLedgerRealSeal, namePkg,
      realSealPkg⟩

end BEDC.Derived.CauchyProductUp
