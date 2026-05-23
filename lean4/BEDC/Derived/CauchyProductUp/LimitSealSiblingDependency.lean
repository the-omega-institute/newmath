import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_limitseal_sibling_dependency [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal limitSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg →
      Cont classifier routes realSeal →
        Cont realSeal ledger limitSeal →
          PkgSig bundle limitSeal pkg →
            UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
              UnaryHistory limitSeal ∧ Cont product ledger classifier ∧
                Cont classifier routes realSeal ∧ Cont realSeal ledger limitSeal ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle limitSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet classifierRoutesRealSeal realSealLedgerLimit limitSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  have limitSealUnary : UnaryHistory limitSeal :=
    unary_cont_closed realSealUnary ledgerUnary realSealLedgerLimit
  exact
    ⟨productUnary, classifierUnary, realSealUnary, limitSealUnary, classifierRoute,
      classifierRoutesRealSeal, realSealLedgerLimit, namePkg, limitSealPkg⟩

end BEDC.Derived.CauchyProductUp
