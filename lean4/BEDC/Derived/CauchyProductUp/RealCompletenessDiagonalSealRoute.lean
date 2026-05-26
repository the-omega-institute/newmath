import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_completeness_diagonal_seal_route [AskSetup]
    [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name diagonalSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        Cont realSeal ledger diagonalSeal ->
          PkgSig bundle diagonalSeal pkg ->
            UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
              UnaryHistory classifier ∧ UnaryHistory realSeal ∧ UnaryHistory diagonalSeal ∧
                Cont observationA observationB product ∧ Cont product ledger classifier ∧
                  Cont classifier routes realSeal ∧ Cont realSeal ledger diagonalSeal ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle diagonalSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet realSealRoute diagonalSealRoute diagonalSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary realSealRoute
  have diagonalSealUnary : UnaryHistory diagonalSeal :=
    unary_cont_closed realSealUnary ledgerUnary diagonalSealRoute
  exact
    ⟨windowAUnary, windowBUnary, productUnary, classifierUnary, realSealUnary,
      diagonalSealUnary, productRoute, classifierRoute, realSealRoute, diagonalSealRoute,
      namePkg, diagonalSealPkg⟩

end BEDC.Derived.CauchyProductUp
