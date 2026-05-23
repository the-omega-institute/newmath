import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_regseqrat_streamname_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory observationA ∧
            UnaryHistory observationB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
              UnaryHistory realSeal ∧ Cont observationA observationB product ∧
                Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet classifierRoutesRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRealSeal
  exact
    ⟨windowAUnary, windowBUnary, observationAUnary, observationBUnary, productUnary,
      classifierUnary, realSealUnary, productRoute, classifierRoute, classifierRoutesRealSeal,
      namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
