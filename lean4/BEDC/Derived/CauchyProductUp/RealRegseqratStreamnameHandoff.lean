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
      classifier transport routes ledger name streamRead regseqSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes regseqSeal ->
          Cont regseqSeal ledger realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory transport ∧ UnaryHistory streamRead ∧
                  UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧
                    UnaryHistory realSeal ∧ Cont windowA windowB transport ∧
                      Cont transport routes streamRead ∧
                        Cont observationA observationB product ∧
                          Cont product ledger classifier ∧
                            Cont classifier routes regseqSeal ∧
                              Cont regseqSeal ledger realSeal ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesStreamRead classifierRoutesRegseq regseqRealSeal realSealPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamRead
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRegseq
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqRealSeal
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, transportUnary,
      streamReadUnary, productUnary, classifierUnary, regseqSealUnary, realSealUnary,
      windowTransport, transportRoutesStreamRead, productRoute, classifierRoute,
      classifierRoutesRegseq, regseqRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
