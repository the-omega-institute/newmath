import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_source_window_seal_consumer_exactness [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal realSeal consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        Cont regseqSeal ledger realSeal ->
          Cont realSeal routes consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory radiusA ∧ UnaryHistory radiusB ∧
                  UnaryHistory observationA ∧ UnaryHistory observationB ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧
                      UnaryHistory regseqSeal ∧ UnaryHistory realSeal ∧
                        UnaryHistory consumerRead ∧ Cont windowA windowB transport ∧
                          Cont observationA observationB product ∧
                            Cont product ledger classifier ∧
                              Cont classifier routes regseqSeal ∧
                                Cont regseqSeal ledger realSeal ∧
                                  Cont realSeal routes consumerRead ∧ PkgSig bundle name pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierSeal sealReal realConsumer consumerPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierSeal
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqSealUnary ledgerUnary sealReal
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed realSealUnary routesUnary realConsumer
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, radiusAUnary, radiusBUnary,
      observationAUnary, observationBUnary, productUnary, classifierUnary, regseqSealUnary,
      realSealUnary, consumerReadUnary, windowTransport, productRoute, classifierRoute,
      classifierSeal, sealReal, realConsumer, namePkg, consumerPkg⟩

end BEDC.Derived.CauchyProductUp
