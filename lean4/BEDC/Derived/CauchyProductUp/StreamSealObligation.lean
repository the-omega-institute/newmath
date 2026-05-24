import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_stream_seal_obligation [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal realSeal streamSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        Cont regseqSeal ledger realSeal ->
          Cont transport realSeal streamSeal ->
            PkgSig bundle streamSeal pkg ->
              UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory radiusA ∧
                UnaryHistory radiusB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory regseqSeal ∧ UnaryHistory realSeal ∧
                    UnaryHistory streamSeal ∧ Cont windowA windowB transport ∧
                      Cont observationA observationB product ∧
                        Cont product ledger classifier ∧
                          Cont classifier routes regseqSeal ∧
                            Cont regseqSeal ledger realSeal ∧
                              Cont transport realSeal streamSeal ∧
                                PkgSig bundle name pkg ∧
                                  PkgSig bundle streamSeal pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRegseq regseqReal transportStream streamPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have regseqUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRegseq
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary ledgerUnary regseqReal
  have streamUnary : UnaryHistory streamSeal :=
    unary_cont_closed transportUnary realUnary transportStream
  exact
    ⟨windowAUnary, windowBUnary, radiusAUnary, radiusBUnary, productUnary,
      classifierUnary, regseqUnary, realUnary, streamUnary, windowTransport, productRoute,
      classifierRoute, classifierRegseq, regseqReal, transportStream, namePkg, streamPkg⟩

end BEDC.Derived.CauchyProductUp
