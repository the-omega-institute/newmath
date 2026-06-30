import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCoreSiblingRoute [AskSetup] [PackageSetup]
    {hub tailEnvelope dyadicLedger streamWindow regseqReadback realSeal transport
      replay provenance localName routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory hub ->
      UnaryHistory tailEnvelope ->
        UnaryHistory dyadicLedger ->
          UnaryHistory regseqReadback ->
            UnaryHistory transport ->
              Cont hub tailEnvelope routeRead ->
                Cont tailEnvelope dyadicLedger streamWindow ->
                  Cont streamWindow regseqReadback realSeal ->
                    Cont realSeal transport replay ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle localName pkg ->
                          UnaryHistory routeRead ∧ UnaryHistory streamWindow ∧
                            UnaryHistory realSeal ∧ UnaryHistory replay ∧
                              Cont hub tailEnvelope routeRead ∧
                                Cont tailEnvelope dyadicLedger streamWindow ∧
                                  Cont streamWindow regseqReadback realSeal ∧
                                    Cont realSeal transport replay ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro hubUnary tailEnvelopeUnary dyadicLedgerUnary regseqReadbackUnary transportUnary
    hubTailRoute tailDyadicRoute streamRegseqRoute realTransportRoute provenancePkg
    localNamePkg
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed hubUnary tailEnvelopeUnary hubTailRoute
  have streamWindowUnary : UnaryHistory streamWindow :=
    unary_cont_closed tailEnvelopeUnary dyadicLedgerUnary tailDyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed streamWindowUnary regseqReadbackUnary streamRegseqRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed realSealUnary transportUnary realTransportRoute
  exact
    ⟨routeReadUnary, streamWindowUnary, realSealUnary, replayUnary, hubTailRoute,
      tailDyadicRoute, streamRegseqRoute, realTransportRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.DyadicUp
