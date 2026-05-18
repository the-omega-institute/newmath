import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PropextTransportBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PropextTransportBoundaryCarrier [AskSetup] [PackageSetup]
    (bidirectional direction replacement transport continuation provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bidirectional ∧
    UnaryHistory direction ∧
      UnaryHistory replacement ∧
        UnaryHistory transport ∧
          UnaryHistory continuation ∧
            UnaryHistory provenance ∧
              UnaryHistory localName ∧
                Cont bidirectional direction continuation ∧
                  Cont replacement transport provenance ∧
                    PkgSig bundle localName pkg

theorem PropextTransportBoundaryDirectionDeterminacy [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      forwardRead reverseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport
        continuation provenance localName bundle pkg →
      Cont bidirectional direction forwardRead →
        Cont replacement transport reverseRead →
          PkgSig bundle forwardRead pkg →
            PkgSig bundle reverseRead pkg →
              UnaryHistory bidirectional ∧
                UnaryHistory direction ∧
                  UnaryHistory replacement ∧
                    UnaryHistory transport ∧
                      UnaryHistory continuation ∧
                        UnaryHistory localName ∧
                          UnaryHistory forwardRead ∧
                            UnaryHistory reverseRead ∧
                              Cont bidirectional direction forwardRead ∧
                                Cont replacement transport reverseRead ∧
                                  PkgSig bundle localName pkg ∧
                                    PkgSig bundle forwardRead pkg ∧
                                      PkgSig bundle reverseRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier forwardCont reverseCont forwardPkg reversePkg
  rcases carrier with
    ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary,
      continuationUnary, _provenanceUnary, localNameUnary, _carrierForward,
      _carrierReverse, localNamePkg⟩
  have forwardUnary : UnaryHistory forwardRead :=
    unary_cont_closed bidirectionalUnary directionUnary forwardCont
  have reverseUnary : UnaryHistory reverseRead :=
    unary_cont_closed replacementUnary transportUnary reverseCont
  exact
    ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary, continuationUnary,
      localNameUnary, forwardUnary, reverseUnary, forwardCont, reverseCont, localNamePkg,
      forwardPkg, reversePkg⟩

theorem PropextTransportBoundaryNonEscapeReadback [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      contextRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport
        continuation provenance localName bundle pkg →
      Cont replacement transport contextRead →
        Cont bidirectional direction ledgerRead →
          PkgSig bundle localName pkg →
            UnaryHistory replacement ∧
              UnaryHistory transport ∧
                UnaryHistory provenance ∧
                  UnaryHistory contextRead ∧
                    UnaryHistory ledgerRead ∧
                      Cont replacement transport contextRead ∧
                        Cont bidirectional direction ledgerRead ∧
                          PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier contextCont ledgerCont localPkg
  rcases carrier with
    ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary,
      _continuationUnary, provenanceUnary, _localNameUnary, _carrierLedger,
      _carrierContext, _carrierPkg⟩
  have contextUnary : UnaryHistory contextRead :=
    unary_cont_closed replacementUnary transportUnary contextCont
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed bidirectionalUnary directionUnary ledgerCont
  exact
    ⟨replacementUnary, transportUnary, provenanceUnary, contextUnary, ledgerUnary,
      contextCont, ledgerCont, localPkg⟩

theorem PropextTransportBoundaryLedgerExactness [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      ledgerRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport
        continuation provenance localName bundle pkg →
      Cont transport continuation ledgerRead →
        Cont ledgerRead localName replayRead →
          PkgSig bundle replayRead pkg →
            UnaryHistory transport ∧
              UnaryHistory continuation ∧
                UnaryHistory ledgerRead ∧
                  UnaryHistory replayRead ∧
                    Cont transport continuation ledgerRead ∧
                      Cont ledgerRead localName replayRead ∧
                        PkgSig bundle localName pkg ∧
                          PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier ledgerCont replayCont replayPkg
  rcases carrier with
    ⟨_bidirectionalUnary, _directionUnary, _replacementUnary, transportUnary,
      continuationUnary, _provenanceUnary, localNameUnary, _carrierForward,
      _carrierReverse, localNamePkg⟩
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary continuationUnary ledgerCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed ledgerUnary localNameUnary replayCont
  exact
    ⟨transportUnary, continuationUnary, ledgerUnary, replayUnary, ledgerCont,
      replayCont, localNamePkg, replayPkg⟩

theorem PropextTransportBoundaryNonEscape [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      contextRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport
        continuation provenance localName bundle pkg →
      Cont replacement continuation contextRead →
        PkgSig bundle contextRead pkg →
          UnaryHistory contextRead ∧
            Cont replacement continuation contextRead ∧
              PkgSig bundle localName pkg ∧
                PkgSig bundle contextRead pkg ∧
                  hsame bidirectional bidirectional ∧
                    hsame replacement replacement ∧
                      hsame continuation continuation := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier contextCont contextPkg
  rcases carrier with
    ⟨_bidirectionalUnary, _directionUnary, replacementUnary, _transportUnary,
      continuationUnary, _provenanceUnary, _localNameUnary, _carrierForward,
      _carrierReverse, localNamePkg⟩
  have contextUnary : UnaryHistory contextRead :=
    unary_cont_closed replacementUnary continuationUnary contextCont
  exact
    ⟨contextUnary, contextCont, localNamePkg, contextPkg, hsame_refl bidirectional,
      hsame_refl replacement, hsame_refl continuation⟩

theorem PropextTransportBoundaryContextReplacementLocality [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      contextRead ledgerRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport
        continuation provenance localName bundle pkg →
      Cont replacement transport contextRead →
        Cont bidirectional direction ledgerRead →
          Cont contextRead localName replayRead →
            PkgSig bundle contextRead pkg →
              PkgSig bundle replayRead pkg →
                UnaryHistory replacement ∧
                  UnaryHistory transport ∧
                    UnaryHistory contextRead ∧
                      UnaryHistory replayRead ∧
                        Cont replacement transport contextRead ∧
                          Cont contextRead localName replayRead ∧
                            PkgSig bundle localName pkg ∧
                              PkgSig bundle contextRead pkg ∧
                                PkgSig bundle replayRead pkg ∧
                                  hsame replacement replacement ∧
                                    hsame transport transport := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier contextCont _ledgerCont replayCont contextPkg replayPkg
  rcases carrier with
    ⟨_bidirectionalUnary, _directionUnary, replacementUnary, transportUnary,
      _continuationUnary, _provenanceUnary, localNameUnary, _carrierLedger,
      _carrierContext, localNamePkg⟩
  have contextUnary : UnaryHistory contextRead :=
    unary_cont_closed replacementUnary transportUnary contextCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed contextUnary localNameUnary replayCont
  exact
    ⟨replacementUnary, transportUnary, contextUnary, replayUnary, contextCont, replayCont,
      localNamePkg, contextPkg, replayPkg, hsame_refl replacement, hsame_refl transport⟩

end BEDC.Derived.PropextTransportBoundaryUp
