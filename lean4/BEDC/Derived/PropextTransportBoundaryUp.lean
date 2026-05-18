import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PropextTransportBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem PropextTransportBoundaryThreeAxiomsSiblingLink [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport
        continuation provenance localName bundle pkg →
      Cont transport continuation siblingRead →
        PkgSig bundle siblingRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row localName ∧
                  PropextTransportBoundaryCarrier bidirectional direction replacement
                    transport continuation provenance localName bundle pkg)
              (fun row : BHist => hsame row localName ∧
                Cont transport continuation siblingRead)
              (fun row : BHist => hsame row localName ∧ PkgSig bundle siblingRead pkg)
              hsame ∧
            UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory siblingRead ∧
              Cont transport continuation siblingRead ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle siblingRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier transportContinuation siblingPkg
  have carrierWitness := carrier
  obtain ⟨_bidirectionalUnary, _directionUnary, _replacementUnary, transportUnary,
    continuationUnary, _provenanceUnary, _localNameUnary, _carrierForward,
    _carrierReverse, localNamePkg⟩ := carrier
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed transportUnary continuationUnary transportContinuation
  have sourceAtName :
      hsame localName localName ∧
        PropextTransportBoundaryCarrier bidirectional direction replacement transport
          continuation provenance localName bundle pkg :=
    And.intro (hsame_refl localName) carrierWitness
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              PropextTransportBoundaryCarrier bidirectional direction replacement transport
                continuation provenance localName bundle pkg)
          (fun row : BHist => hsame row localName ∧
            Cont transport continuation siblingRead)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle siblingRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceAtName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left transportContinuation
    ledger_sound := by
      intro _row source
      exact And.intro source.left siblingPkg
  }
  exact
    ⟨cert, transportUnary, continuationUnary, siblingUnary, transportContinuation,
      localNamePkg, siblingPkg⟩

theorem PropextTransportBoundaryDirectionLedgerCoverage [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName
      forwardRead reverseRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport continuation
        provenance localName bundle pkg ->
      Cont bidirectional direction forwardRead ->
        Cont replacement transport reverseRead ->
          Cont transport continuation ledgerRead ->
            PkgSig bundle forwardRead pkg ->
              PkgSig bundle reverseRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  UnaryHistory direction ∧ UnaryHistory forwardRead ∧
                    UnaryHistory reverseRead ∧ UnaryHistory ledgerRead ∧
                      Cont bidirectional direction forwardRead ∧
                        Cont replacement transport reverseRead ∧
                          Cont transport continuation ledgerRead ∧
                            PkgSig bundle localName pkg ∧
                              PkgSig bundle forwardRead pkg ∧
                                PkgSig bundle reverseRead pkg ∧
                                  PkgSig bundle ledgerRead pkg ∧
                                    hsame bidirectional bidirectional := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier forwardCont reverseCont ledgerCont forwardPkg reversePkg ledgerPkg
  rcases carrier with
    ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary,
      continuationUnary, _provenanceUnary, _localNameUnary, _carrierDirection,
      _carrierReplacement, localNamePkg⟩
  have forwardUnary : UnaryHistory forwardRead :=
    unary_cont_closed bidirectionalUnary directionUnary forwardCont
  have reverseUnary : UnaryHistory reverseRead :=
    unary_cont_closed replacementUnary transportUnary reverseCont
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary continuationUnary ledgerCont
  exact
    ⟨directionUnary, forwardUnary, reverseUnary, ledgerUnary, forwardCont,
      reverseCont, ledgerCont, localNamePkg, forwardPkg, reversePkg, ledgerPkg,
      hsame_refl bidirectional⟩

theorem PropextTransportBoundaryTasteGateRefusalExactness [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName contextRead
      replayRead forwardRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport continuation
        provenance localName bundle pkg →
      Cont replacement transport contextRead →
        Cont contextRead localName replayRead →
          Cont bidirectional direction forwardRead →
            Cont transport continuation ledgerRead →
              PkgSig bundle replayRead pkg →
                PkgSig bundle forwardRead pkg →
                  PkgSig bundle ledgerRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row localName ∧
                            PropextTransportBoundaryCarrier bidirectional direction replacement
                              transport continuation provenance localName bundle pkg)
                        (fun row : BHist =>
                          hsame row localName ∧ Cont replacement transport contextRead ∧
                            Cont contextRead localName replayRead)
                        (fun row : BHist =>
                          hsame row localName ∧ PkgSig bundle replayRead pkg ∧
                            PkgSig bundle ledgerRead pkg)
                        hsame ∧
                      UnaryHistory contextRead ∧ UnaryHistory replayRead ∧
                        UnaryHistory forwardRead ∧ UnaryHistory ledgerRead ∧
                          Cont replacement transport contextRead ∧
                            Cont contextRead localName replayRead ∧
                              Cont bidirectional direction forwardRead ∧
                                Cont transport continuation ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier contextCont replayCont forwardCont ledgerCont replayPkg _forwardPkg ledgerPkg
  have carrierWitness := carrier
  obtain ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary,
    continuationUnary, _provenanceUnary, localNameUnary, _carrierDirection,
    _carrierReplacement, _localNamePkg⟩ := carrier
  have contextUnary : UnaryHistory contextRead :=
    unary_cont_closed replacementUnary transportUnary contextCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed contextUnary localNameUnary replayCont
  have forwardUnary : UnaryHistory forwardRead :=
    unary_cont_closed bidirectionalUnary directionUnary forwardCont
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed transportUnary continuationUnary ledgerCont
  have sourceAtName :
      hsame localName localName ∧
        PropextTransportBoundaryCarrier bidirectional direction replacement transport
          continuation provenance localName bundle pkg :=
    And.intro (hsame_refl localName) carrierWitness
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              PropextTransportBoundaryCarrier bidirectional direction replacement transport
                continuation provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row localName ∧ Cont replacement transport contextRead ∧
              Cont contextRead localName replayRead)
          (fun row : BHist =>
            hsame row localName ∧ PkgSig bundle replayRead pkg ∧
              PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceAtName
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, contextCont, replayCont⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, replayPkg, ledgerPkg⟩
  }
  exact
    ⟨cert, contextUnary, replayUnary, forwardUnary, ledgerUnary, contextCont,
      replayCont, forwardCont, ledgerCont⟩

end BEDC.Derived.PropextTransportBoundaryUp
