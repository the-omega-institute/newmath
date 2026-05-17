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

end BEDC.Derived.PropextTransportBoundaryUp
