import BEDC.Derived.PropextTransportBoundaryUp

namespace BEDC.Derived.PropextTransportBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PropextTransportBoundaryNameCertObligations [AskSetup] [PackageSetup]
    {bidirectional direction replacement transport continuation provenance localName ledgerRead
      contextRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PropextTransportBoundaryCarrier bidirectional direction replacement transport continuation
        provenance localName bundle pkg ->
      Cont bidirectional direction ledgerRead ->
        Cont replacement transport contextRead ->
          PkgSig bundle ledgerRead pkg ->
            PkgSig bundle contextRead pkg ->
              UnaryHistory bidirectional ∧ UnaryHistory direction ∧ UnaryHistory replacement ∧
                UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
                  UnaryHistory localName ∧ UnaryHistory ledgerRead ∧ UnaryHistory contextRead ∧
                    Cont bidirectional direction ledgerRead ∧
                      Cont replacement transport contextRead ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle ledgerRead pkg ∧ PkgSig bundle contextRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro carrier ledgerCont contextCont ledgerPkg contextPkg
  rcases carrier with
    ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary,
      continuationUnary, provenanceUnary, localNameUnary, _carrierLedger, _carrierContext,
      localNamePkg⟩
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed bidirectionalUnary directionUnary ledgerCont
  have contextUnary : UnaryHistory contextRead :=
    unary_cont_closed replacementUnary transportUnary contextCont
  exact
    ⟨bidirectionalUnary, directionUnary, replacementUnary, transportUnary, continuationUnary,
      provenanceUnary, localNameUnary, ledgerUnary, contextUnary, ledgerCont, contextCont,
      localNamePkg, ledgerPkg, contextPkg⟩

end BEDC.Derived.PropextTransportBoundaryUp
