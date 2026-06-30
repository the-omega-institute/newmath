import BEDC.Derived.NonAxiomAdmissionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NonAxiomAdmissionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NonAxiomAdmissionCarrier [AskSetup] [PackageSetup]
    (proposal acceptedForm witnessRoute transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory proposal ∧ UnaryHistory acceptedForm ∧ UnaryHistory witnessRoute ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧
      Cont proposal acceptedForm witnessRoute ∧ Cont witnessRoute transport replay ∧
        Cont replay provenance localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem NonAxiomAdmissionCarrier_boundary_exhaustion [AskSetup] [PackageSetup]
    {proposal acceptedForm witnessRoute transport replay provenance localName
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NonAxiomAdmissionCarrier proposal acceptedForm witnessRoute transport replay provenance
        localName bundle pkg ->
      Cont proposal acceptedForm boundaryRead ->
        PkgSig bundle boundaryRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row proposal ∨ hsame row acceptedForm ∨
                  hsame row witnessRoute ∨ hsame row boundaryRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont proposal acceptedForm boundaryRead ∧
                  PkgSig bundle boundaryRead pkg)
              hsame ∧
            UnaryHistory proposal ∧ UnaryHistory acceptedForm ∧ UnaryHistory witnessRoute ∧
              UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier proposalAcceptedBoundary boundaryPkg
  obtain ⟨proposalUnary, acceptedFormUnary, witnessRouteUnary, _transportUnary,
    _replayUnary, _proposalAcceptedWitness, _witnessTransportReplay, _replayProvenanceLocal,
    _provenancePkg, _localNamePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed proposalUnary acceptedFormUnary proposalAcceptedBoundary
  have sourceAtBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row proposal ∨ hsame row acceptedForm ∨ hsame row witnessRoute ∨
              hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont proposal acceptedForm boundaryRead ∧
              PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceAtBoundary
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, proposalAcceptedBoundary, boundaryPkg⟩
  }
  exact ⟨cert, proposalUnary, acceptedFormUnary, witnessRouteUnary, boundaryUnary⟩

end BEDC.Derived.NonAxiomAdmissionUp
