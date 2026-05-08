import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparableExtSourceRow [AskSetup] [PackageSetup]
    (field polynomial simple provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory field ∧ UnaryHistory polynomial ∧ UnaryHistory simple ∧
    UnaryHistory provenance ∧ UnaryHistory endpoint ∧
      Cont field polynomial provenance ∧ Cont provenance simple endpoint ∧
        PkgSig bundle endpoint pkg

theorem SeparableExtSourceRow_classifier_stability [AskSetup] [PackageSetup]
    {field field' polynomial polynomial' simple simple' provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceRow field polynomial simple provenance endpoint bundle pkg ->
      hsame field field' ->
        hsame polynomial polynomial' ->
          hsame simple simple' ->
            Cont field' polynomial' provenance' ->
              Cont provenance' simple' endpoint' ->
                PkgSig bundle endpoint' pkg ->
                  SeparableExtSourceRow field' polynomial' simple' provenance' endpoint'
                      bundle pkg ∧
                    hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro row sameField samePolynomial sameSimple provenanceCont' endpointCont' pkgSig'
  have fieldUnary' : UnaryHistory field' :=
    unary_transport row.left sameField
  have polynomialUnary' : UnaryHistory polynomial' :=
    unary_transport row.right.left samePolynomial
  have simpleUnary' : UnaryHistory simple' :=
    unary_transport row.right.right.left sameSimple
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed fieldUnary' polynomialUnary' provenanceCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' simpleUnary' endpointCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameField samePolynomial row.right.right.right.right.right.left
      provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameSimple row.right.right.right.right.right.right.left
      endpointCont'
  exact And.intro
    (And.intro fieldUnary'
      (And.intro polynomialUnary'
        (And.intro simpleUnary'
          (And.intro provenanceUnary'
            (And.intro endpointUnary'
              (And.intro provenanceCont'
                (And.intro endpointCont' pkgSig')))))))
    (And.intro sameProvenance sameEndpoint)

theorem SeparableExtSourceRow_semantic_name_certificate [AskSetup] [PackageSetup]
    {field polynomial simple provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceRow field polynomial simple provenance endpoint bundle pkg ->
      SemanticNameCert
        (fun e : BHist => ∃ p : BHist,
          SeparableExtSourceRow field polynomial simple p e bundle pkg)
        (fun e : BHist => ∃ p : BHist,
          SeparableExtSourceRow field polynomial simple p e bundle pkg)
        (fun e : BHist => ∃ p : BHist,
          SeparableExtSourceRow field polynomial simple p e bundle pkg)
        (fun left right : BHist =>
          (∃ leftProv : BHist,
            SeparableExtSourceRow field polynomial simple leftProv left bundle pkg) ∧
            (∃ rightProv : BHist,
              SeparableExtSourceRow field polynomial simple rightProv right bundle pkg) ∧
              hsame left right) := by
  intro row
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (Exists.intro provenance row)
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

end BEDC.Derived.SeparableExtUp
