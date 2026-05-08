import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparableExtSourceSurface [AskSetup] [PackageSetup]
    (fieldExt polynomial generator minimal simpleRoot provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory generator ∧
    UnaryHistory minimal ∧ UnaryHistory simpleRoot ∧
      Cont fieldExt polynomial provenance ∧ Cont provenance simpleRoot endpoint ∧
        PkgSig bundle endpoint pkg

theorem SeparableExtSourceSurface_dependency_ledger_closure [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot provenance endpoint
        bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        hsame provenance (append fieldExt polynomial) ∧
          hsame endpoint (append provenance simpleRoot) ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed surface.left surface.right.left
      surface.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary surface.right.right.right.right.left
      surface.right.right.right.right.right.right.left
  exact And.intro provenanceUnary
    (And.intro endpointUnary
      (And.intro surface.right.right.right.right.right.left
        (And.intro surface.right.right.right.right.right.right.left
          surface.right.right.right.right.right.right.right)))

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

theorem SeparableExtSourceSurface_simple_root_obligation [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot simpleRoot' provenance endpoint
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot provenance endpoint
        bundle pkg ->
      hsame simpleRoot simpleRoot' ->
        Cont provenance simpleRoot' endpoint' ->
          PkgSig bundle endpoint' pkg ->
            SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot' provenance
                endpoint' bundle pkg ∧
              hsame endpoint endpoint' := by
  intro surface sameSimpleRoot endpointCont' pkgSig'
  have simpleRootUnary' : UnaryHistory simpleRoot' :=
    unary_transport surface.right.right.right.right.left sameSimpleRoot
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameSimpleRoot
      surface.right.right.right.right.right.right.left endpointCont'
  exact And.intro
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left
            (And.intro simpleRootUnary'
              (And.intro surface.right.right.right.right.right.left
                (And.intro endpointCont' pkgSig')))))))
    sameEndpoint

end BEDC.Derived.SeparableExtUp
