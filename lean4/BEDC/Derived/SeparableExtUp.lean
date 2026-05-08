import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp

theorem SeparableExtSimpleRoot_obligation
    {fieldPacket polynomialPacket minimalPolynomial derivativeWitness simpleRootRow packageLedger :
      BHist} :
    UnaryHistory fieldPacket ->
      UnaryHistory polynomialPacket ->
        PolynomialSingletonCarrier minimalPolynomial ->
          UnaryHistory derivativeWitness ->
            Cont minimalPolynomial derivativeWitness simpleRootRow ->
              Cont fieldPacket polynomialPacket packageLedger ->
                UnaryHistory simpleRootRow ∧
                  hsame simpleRootRow (append minimalPolynomial derivativeWitness) ∧
                    hsame packageLedger (append fieldPacket polynomialPacket) := by
  intro _ _ minimalCarrier derivativeUnary simpleRootCont packageCont
  have minimalUnary : UnaryHistory minimalPolynomial := by
    cases minimalCarrier
    exact unary_empty
  constructor
  · exact unary_cont_closed minimalUnary derivativeUnary simpleRootCont
  · constructor
    · exact simpleRootCont
    · exact packageCont

def SeparableExtJointSource
    (field polynomial generator minpoly derivative provenance endpoint : BHist) : Prop :=
  FieldExtSingletonCarrier field ∧ PolynomialSingletonCarrier polynomial ∧
    UnaryHistory generator ∧ UnaryHistory derivative ∧
      PolynomialSingletonClassifier minpoly polynomial ∧ Cont polynomial derivative provenance ∧
        Cont provenance generator endpoint

theorem SeparableExtJointSource_fieldext_polynomial_source
    {field polynomial generator minpoly derivative provenance endpoint : BHist} :
    SeparableExtJointSource field polynomial generator minpoly derivative provenance endpoint ->
      FieldExtSingletonCarrier field ∧ PolynomialSingletonCarrier polynomial ∧
        UnaryHistory generator ∧ UnaryHistory derivative ∧
          PolynomialSingletonClassifier minpoly polynomial ∧
            Cont polynomial derivative provenance ∧ Cont provenance generator endpoint ∧
              UnaryHistory endpoint ∧
                hsame endpoint (append (append polynomial derivative) generator) := by
  intro source
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed
      (unary_transport unary_empty (hsame_symm source.right.left))
      source.right.right.right.left
      source.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary source.right.right.left
      source.right.right.right.right.right.right
  have endpointReadback :
      hsame endpoint (append (append polynomial derivative) generator) :=
    hsame_trans source.right.right.right.right.right.right
      (congrArg (fun row : BHist => append row generator)
        source.right.right.right.right.right.left)
  exact And.intro source.left
    (And.intro source.right.left
      (And.intro source.right.right.left
        (And.intro source.right.right.right.left
          (And.intro source.right.right.right.right.left
            (And.intro source.right.right.right.right.right.left
              (And.intro source.right.right.right.right.right.right
                (And.intro endpointUnary endpointReadback)))))))

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

theorem SeparableExtSourceSurface_classifier_stability [AskSetup] [PackageSetup]
    {fieldExt fieldExt' polynomial polynomial' generator generator' minimal minimal'
      simpleRoot simpleRoot' provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot provenance endpoint
        bundle pkg ->
      hsame fieldExt fieldExt' ->
        hsame polynomial polynomial' ->
          hsame generator generator' ->
            hsame minimal minimal' ->
              hsame simpleRoot simpleRoot' ->
                Cont fieldExt' polynomial' provenance' ->
                  Cont provenance' simpleRoot' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      SeparableExtSourceSurface fieldExt' polynomial' generator' minimal'
                          simpleRoot' provenance' endpoint' bundle pkg ∧
                        hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro surface sameField samePolynomial sameGenerator sameMinimal sameSimpleRoot provenanceCont'
    endpointCont' pkgSig'
  have fieldUnary' : UnaryHistory fieldExt' :=
    unary_transport surface.left sameField
  have polynomialUnary' : UnaryHistory polynomial' :=
    unary_transport surface.right.left samePolynomial
  have generatorUnary' : UnaryHistory generator' :=
    unary_transport surface.right.right.left sameGenerator
  have minimalUnary' : UnaryHistory minimal' :=
    unary_transport surface.right.right.right.left sameMinimal
  have simpleRootUnary' : UnaryHistory simpleRoot' :=
    unary_transport surface.right.right.right.right.left sameSimpleRoot
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameField samePolynomial surface.right.right.right.right.right.left
      provenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameSimpleRoot
      surface.right.right.right.right.right.right.left endpointCont'
  exact And.intro
    (And.intro fieldUnary'
      (And.intro polynomialUnary'
        (And.intro generatorUnary'
          (And.intro minimalUnary'
            (And.intro simpleRootUnary'
              (And.intro provenanceCont' (And.intro endpointCont' pkgSig')))))))
    (And.intro sameProvenance sameEndpoint)

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

theorem SeparableExtSourceSurface_semantic_name_certificate [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot provenance endpoint
        bundle pkg ->
      SemanticNameCert
        (fun target : BHist =>
          exists carriedProvenance : BHist,
            SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot
              carriedProvenance target bundle pkg)
        (fun target : BHist =>
          exists carriedProvenance : BHist,
            SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot
              carriedProvenance target bundle pkg)
        (fun target : BHist =>
          exists carriedProvenance : BHist,
            SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot
              carriedProvenance target bundle pkg)
        (fun left right : BHist =>
          (exists leftProvenance : BHist,
            SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot
              leftProvenance left bundle pkg) /\
            (exists rightProvenance : BHist,
              SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot
                rightProvenance right bundle pkg) /\
              hsame left right) := by
  intro surface
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (Exists.intro provenance surface)
      equiv_refl := by
        intro target targetSurface
        exact And.intro targetSurface (And.intro targetSurface (hsame_refl target))
      equiv_symm := by
        intro left right classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro left middle right leftMiddle middleRight
        exact And.intro leftMiddle.left
          (And.intro middleRight.right.left
            (hsame_trans leftMiddle.right.right middleRight.right.right))
      carrier_respects_equiv := by
        intro left right classified _leftSurface
        exact classified.right.left
    }
    pattern_sound := by
      intro _target source
      exact source
    ledger_sound := by
      intro _target source
      exact source
  }

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
