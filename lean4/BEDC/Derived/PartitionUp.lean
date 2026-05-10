import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PartitionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PartitionBHistCarrier [AskSetup] [PackageSetup]
    (listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory listRow ∧ UnaryHistory partRows ∧ UnaryHistory sumRow ∧
    UnaryHistory decreaseRows ∧ UnaryHistory boundary ∧ Cont listRow sumRow route ∧
      Cont decreaseRows boundary provenance ∧ Cont route provenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem PartitionBHistCarrier_obligation [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      UnaryHistory listRow ∧ UnaryHistory partRows ∧ UnaryHistory sumRow ∧
        UnaryHistory decreaseRows ∧ UnaryHistory boundary ∧ Cont listRow sumRow route ∧
          Cont decreaseRows boundary provenance ∧ Cont route provenance endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right⟩

theorem PartitionBHistCarrier_finite_namecert_surface [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧
        PkgSig bundle endpoint pkg := by
  intro carrier
  have endpointSource :
      PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
          endpoint bundle pkg ∧
        hsame endpoint endpoint :=
    And.intro carrier (hsame_refl endpoint)
  have core :
      NameCert
        (fun row : BHist =>
          PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
            endpoint bundle pkg ∧ hsame row endpoint)
        hsame := {
    carrier_inhabited := Exists.intro endpoint endpointSource
    equiv_refl := by
      intro h _source
      exact hsame_refl h
    equiv_symm := by
      intro _h _k same
      exact hsame_symm same
    equiv_trans := by
      intro _h _k _r sameHK sameKR
      exact hsame_trans sameHK sameKR
    carrier_respects_equiv := by
      intro h k sameHK sourceH
      exact And.intro sourceH.left (hsame_trans (hsame_symm sameHK) sourceH.right)
  }
  exact
    And.intro
      {
        core := core
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }
      carrier.right.right.right.right.right.right.right.right

theorem PartitionBHistCarrier_classifier_stability [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint listRow' partRows'
      sumRow' decreaseRows' boundary' route' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      hsame listRow listRow' ->
        hsame partRows partRows' ->
          hsame sumRow sumRow' ->
            hsame decreaseRows decreaseRows' ->
              hsame boundary boundary' ->
                Cont listRow' sumRow' route' ->
                  Cont decreaseRows' boundary' provenance' ->
                    Cont route' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        PartitionBHistCarrier listRow' partRows' sumRow' decreaseRows'
                            boundary' route' provenance' endpoint' bundle pkg ∧
                          hsame route route' ∧ hsame provenance provenance' ∧
                            hsame endpoint endpoint' := by
  intro carrier sameList sameParts sameSum sameDecrease sameBoundary routeCont'
    provenanceCont' endpointCont' endpointPkg'
  have routeSame : hsame route route' :=
    cont_respects_hsame sameList sameSum carrier.right.right.right.right.right.left routeCont'
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame sameDecrease sameBoundary
      carrier.right.right.right.right.right.right.left provenanceCont'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame routeSame provenanceSame
      carrier.right.right.right.right.right.right.right.left endpointCont'
  have transportedCarrier :
      PartitionBHistCarrier listRow' partRows' sumRow' decreaseRows' boundary' route'
        provenance' endpoint' bundle pkg :=
    And.intro (unary_transport carrier.left sameList)
      (And.intro (unary_transport carrier.right.left sameParts)
        (And.intro (unary_transport carrier.right.right.left sameSum)
          (And.intro (unary_transport carrier.right.right.right.left sameDecrease)
            (And.intro (unary_transport carrier.right.right.right.right.left sameBoundary)
              (And.intro routeCont'
                (And.intro provenanceCont' (And.intro endpointCont' endpointPkg')))))))
  exact
    And.intro transportedCarrier
      (And.intro routeSame (And.intro provenanceSame endpointSame))

theorem PartitionBHistCarrier_young_boundary_package [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint routeBoundary
      packaged : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      Cont route boundary routeBoundary ->
        Cont provenance routeBoundary packaged ->
          PkgSig bundle packaged pkg ->
            UnaryHistory routeBoundary ∧ UnaryHistory packaged ∧
              hsame routeBoundary (append route boundary) ∧
                hsame packaged (append provenance routeBoundary) := by
  intro carrier routeBoundaryCont packagedCont _packagedPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed carrier.left carrier.right.right.left
      carrier.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed carrier.right.right.right.left carrier.right.right.right.right.left
      carrier.right.right.right.right.right.right.left
  have routeBoundaryUnary : UnaryHistory routeBoundary :=
    unary_cont_closed routeUnary carrier.right.right.right.right.left routeBoundaryCont
  have packagedUnary : UnaryHistory packaged :=
    unary_cont_closed provenanceUnary routeBoundaryUnary packagedCont
  exact
    ⟨routeBoundaryUnary,
      packagedUnary,
      routeBoundaryCont,
      packagedCont⟩

theorem PartitionBHistCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {listRow partRows sumRow weakRows boundaryRow routeLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory listRow ->
      UnaryHistory partRows ->
        UnaryHistory weakRows ->
          UnaryHistory routeLedger ->
            UnaryHistory provenance ->
              Cont listRow partRows sumRow ->
                Cont sumRow weakRows boundaryRow ->
                  Cont boundaryRow routeLedger endpoint ->
                    PkgSig bundle endpoint pkg ->
                      UnaryHistory sumRow ∧ UnaryHistory boundaryRow ∧
                        UnaryHistory endpoint ∧ hsame sumRow (append listRow partRows) ∧
                          hsame boundaryRow (append sumRow weakRows) ∧
                            hsame endpoint (append boundaryRow routeLedger) ∧
                              PkgSig bundle endpoint pkg := by
  intro listUnary partUnary weakUnary routeUnary _provenanceUnary listPartRow weakBoundaryRow
    routeEndpointRow pkgSig
  have sumUnary : UnaryHistory sumRow :=
    unary_cont_closed listUnary partUnary listPartRow
  have boundaryUnary : UnaryHistory boundaryRow :=
    unary_cont_closed sumUnary weakUnary weakBoundaryRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed boundaryUnary routeUnary routeEndpointRow
  exact
    And.intro sumUnary
      (And.intro boundaryUnary
        (And.intro endpointUnary
          (And.intro listPartRow
            (And.intro weakBoundaryRow
              (And.intro routeEndpointRow pkgSig)))))

theorem PartitionBHistCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {listRow partRows sumRow decreaseRows boundary route provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              row bundle pkg)
        (fun row : BHist =>
          exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              row bundle pkg)
        (fun row : BHist =>
          exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              row bundle pkg)
        (fun h k : BHist =>
          (exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
            PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
              h bundle pkg) ∧
            (exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
              PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance
                k bundle pkg) ∧
              hsame h k) := by
  intro carrier
  let SourceSpec : BHist -> Prop := fun row =>
    exists listRow partRows sumRow decreaseRows boundary route provenance : BHist,
      PartitionBHistCarrier listRow partRows sumRow decreaseRows boundary route provenance row
        bundle pkg
  have endpointSource : SourceSpec endpoint := by
    exact
      ⟨listRow, partRows, sumRow, decreaseRows, boundary, route, provenance, carrier⟩
  constructor
  · constructor
    · exact ⟨endpoint, endpointSource⟩
    · intro h source
      exact ⟨source, source, hsame_refl h⟩
    · intro h k classified
      exact ⟨classified.right.left, classified.left, hsame_symm classified.right.right⟩
    · intro h k r classifiedHK classifiedKR
      exact
        ⟨classifiedHK.left, classifiedKR.right.left,
          hsame_trans classifiedHK.right.right classifiedKR.right.right⟩
    · intro h k classified _source
      exact classified.right.left
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.PartitionUp
