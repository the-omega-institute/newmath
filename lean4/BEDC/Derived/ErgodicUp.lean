import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ErgodicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ErgodicBHistSourceSurface [AskSetup] [PackageSetup]
    (dyn measure invariant transport ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dyn ∧ UnaryHistory measure ∧ UnaryHistory transport ∧
    UnaryHistory provenance ∧ Cont invariant transport ledger ∧
      Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

def ErgodicMeasurePreservingCarrier [AskSetup] [PackageSetup]
    (dyn measure invariant transport ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ErgodicBHistSourceSurface dyn measure invariant transport ledger provenance endpoint bundle
    pkg ∧ hsame invariant (append dyn measure)

theorem ErgodicBHistSourceSurface_invariant_subspace_classifier [AskSetup] [PackageSetup]
    {dyn measure invariant transport ledger provenance endpoint invariant' transport' ledger'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingCarrier dyn measure invariant transport ledger provenance endpoint
        bundle pkg ->
      hsame invariant invariant' ->
        hsame transport transport' ->
          Cont invariant' transport' ledger' ->
            Cont provenance ledger' endpoint' ->
              PkgSig bundle endpoint' pkg ->
                ErgodicBHistSourceSurface dyn measure invariant' transport' ledger' provenance
                    endpoint' bundle pkg ∧
                  hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro carrier sameInvariant sameTransport ledgerRow' endpointRow' pkgSig'
  have surface :
      ErgodicBHistSourceSurface dyn measure invariant transport ledger provenance endpoint
        bundle pkg :=
    carrier.left
  have ledgerRow : Cont invariant transport ledger :=
    surface.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    surface.right.right.right.right.right.left
  have transportUnary' : UnaryHistory transport' :=
    unary_transport surface.right.right.left sameTransport
  have ledgerSame : hsame ledger ledger' :=
    cont_respects_hsame sameInvariant sameTransport ledgerRow ledgerRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) ledgerSame endpointRow endpointRow'
  exact And.intro
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro transportUnary'
          (And.intro surface.right.right.right.left
            (And.intro ledgerRow' (And.intro endpointRow' pkgSig'))))))
    (And.intro ledgerSame endpointSame)

theorem ErgodicMeasurePreservingCarrier_invariant_subspace_classifier [AskSetup]
    [PackageSetup]
    {dyn measure invariant transport ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingCarrier dyn measure invariant transport ledger provenance endpoint
        bundle pkg ->
      UnaryHistory dyn ∧ UnaryHistory measure ∧ UnaryHistory invariant ∧
        hsame invariant (append dyn measure) ∧ Cont invariant transport ledger ∧
          hsame ledger (append invariant transport) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have source :
      ErgodicBHistSourceSurface dyn measure invariant transport ledger provenance endpoint bundle
        pkg := carrier.left
  have dynUnary : UnaryHistory dyn := source.left
  have measureUnary : UnaryHistory measure := source.right.left
  have transportUnary : UnaryHistory transport := source.right.right.left
  have invariantReadback : hsame invariant (append dyn measure) := carrier.right
  have invariantUnary : UnaryHistory invariant :=
    unary_transport (unary_append_closed dynUnary measureUnary) (hsame_symm invariantReadback)
  have ledgerRow : Cont invariant transport ledger :=
    source.right.right.right.right.left
  have ledgerReadback : hsame ledger (append invariant transport) :=
    ledgerRow
  have pkgRow : PkgSig bundle endpoint pkg :=
    source.right.right.right.right.right.right
  exact And.intro dynUnary
    (And.intro measureUnary
      (And.intro invariantUnary
        (And.intro invariantReadback
          (And.intro ledgerRow
            (And.intro ledgerReadback pkgRow)))))

theorem ErgodicMeasurePreservingCarrier_decomposition_ledger [AskSetup] [PackageSetup]
    {dyn measure invariant transport ledger provenance endpoint decomposition : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingCarrier dyn measure invariant transport ledger provenance endpoint
        bundle pkg ->
      Cont ledger invariant decomposition ->
        UnaryHistory decomposition ∧ hsame decomposition (append ledger invariant) ∧
          hsame ledger (append invariant transport) ∧
            hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro carrier decompositionRow
  have source :
      ErgodicBHistSourceSurface dyn measure invariant transport ledger provenance endpoint bundle
        pkg := carrier.left
  have classifier :=
    ErgodicMeasurePreservingCarrier_invariant_subspace_classifier carrier
  have transportUnary : UnaryHistory transport :=
    source.right.right.left
  have provenanceEndpointRow : Cont provenance ledger endpoint :=
    source.right.right.right.right.right.left
  have invariantUnary : UnaryHistory invariant :=
    classifier.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed invariantUnary transportUnary classifier.right.right.right.right.right.left
  have decompositionUnary : UnaryHistory decomposition :=
    unary_cont_closed ledgerUnary invariantUnary decompositionRow
  have decompositionReadback : hsame decomposition (append ledger invariant) :=
    decompositionRow
  have endpointReadback : hsame endpoint (append provenance ledger) :=
    provenanceEndpointRow
  exact And.intro decompositionUnary
    (And.intro decompositionReadback
      (And.intro classifier.right.right.right.right.right.left
        (And.intro endpointReadback classifier.right.right.right.right.right.right)))

def ErgodicMeasurePreservingSurface [AskSetup] [PackageSetup]
    (dynamic measure invariant transport route endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dynamic ∧ UnaryHistory measure ∧ UnaryHistory invariant ∧
    UnaryHistory transport ∧ Cont invariant transport route ∧ Cont route measure endpoint ∧
      PkgSig bundle endpoint pkg

theorem ErgodicMeasurePreservingSurface_invariant_subspace_classifier [AskSetup]
    [PackageSetup] {dynamic measure invariant transport route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingSurface dynamic measure invariant transport route endpoint bundle pkg ->
      UnaryHistory dynamic ∧ UnaryHistory measure ∧ UnaryHistory invariant ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory endpoint ∧
          Cont invariant transport route ∧ Cont route measure endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro surface
  have routeUnary : UnaryHistory route :=
    unary_cont_closed surface.right.right.left surface.right.right.right.left
      surface.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary surface.right.left surface.right.right.right.right.right.left
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro surface.right.right.left
        (And.intro surface.right.right.right.left
          (And.intro routeUnary
            (And.intro endpointUnary
              (And.intro surface.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.left
                  surface.right.right.right.right.right.right)))))))

theorem ErgodicMeasurePreservingSurface_decomposition_ledger [AskSetup] [PackageSetup]
    {dynamic measure invariant transport route endpoint decomposition : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingSurface dynamic measure invariant transport route endpoint bundle pkg ->
      Cont endpoint invariant decomposition ->
        PkgSig bundle decomposition pkg ->
          UnaryHistory route ∧ UnaryHistory endpoint ∧ UnaryHistory decomposition ∧
            hsame route (append invariant transport) ∧ hsame endpoint (append route measure) ∧
              hsame decomposition (append endpoint invariant) ∧ PkgSig bundle decomposition pkg := by
  intro surface decompositionRow decompositionPkg
  have rows :=
    ErgodicMeasurePreservingSurface_invariant_subspace_classifier
      (dynamic := dynamic) (measure := measure) (invariant := invariant)
      (transport := transport) (route := route) (endpoint := endpoint)
      (bundle := bundle) (pkg := pkg) surface
  have decompositionUnary : UnaryHistory decomposition :=
    unary_cont_closed rows.right.right.right.right.right.left rows.right.right.left
      decompositionRow
  exact And.intro rows.right.right.right.right.left
    (And.intro rows.right.right.right.right.right.left
      (And.intro decompositionUnary
        (And.intro rows.right.right.right.right.right.right.left
          (And.intro rows.right.right.right.right.right.right.right.left
            (And.intro decompositionRow decompositionPkg)))))

theorem ErgodicMeasurePreservingCarrier_semantic_name_certificate [AskSetup]
    [PackageSetup]
    {dyn measure invariant transport ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ErgodicMeasurePreservingCarrier dyn measure invariant transport ledger provenance endpoint
        bundle pkg ->
      SemanticNameCert
        (fun h : BHist =>
          ErgodicMeasurePreservingCarrier dyn measure h transport ledger provenance endpoint
            bundle pkg)
        (fun h : BHist =>
          ErgodicMeasurePreservingCarrier dyn measure h transport ledger provenance endpoint
            bundle pkg)
        (fun h : BHist =>
          ErgodicMeasurePreservingCarrier dyn measure h transport ledger provenance endpoint
            bundle pkg)
        (fun h k : BHist =>
          ErgodicMeasurePreservingCarrier dyn measure h transport ledger provenance endpoint
              bundle pkg ∧
            ErgodicMeasurePreservingCarrier dyn measure k transport ledger provenance endpoint
              bundle pkg ∧
              hsame h k) := by
  intro carrier
  constructor
  · constructor
    · exact Exists.intro invariant carrier
    · intro h source
      exact And.intro source (And.intro source (hsame_refl h))
    · intro h k same
      exact And.intro same.right.left (And.intro same.left (hsame_symm same.right.right))
    · intro h k r sameHK sameKR
      exact And.intro sameHK.left
        (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
    · intro h k same _source
      exact same.right.left
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.ErgodicUp
