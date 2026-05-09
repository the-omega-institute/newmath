import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ErgodicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.ErgodicUp
