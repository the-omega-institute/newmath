import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.EnrichedCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EnrichedCatCertificateSurface [AskSetup] [PackageSetup]
    (category monoidal hom identity transport provenance readback endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory monoidal ∧ UnaryHistory hom ∧
    UnaryHistory identity ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont hom identity (append hom identity) ∧
        Cont (append hom identity) transport readback ∧
          Cont provenance readback endpoint ∧ PkgSig bundle endpoint pkg

theorem EnrichedCatCertificateSurface_source_obligation [AskSetup] [PackageSetup]
    {category monoidal hom identity transport provenance readback endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatCertificateSurface category monoidal hom identity transport provenance
        readback endpoint bundle pkg ->
      UnaryHistory category ∧ UnaryHistory monoidal ∧ UnaryHistory hom ∧
        UnaryHistory identity ∧ UnaryHistory readback ∧ UnaryHistory endpoint ∧
          Cont provenance readback endpoint ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have homUnary : UnaryHistory hom := surface.right.right.left
  have identityUnary : UnaryHistory identity := surface.right.right.right.left
  have transportUnary : UnaryHistory transport := surface.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := surface.right.right.right.right.right.left
  have homIdentityUnary : UnaryHistory (append hom identity) :=
    unary_cont_closed homUnary identityUnary surface.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed homIdentityUnary transportUnary
      surface.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary readbackUnary
      surface.right.right.right.right.right.right.right.right.left
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro homUnary
        (And.intro identityUnary
          (And.intro readbackUnary
            (And.intro endpointUnary
              (And.intro surface.right.right.right.right.right.right.right.right.left
                surface.right.right.right.right.right.right.right.right.right))))))

def EnrichedCatSourceSurface [AskSetup] [PackageSetup]
    (category monoidal hom identity composition transport provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory monoidal ∧ UnaryHistory hom ∧
    UnaryHistory identity ∧ UnaryHistory composition ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ Cont hom identity composition ∧
        Cont composition transport ledger ∧ Cont provenance ledger endpoint ∧
          PkgSig bundle endpoint pkg

theorem EnrichedCatSourceSurface_source_obligation [AskSetup] [PackageSetup]
    {category monoidal hom identity composition transport provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatSourceSurface category monoidal hom identity composition transport provenance
        ledger endpoint bundle pkg ->
      UnaryHistory category ∧ UnaryHistory monoidal ∧ UnaryHistory hom ∧
        UnaryHistory identity ∧ UnaryHistory composition ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ Cont hom identity composition ∧
            Cont composition transport ledger ∧ hsame ledger (append composition transport) ∧
              hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed surface.right.right.right.right.left surface.right.right.right.right.right.left
      surface.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed surface.right.right.right.right.right.right.left ledgerUnary
      surface.right.right.right.right.right.right.right.right.right.left
  constructor
  · exact surface.left
  constructor
  · exact surface.right.left
  constructor
  · exact surface.right.right.left
  constructor
  · exact surface.right.right.right.left
  constructor
  · exact surface.right.right.right.right.left
  constructor
  · exact ledgerUnary
  constructor
  · exact endpointUnary
  constructor
  · exact surface.right.right.right.right.right.right.right.left
  constructor
  · exact surface.right.right.right.right.right.right.right.right.left
  constructor
  · exact surface.right.right.right.right.right.right.right.right.left
  constructor
  · exact surface.right.right.right.right.right.right.right.right.right.left
  · exact surface.right.right.right.right.right.right.right.right.right.right

theorem EnrichedCatSourceSurface_classifier_transport_obligation [AskSetup] [PackageSetup]
    {category monoidal hom identity composition transport provenance ledger endpoint category'
      monoidal' hom' identity' composition' transport' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatSourceSurface category monoidal hom identity composition transport provenance
        ledger endpoint bundle pkg ->
      hsame category category' ->
        hsame monoidal monoidal' ->
          hsame hom hom' ->
            hsame identity identity' ->
              hsame transport transport' ->
                hsame provenance provenance' ->
                  Cont hom' identity' composition' ->
                    Cont composition' transport' ledger' ->
                      Cont provenance' ledger' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          EnrichedCatSourceSurface category' monoidal' hom' identity'
                              composition' transport' provenance' ledger' endpoint' bundle pkg ∧
                            hsame composition composition' ∧ hsame ledger ledger' ∧
                              hsame endpoint endpoint' := by
  intro surface sameCategory sameMonoidal sameHom sameIdentity sameTransport sameProvenance
  intro compositionRow' ledgerRow' endpointRow' pkgSig'
  have categoryUnary' : UnaryHistory category' :=
    unary_transport surface.left sameCategory
  have monoidalUnary' : UnaryHistory monoidal' :=
    unary_transport surface.right.left sameMonoidal
  have homUnary' : UnaryHistory hom' :=
    unary_transport surface.right.right.left sameHom
  have identityUnary' : UnaryHistory identity' :=
    unary_transport surface.right.right.right.left sameIdentity
  have sameComposition : hsame composition composition' :=
    cont_respects_hsame sameHom sameIdentity surface.right.right.right.right.right.right.right.left
      compositionRow'
  have compositionUnary' : UnaryHistory composition' :=
    unary_cont_closed homUnary' identityUnary' compositionRow'
  have transportUnary' : UnaryHistory transport' :=
    unary_transport surface.right.right.right.right.right.left sameTransport
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport surface.right.right.right.right.right.right.left sameProvenance
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameComposition sameTransport
      surface.right.right.right.right.right.right.right.right.left ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger
      surface.right.right.right.right.right.right.right.right.right.left endpointRow'
  exact And.intro
    (And.intro categoryUnary'
      (And.intro monoidalUnary'
        (And.intro homUnary'
          (And.intro identityUnary'
            (And.intro compositionUnary'
              (And.intro transportUnary'
                (And.intro provenanceUnary'
                  (And.intro compositionRow'
                    (And.intro ledgerRow' (And.intro endpointRow' pkgSig'))))))))))
    (And.intro sameComposition (And.intro sameLedger sameEndpoint))

def EnrichedCatPublicPacket [AskSetup] [PackageSetup]
    (categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory categoryBoundary ∧
    UnaryHistory monoidalBoundary ∧
      UnaryHistory homObject ∧
        UnaryHistory identity ∧
          UnaryHistory composition ∧
            UnaryHistory transport ∧
              Cont homObject identity composition ∧
                Cont transport provenance ledger ∧
                  Cont ledger monoidalBoundary endpoint ∧
                    PkgSig bundle endpoint pkg

theorem EnrichedCatPublicPacket_source_obligation [AskSetup] [PackageSetup]
    {categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatPublicPacket categoryBoundary monoidalBoundary homObject identity composition
      transport provenance ledger endpoint bundle pkg ->
      UnaryHistory categoryBoundary ∧
        UnaryHistory monoidalBoundary ∧
          UnaryHistory homObject ∧
            UnaryHistory identity ∧
              UnaryHistory composition ∧
                UnaryHistory transport ∧
                  Cont homObject identity composition ∧
                    Cont transport provenance ledger ∧
                      Cont ledger monoidalBoundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact packet

end BEDC.Derived.EnrichedCatUp
