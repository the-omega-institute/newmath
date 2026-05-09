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
              UnaryHistory provenance ∧
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
                  UnaryHistory provenance ∧
                    Cont homObject identity composition ∧
                      Cont transport provenance ledger ∧
                        Cont ledger monoidalBoundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact packet

theorem EnrichedCatPublicRows_classifier_transport_obligation [AskSetup] [PackageSetup]
    {category tensor hom identity composition provenance ledger endpoint category' tensor' hom'
      identity' composition' provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory category ->
      UnaryHistory tensor ->
        UnaryHistory hom ->
          UnaryHistory identity ->
            UnaryHistory composition ->
              UnaryHistory provenance ->
                Cont hom identity ledger ->
                  Cont ledger composition endpoint ->
                    Cont endpoint provenance tensor ->
                      PkgSig bundle endpoint pkg ->
                        hsame category category' ->
                          hsame tensor tensor' ->
                            hsame hom hom' ->
                              hsame identity identity' ->
                                hsame composition composition' ->
                                  hsame provenance provenance' ->
                                    Cont hom' identity' ledger' ->
                                      Cont ledger' composition' endpoint' ->
                                        Cont endpoint' provenance' tensor' ->
                                          PkgSig bundle endpoint' pkg ->
                                            UnaryHistory category' ∧ UnaryHistory tensor' ∧
                                              UnaryHistory hom' ∧ UnaryHistory identity' ∧
                                                UnaryHistory composition' ∧
                                                  hsame ledger ledger' ∧
                                                    hsame endpoint endpoint' ∧
                                                      hsame tensor tensor' ∧
                                                        PkgSig bundle endpoint' pkg := by
  intro categoryUnary tensorUnary homUnary identityUnary compositionUnary _provenanceUnary
  intro ledgerRow endpointRow tensorRow _pkgSig sameCategory sameTensor sameHom sameIdentity
  intro sameComposition sameProvenance ledgerRow' endpointRow' tensorRow' pkgSig'
  have categoryUnary' : UnaryHistory category' :=
    unary_transport categoryUnary sameCategory
  have tensorUnary' : UnaryHistory tensor' :=
    unary_transport tensorUnary sameTensor
  have homUnary' : UnaryHistory hom' :=
    unary_transport homUnary sameHom
  have identityUnary' : UnaryHistory identity' :=
    unary_transport identityUnary sameIdentity
  have compositionUnary' : UnaryHistory composition' :=
    unary_transport compositionUnary sameComposition
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameHom sameIdentity ledgerRow ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameComposition endpointRow endpointRow'
  have sameTensorFromRows : hsame tensor tensor' :=
    cont_respects_hsame sameEndpoint sameProvenance tensorRow tensorRow'
  exact And.intro categoryUnary'
    (And.intro tensorUnary'
      (And.intro homUnary'
        (And.intro identityUnary'
          (And.intro compositionUnary'
            (And.intro sameLedger
              (And.intro sameEndpoint
                (And.intro sameTensorFromRows pkgSig')))))))

theorem EnrichedCatPublicPacket_classifier_transport_obligation [AskSetup] [PackageSetup]
    {categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint categoryBoundary' monoidalBoundary' homObject' identity' composition' transport'
      provenance' ledger' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatPublicPacket categoryBoundary monoidalBoundary homObject identity composition
        transport provenance ledger endpoint bundle pkg ->
      hsame categoryBoundary categoryBoundary' ->
        hsame monoidalBoundary monoidalBoundary' ->
          hsame homObject homObject' ->
            hsame identity identity' ->
              hsame transport transport' ->
                hsame provenance provenance' ->
                  Cont homObject' identity' composition' ->
                    Cont transport' provenance' ledger' ->
                      Cont ledger' monoidalBoundary' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          EnrichedCatPublicPacket categoryBoundary' monoidalBoundary' homObject'
                              identity' composition' transport' provenance' ledger' endpoint'
                              bundle pkg ∧
                            hsame composition composition' ∧ hsame ledger ledger' ∧
                              hsame endpoint endpoint' := by
  intro packet sameCategory sameMonoidal sameHom sameIdentity sameTransport sameProvenance
    homIdentityCont' transportProvenanceCont' ledgerMonoidalCont' pkgSig'
  have sameComposition : hsame composition composition' :=
    cont_respects_hsame sameHom sameIdentity
      packet.right.right.right.right.right.right.right.left homIdentityCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTransport sameProvenance
      packet.right.right.right.right.right.right.right.right.left transportProvenanceCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameMonoidal
      packet.right.right.right.right.right.right.right.right.right.left ledgerMonoidalCont'
  have transported :
      EnrichedCatPublicPacket categoryBoundary' monoidalBoundary' homObject' identity'
          composition' transport' provenance' ledger' endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameCategory,
      unary_transport packet.right.left sameMonoidal,
      unary_transport packet.right.right.left sameHom,
      unary_transport packet.right.right.right.left sameIdentity,
      unary_cont_closed (unary_transport packet.right.right.left sameHom)
        (unary_transport packet.right.right.right.left sameIdentity) homIdentityCont',
      unary_transport packet.right.right.right.right.right.left sameTransport,
      unary_transport packet.right.right.right.right.right.right.left sameProvenance,
      homIdentityCont',
      transportProvenanceCont',
      ledgerMonoidalCont',
      pkgSig'⟩
  exact And.intro transported
    (And.intro sameComposition (And.intro sameLedger sameEndpoint))

theorem EnrichedCatPublicPacket_ledger_exactness_obligation [AskSetup] [PackageSetup]
    {categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatPublicPacket categoryBoundary monoidalBoundary homObject identity composition
        transport provenance ledger endpoint bundle pkg ->
      UnaryHistory homObject ∧ UnaryHistory identity ∧ UnaryHistory composition ∧
        UnaryHistory transport ∧ hsame composition (append homObject identity) ∧
          hsame ledger (append transport provenance) ∧
            hsame endpoint (append ledger monoidalBoundary) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have homUnary : UnaryHistory homObject :=
    packet.right.right.left
  have identityUnary : UnaryHistory identity :=
    packet.right.right.right.left
  have compositionUnary : UnaryHistory composition :=
    packet.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.left
  have compositionRow : Cont homObject identity composition :=
    packet.right.right.right.right.right.right.right.left
  have ledgerRow : Cont transport provenance ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont ledger monoidalBoundary endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  exact And.intro homUnary
    (And.intro identityUnary
      (And.intro compositionUnary
        (And.intro transportUnary
          (And.intro compositionRow
            (And.intro ledgerRow
              (And.intro endpointRow pkgSig))))))

theorem EnrichedCatPublicPacket_monoidal_category_boundary [AskSetup] [PackageSetup]
    {categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint tensorReadback consumerReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatPublicPacket categoryBoundary monoidalBoundary homObject identity composition
        transport provenance ledger endpoint bundle pkg ->
      Cont composition monoidalBoundary tensorReadback ->
        Cont endpoint tensorReadback consumerReadback ->
          UnaryHistory tensorReadback ∧ UnaryHistory consumerReadback ∧
            hsame tensorReadback (append composition monoidalBoundary) ∧
              hsame consumerReadback (append endpoint tensorReadback) ∧
                hsame endpoint (append ledger monoidalBoundary) ∧
                  PkgSig bundle endpoint pkg := by
  intro packet tensorReadbackRow consumerReadbackRow
  have compositionUnary : UnaryHistory composition :=
    packet.right.right.right.right.left
  have monoidalUnary : UnaryHistory monoidalBoundary :=
    packet.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed transportUnary provenanceUnary
      packet.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary monoidalUnary
      packet.right.right.right.right.right.right.right.right.right.left
  have tensorReadbackUnary : UnaryHistory tensorReadback :=
    unary_cont_closed compositionUnary monoidalUnary tensorReadbackRow
  have consumerReadbackUnary : UnaryHistory consumerReadback :=
    unary_cont_closed endpointUnary tensorReadbackUnary consumerReadbackRow
  exact And.intro tensorReadbackUnary
    (And.intro consumerReadbackUnary
      (And.intro tensorReadbackRow
        (And.intro consumerReadbackRow
          (And.intro packet.right.right.right.right.right.right.right.right.right.left
            packet.right.right.right.right.right.right.right.right.right.right))))

theorem EnrichedCatSourceSurface_consumer_readback_boundary [AskSetup] [PackageSetup]
    {category monoidal hom identity composition transport provenance ledger endpoint consumer
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatSourceSurface category monoidal hom identity composition transport provenance
        ledger endpoint bundle pkg ->
      UnaryHistory consumer ->
        Cont endpoint consumer readback ->
          UnaryHistory readback ∧ hsame readback (append endpoint consumer) ∧
            PkgSig bundle endpoint pkg := by
  intro surface consumerUnary readbackRow
  have source := EnrichedCatSourceSurface_source_obligation surface
  have endpointUnary : UnaryHistory endpoint :=
    source.right.right.right.right.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed endpointUnary consumerUnary readbackRow
  exact And.intro readbackUnary
    (And.intro readbackRow
      source.right.right.right.right.right.right.right.right.right.right.right)

theorem EnrichedCatSourceSurface_tensor_composition_scope [AskSetup] [PackageSetup]
    {category monoidal hom identity composition transport provenance ledger endpoint
      tensorReadback consumerReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatSourceSurface category monoidal hom identity composition transport provenance
        ledger endpoint bundle pkg ->
      Cont composition monoidal tensorReadback ->
        Cont endpoint tensorReadback consumerReadback ->
          UnaryHistory composition ∧ UnaryHistory tensorReadback ∧
            UnaryHistory consumerReadback ∧ Cont hom identity composition ∧
              Cont composition monoidal tensorReadback ∧
                Cont endpoint tensorReadback consumerReadback ∧
                  hsame ledger (append composition transport) ∧
                    PkgSig bundle endpoint pkg := by
  intro surface tensorReadbackRow consumerReadbackRow
  have source := EnrichedCatSourceSurface_source_obligation surface
  have compositionUnary : UnaryHistory composition :=
    source.right.right.right.right.left
  have monoidalUnary : UnaryHistory monoidal :=
    source.right.left
  have endpointUnary : UnaryHistory endpoint :=
    source.right.right.right.right.right.right.left
  have tensorReadbackUnary : UnaryHistory tensorReadback :=
    unary_cont_closed compositionUnary monoidalUnary tensorReadbackRow
  have consumerReadbackUnary : UnaryHistory consumerReadback :=
    unary_cont_closed endpointUnary tensorReadbackUnary consumerReadbackRow
  exact And.intro compositionUnary
    (And.intro tensorReadbackUnary
      (And.intro consumerReadbackUnary
        (And.intro source.right.right.right.right.right.right.right.left
          (And.intro tensorReadbackRow
            (And.intro consumerReadbackRow
              (And.intro source.right.right.right.right.right.right.right.right.right.left
                source.right.right.right.right.right.right.right.right.right.right.right))))))

end BEDC.Derived.EnrichedCatUp
