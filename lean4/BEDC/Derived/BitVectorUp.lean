import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BitVectorPacket [AskSetup] [PackageSetup]
    (length spine ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont length spine ledger ∧
    Cont ledger provenance endpoint ∧
      PkgSig bundle endpoint pkg

theorem BitVectorPacket_carrier_transport [AskSetup] [PackageSetup]
    {length length' spine spine' ledger ledger' provenance provenance' endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame length length' ->
      hsame spine spine' ->
        hsame ledger ledger' ->
          hsame provenance provenance' ->
            BitVectorPacket length spine ledger provenance endpoint bundle pkg ->
              BitVectorPacket length' spine' ledger' provenance' endpoint bundle pkg := by
  intro sameLength sameSpine sameLedger sameProvenance packet
  exact And.intro
    (cont_hsame_transport sameLength sameSpine sameLedger packet.left)
    (And.intro
      (cont_hsame_transport sameLedger sameProvenance (hsame_refl endpoint) packet.right.left)
      packet.right.right)

def BitVectorSourceClassifier
    (length spine ledger provenance length' spine' ledger' provenance' : BHist) : Prop :=
  hsame length length' ∧ hsame spine spine' ∧ hsame ledger ledger' ∧
    hsame provenance provenance'

theorem BitVectorSourceClassifier_laws :
    (∀ {n s l p : BHist}, Cont n s l -> hsame p p ->
      BitVectorSourceClassifier n s l p n s l p) ∧
      (∀ {n s l p n' s' l' p' : BHist},
        BitVectorSourceClassifier n s l p n' s' l' p' ->
          BitVectorSourceClassifier n' s' l' p' n s l p) ∧
        (∀ {n s l p n' s' l' p' n'' s'' l'' p'' : BHist},
          BitVectorSourceClassifier n s l p n' s' l' p' ->
            BitVectorSourceClassifier n' s' l' p' n'' s'' l'' p'' ->
              BitVectorSourceClassifier n s l p n'' s'' l'' p'') := by
  constructor
  · intro n s l p _route sameProvenance
    constructor
    · exact hsame_refl n
    · constructor
      · exact hsame_refl s
      · constructor
        · exact hsame_refl l
        · exact sameProvenance
  · constructor
    · intro n s l p n' s' l' p' classified
      cases classified with
      | intro sameLength rest =>
          cases rest with
          | intro sameSpine rest =>
              cases rest with
              | intro sameLedger sameProvenance =>
                  constructor
                  · exact hsame_symm sameLength
                  · constructor
                    · exact hsame_symm sameSpine
                    · constructor
                      · exact hsame_symm sameLedger
                      · exact hsame_symm sameProvenance
    · intro n s l p n' s' l' p' n'' s'' l'' p'' left right
      cases left with
      | intro sameLengthLeft leftRest =>
          cases leftRest with
          | intro sameSpineLeft leftRest =>
              cases leftRest with
              | intro sameLedgerLeft sameProvenanceLeft =>
                  cases right with
                  | intro sameLengthRight rightRest =>
                      cases rightRest with
                      | intro sameSpineRight rightRest =>
                          cases rightRest with
                          | intro sameLedgerRight sameProvenanceRight =>
                              constructor
                              · exact hsame_trans sameLengthLeft sameLengthRight
                              · constructor
                                · exact hsame_trans sameSpineLeft sameSpineRight
                                · constructor
                                  · exact hsame_trans sameLedgerLeft sameLedgerRight
                                  · exact hsame_trans sameProvenanceLeft sameProvenanceRight

def BitVectorBHistSource [AskSetup] [PackageSetup]
    (length spine ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
    Cont length spine endpoint ∧ Cont endpoint ledger provenance ∧ PkgSig bundle provenance pkg

theorem BitVectorBHistSource_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance endpoint length' spine' ledger' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorBHistSource length spine ledger provenance endpoint bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame ledger ledger' ->
            hsame provenance provenance' ->
              Cont length' spine' endpoint' ->
                Cont endpoint' ledger' provenance' ->
                  PkgSig bundle provenance' pkg ->
                    BitVectorBHistSource length' spine' ledger' provenance' endpoint' bundle pkg ∧
                      hsame endpoint endpoint' ∧ hsame provenance provenance' := by
  intro source sameLength sameSpine sameLedger sameProvenance endpointRoute provenanceRoute pkgRoute
  obtain ⟨lengthUnary, spineUnary, ledgerUnary, provenanceUnary, endpointSource,
    provenanceSource, _pkgSource⟩ := source
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameLength sameSpine endpointSource endpointRoute
  have provenanceSameFromRoutes : hsame provenance provenance' :=
    cont_respects_hsame endpointSame sameLedger provenanceSource provenanceRoute
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨lengthUnary', spineUnary', ledgerUnary', provenanceUnary', endpointRoute, provenanceRoute,
        pkgRoute⟩,
      endpointSame, provenanceSameFromRoutes⟩

def BitVectorCarrier [AskSetup] [PackageSetup]
    (length spine ledger provenance payload : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧
    Cont length spine payload ∧ Cont payload ledger provenance ∧ PkgSig bundle provenance pkg

theorem BitVectorCarrier_hsame_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance payload length' spine' ledger' provenance' payload' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorCarrier length spine ledger provenance payload bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame ledger ledger' ->
            Cont length' spine' payload' ->
              Cont payload' ledger' provenance' ->
                PkgSig bundle provenance' pkg ->
                  BitVectorCarrier length' spine' ledger' provenance' payload' bundle pkg ∧
                    hsame payload payload' ∧ hsame provenance provenance' := by
  intro carrier sameLength sameSpine sameLedger payloadRow' provenanceRow' pkgSig'
  have lengthUnary : UnaryHistory length :=
    carrier.left
  have spineUnary : UnaryHistory spine :=
    carrier.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.left
  have payloadRow : Cont length spine payload :=
    carrier.right.right.right.left
  have provenanceRow : Cont payload ledger provenance :=
    carrier.right.right.right.right.left
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have samePayload : hsame payload payload' :=
    cont_respects_hsame sameLength sameSpine payloadRow payloadRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame samePayload sameLedger provenanceRow provenanceRow'
  exact And.intro
    (And.intro lengthUnary'
      (And.intro spineUnary'
        (And.intro ledgerUnary'
          (And.intro payloadRow'
            (And.intro provenanceRow' pkgSig')))))
    (And.intro samePayload sameProvenance)

def BitVectorCarrierPacket [AskSetup] [PackageSetup]
    (length spine ledger provenance lengthSpineRoute : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
    Cont length spine lengthSpineRoute ∧ Cont lengthSpineRoute ledger provenance ∧
      PkgSig bundle provenance pkg

theorem BitVectorSourcePacket_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance lengthSpineRoute length' spine' ledger' provenance'
      lengthSpineRoute' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorCarrierPacket length spine ledger provenance lengthSpineRoute bundle pkg ->
      hsame length length' -> hsame spine spine' -> hsame ledger ledger' ->
        Cont length' spine' lengthSpineRoute' ->
          Cont lengthSpineRoute' ledger' provenance' ->
            PkgSig bundle provenance' pkg ->
              BitVectorCarrierPacket length' spine' ledger' provenance' lengthSpineRoute'
                  bundle pkg ∧
                hsame lengthSpineRoute lengthSpineRoute' ∧ hsame provenance provenance' := by
  intro packet sameLength sameSpine sameLedger lengthSpineRow' provenanceRow' pkgSig'
  have lengthSpineRow : Cont length spine lengthSpineRoute :=
    packet.right.right.right.right.left
  have provenanceRow : Cont lengthSpineRoute ledger provenance :=
    packet.right.right.right.right.right.left
  have sameLengthSpineRoute : hsame lengthSpineRoute lengthSpineRoute' :=
    cont_respects_hsame sameLength sameSpine lengthSpineRow lengthSpineRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLengthSpineRoute sameLedger provenanceRow provenanceRow'
  have transported :
      BitVectorCarrierPacket length' spine' ledger' provenance' lengthSpineRoute' bundle pkg :=
    ⟨unary_transport packet.left sameLength,
      unary_transport packet.right.left sameSpine,
      unary_transport packet.right.right.left sameLedger,
      unary_transport packet.right.right.right.left sameProvenance,
      lengthSpineRow',
      provenanceRow',
      pkgSig'⟩
  exact And.intro transported
    (And.intro sameLengthSpineRoute sameProvenance)

def BitVectorSource [AskSetup] [PackageSetup]
    (length spine ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧
    UnaryHistory provenance ∧ Cont length spine ledger ∧ PkgSig bundle provenance pkg

theorem BitVectorSource_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance length' spine' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorSource length spine ledger provenance bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame provenance provenance' ->
            Cont length' spine' ledger' ->
              PkgSig bundle provenance' pkg ->
                BitVectorSource length' spine' ledger' provenance' bundle pkg ∧
                  hsame ledger ledger' := by
  intro source sameLength sameSpine sameProvenance ledgerRow' pkgSig'
  cases source with
  | intro lengthUnary sourceRest =>
      cases sourceRest with
      | intro spineUnary sourceRest =>
          cases sourceRest with
          | intro _ledgerUnary sourceRest =>
              cases sourceRest with
              | intro provenanceUnary sourceRest =>
                  cases sourceRest with
                  | intro ledgerRow _pkgSig =>
                      have lengthUnary' : UnaryHistory length' :=
                        unary_transport lengthUnary sameLength
                      have spineUnary' : UnaryHistory spine' :=
                        unary_transport spineUnary sameSpine
                      have provenanceUnary' : UnaryHistory provenance' :=
                        unary_transport provenanceUnary sameProvenance
                      have ledgerUnary' : UnaryHistory ledger' :=
                        unary_repetition_closed_under_continuation lengthUnary' spineUnary'
                          ledgerRow'
                      have sameLedger : hsame ledger ledger' :=
                        cont_respects_hsame sameLength sameSpine ledgerRow ledgerRow'
                      constructor
                      · exact ⟨lengthUnary', spineUnary', ledgerUnary', provenanceUnary',
                          ledgerRow', pkgSig'⟩
                      · exact sameLedger

def BitVectorFiniteLedger [AskSetup] [PackageSetup]
    (length spine ledger provenance read : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory provenance ∧
    Cont length spine ledger ∧ Cont ledger provenance read ∧ PkgSig bundle read pkg

theorem BitVectorFiniteLedger_ledger_coverage [AskSetup] [PackageSetup]
    {length spine ledger provenance read : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorFiniteLedger length spine ledger provenance read bundle pkg ->
      UnaryHistory ledger ∧ UnaryHistory read ∧ hsame ledger (append length spine) ∧
        hsame read (append ledger provenance) ∧ PkgSig bundle read pkg := by
  intro finiteLedger
  have lengthUnary : UnaryHistory length :=
    finiteLedger.left
  have spineUnary : UnaryHistory spine :=
    finiteLedger.right.left
  have provenanceUnary : UnaryHistory provenance :=
    finiteLedger.right.right.left
  have ledgerRow : Cont length spine ledger :=
    finiteLedger.right.right.right.left
  have readRow : Cont ledger provenance read :=
    finiteLedger.right.right.right.right.left
  have pkgSig : PkgSig bundle read pkg :=
    finiteLedger.right.right.right.right.right
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed lengthUnary spineUnary ledgerRow
  have readUnary : UnaryHistory read :=
    unary_cont_closed ledgerUnary provenanceUnary readRow
  exact And.intro ledgerUnary
    (And.intro readUnary
      (And.intro ledgerRow
        (And.intro readRow pkgSig)))

theorem BitVectorFiniteLedger_public_finite_algebra_export [AskSetup] [PackageSetup]
    {length spine ledger provenance read consumer exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorFiniteLedger length spine ledger provenance read bundle pkg ->
      UnaryHistory consumer ->
        Cont read consumer exported ->
          PkgSig bundle exported pkg ->
            UnaryHistory exported ∧ hsame exported (append read consumer) ∧
              PkgSig bundle exported pkg ∧ hsame ledger (append length spine) ∧
                hsame read (append ledger provenance) := by
  intro finiteLedger consumerUnary exportRow pkgExport
  obtain ⟨_ledgerUnary, readUnary, ledgerRow, readRow, _pkgRead⟩ :=
    BitVectorFiniteLedger_ledger_coverage finiteLedger
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed readUnary consumerUnary exportRow
  exact
    ⟨exportedUnary, exportRow, pkgExport, ledgerRow, readRow⟩

theorem BitVectorFiniteLedger_semantic_name_certificate [AskSetup] [PackageSetup]
    {length spine ledger provenance read : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorFiniteLedger length spine ledger provenance read bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row read ∧
          BitVectorFiniteLedger length spine ledger provenance row bundle pkg)
        (fun row : BHist => UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧
          UnaryHistory row ∧ hsame ledger (append length spine))
        (fun row : BHist => PkgSig bundle row pkg ∧ hsame row (append ledger provenance))
        hsame := by
  intro finiteLedger
  exact {
    core := {
      carrier_inhabited := Exists.intro read ⟨hsame_refl read, finiteLedger⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨lengthUnary, spineUnary, provenanceUnary, ledgerRow, readRow, _pkgSig⟩ :=
        sourceRow.right
      have ledgerUnary : UnaryHistory ledger :=
        unary_cont_closed lengthUnary spineUnary ledgerRow
      have rowUnary : UnaryHistory _row :=
        unary_cont_closed ledgerUnary provenanceUnary readRow
      exact ⟨lengthUnary, spineUnary, ledgerUnary, rowUnary, ledgerRow⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_lengthUnary, _spineUnary, _provenanceUnary, _ledgerRow, readRow, pkgSig⟩ :=
        sourceRow.right
      exact ⟨pkgSig, readRow⟩
  }

theorem BitVectorFiniteLedger_public_export_transport [AskSetup] [PackageSetup]
    {length spine ledger provenance read length' spine' ledger' provenance' read' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorFiniteLedger length spine ledger provenance read bundle pkg ->
      hsame length length' -> hsame spine spine' -> hsame provenance provenance' ->
        Cont length' spine' ledger' -> Cont ledger' provenance' read' ->
          PkgSig bundle read' pkg ->
            BitVectorFiniteLedger length' spine' ledger' provenance' read' bundle pkg ∧
              hsame ledger ledger' ∧ hsame read read' := by
  intro finiteLedger sameLength sameSpine sameProvenance ledgerRow' readRow' pkgSig'
  obtain ⟨lengthUnary, spineUnary, provenanceUnary, ledgerRow, readRow, _pkgSig⟩ :=
    finiteLedger
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLength sameSpine ledgerRow ledgerRow'
  have sameRead : hsame read read' :=
    cont_respects_hsame sameLedger sameProvenance readRow readRow'
  have transported :
      BitVectorFiniteLedger length' spine' ledger' provenance' read' bundle pkg :=
    ⟨unary_transport lengthUnary sameLength,
      unary_transport spineUnary sameSpine,
      unary_transport provenanceUnary sameProvenance,
      ledgerRow',
      readRow',
      pkgSig'⟩
  exact ⟨transported, sameLedger, sameRead⟩

theorem BitVectorFiniteLedger_finite_data_anchor [AskSetup] [PackageSetup]
    {length spine ledger provenance read consumerTail exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorFiniteLedger length spine ledger provenance read bundle pkg ->
      UnaryHistory consumerTail ->
        Cont read consumerTail exported ->
          Cont length spine ledger ∧ Cont ledger provenance read ∧
            Cont read consumerTail exported ∧ UnaryHistory ledger ∧ UnaryHistory read ∧
              UnaryHistory exported ∧ hsame exported (append read consumerTail) ∧
                PkgSig bundle read pkg := by
  intro finiteLedger consumerTailUnary exportedRow
  have lengthUnary : UnaryHistory length :=
    finiteLedger.left
  have spineUnary : UnaryHistory spine :=
    finiteLedger.right.left
  have provenanceUnary : UnaryHistory provenance :=
    finiteLedger.right.right.left
  have ledgerRow : Cont length spine ledger :=
    finiteLedger.right.right.right.left
  have readRow : Cont ledger provenance read :=
    finiteLedger.right.right.right.right.left
  have pkgSig : PkgSig bundle read pkg :=
    finiteLedger.right.right.right.right.right
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed lengthUnary spineUnary ledgerRow
  have readUnary : UnaryHistory read :=
    unary_cont_closed ledgerUnary provenanceUnary readRow
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed readUnary consumerTailUnary exportedRow
  exact
    ⟨ledgerRow, readRow, exportedRow, ledgerUnary, readUnary, exportedUnary, exportedRow,
      pkgSig⟩

def BitVectorSourcePacket [AskSetup] [PackageSetup]
    (n spine ledger route provenance source : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory n ∧ UnaryHistory spine ∧ UnaryHistory route ∧ Cont n spine ledger ∧
    Cont ledger route provenance ∧ PkgSig bundle source pkg

theorem BitVectorSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {n spine ledger route provenance source : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    BitVectorSourcePacket n spine ledger route provenance source bundle pkg ->
      UnaryHistory n ∧ UnaryHistory spine ∧ Cont n spine ledger ∧
        Cont ledger route provenance ∧ hsame ledger (append n spine) ∧
          hsame provenance (append ledger route) ∧ PkgSig bundle source pkg := by
  intro packet
  obtain ⟨nUnary, spineUnary, _routeUnary, ledgerRow, provenanceRow, pkgRow⟩ := packet
  exact ⟨nUnary, spineUnary, ledgerRow, provenanceRow, ledgerRow, provenanceRow, pkgRow⟩

theorem BitVectorSourcePacket_finite_data_anchor [AskSetup] [PackageSetup]
    {n spine ledger route provenance source : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    BitVectorSourcePacket n spine ledger route provenance source bundle pkg ->
      UnaryHistory n ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
        Cont n spine ledger ∧ Cont ledger route provenance ∧ hsame ledger (append n spine) ∧
          hsame provenance (append ledger route) ∧ PkgSig bundle source pkg := by
  intro packet
  obtain ⟨nUnary, spineUnary, routeUnary, ledgerRow, provenanceRow, pkgRow⟩ := packet
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed nUnary spineUnary ledgerRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary routeUnary provenanceRow
  exact
    ⟨nUnary, spineUnary, ledgerUnary, provenanceUnary, ledgerRow, provenanceRow,
      ledgerRow, provenanceRow, pkgRow⟩

theorem BitVectorSourcePacket_fixed_length_consumer_determinacy [AskSetup] [PackageSetup]
    {n spine ledger route provenance source n' spine' ledger' route' provenance' source' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorSourcePacket n spine ledger route provenance source bundle pkg ->
      BitVectorSourcePacket n' spine' ledger' route' provenance' source' bundle pkg ->
        hsame n n' ->
          hsame spine spine' ->
            hsame route route' ->
              hsame ledger ledger' ∧ hsame provenance provenance' := by
  intro packet packet' sameLength sameSpine sameRoute
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLength sameSpine
      packet.right.right.right.left
      packet'.right.right.right.left
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameRoute
      packet.right.right.right.right.left
      packet'.right.right.right.right.left
  exact ⟨sameLedger, sameProvenance⟩

theorem BitVectorSource_semantic_name_certificate [AskSetup] [PackageSetup]
    {length spine ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorSource length spine ledger provenance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧ BitVectorSource length spine ledger row bundle pkg)
        (fun row : BHist => UnaryHistory row ∧ Cont length spine ledger)
        (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory ledger)
        (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := by
  intro source
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, source⟩
      equiv_refl := by
        intro row sourceRow
        obtain ⟨_lengthUnary, _spineUnary, _ledgerUnary, _rowUnary, _ledgerRow,
          pkgRow⟩ := sourceRow.right
        exact ⟨PkgSig_psame_intro pkgRow pkgRow (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨_lengthUnary, _spineUnary, _ledgerUnary, rowUnary, ledgerRow, _pkgRow⟩ :=
        sourceRow.right
      exact ⟨rowUnary, ledgerRow⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_lengthUnary, _spineUnary, ledgerUnary, _rowUnary, _ledgerRow, pkgRow⟩ :=
        sourceRow.right
      exact ⟨pkgRow, ledgerUnary⟩
  }

def BitVectorBoolSpineLedger [AskSetup] [PackageSetup]
    (width spine componentLedger route provenance consumer : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory width ∧ UnaryHistory spine ∧ UnaryHistory componentLedger ∧
    Cont width spine route ∧ Cont route componentLedger provenance ∧
      Cont provenance spine consumer ∧ PkgSig bundle provenance pkg

theorem BitVectorBoolSpineLedger_fixed_length_consumer_determinacy
    [AskSetup] [PackageSetup]
    {width spine componentLedger route provenance consumer width' spine' componentLedger'
      route' provenance' consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorBoolSpineLedger width spine componentLedger route provenance consumer bundle pkg ->
      BitVectorBoolSpineLedger width' spine' componentLedger' route' provenance' consumer'
          bundle pkg ->
        hsame width width' ->
          hsame spine spine' ->
            hsame componentLedger componentLedger' ->
              hsame route route' ∧ hsame provenance provenance' ∧
                hsame consumer consumer' := by
  intro left right sameWidth sameSpine sameComponentLedger
  obtain ⟨_widthUnary, _spineUnary, _componentUnary, leftRouteRow, leftProvenanceRow,
    leftConsumerRow, _leftPkgRow⟩ := left
  obtain ⟨_widthUnary', _spineUnary', _componentUnary', rightRouteRow, rightProvenanceRow,
    rightConsumerRow, _rightPkgRow⟩ := right
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameWidth sameSpine leftRouteRow rightRouteRow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRoute sameComponentLedger leftProvenanceRow rightProvenanceRow
  have sameConsumer : hsame consumer consumer' :=
    cont_respects_hsame sameProvenance sameSpine leftConsumerRow rightConsumerRow
  exact ⟨sameRoute, sameProvenance, sameConsumer⟩

theorem BitVectorSource_fixed_width_consumer_completeness [AskSetup] [PackageSetup]
    {length spine ledger provenance read : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    BitVectorSource length spine ledger provenance bundle pkg ->
      BitVectorFiniteLedger length spine ledger provenance read bundle pkg ->
        SemanticNameCert
            (fun row : BHist =>
              hsame row provenance ∧ BitVectorSource length spine ledger row bundle pkg)
            (fun row : BHist => UnaryHistory row ∧ Cont length spine ledger)
            (fun row : BHist => PkgSig bundle row pkg ∧ UnaryHistory ledger)
            (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') ∧
          UnaryHistory ledger ∧ UnaryHistory read ∧ hsame ledger (append length spine) ∧
            hsame read (append ledger provenance) ∧ PkgSig bundle read pkg := by
  intro source finiteLedger
  exact And.intro
    (BitVectorSource_semantic_name_certificate source)
    (BitVectorFiniteLedger_ledger_coverage finiteLedger)

end BEDC.Derived.BitVectorUp
