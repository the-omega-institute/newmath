import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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

def BitVectorSourcePacket [AskSetup] [PackageSetup]
    (n spine ledger route provenance source : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory n ∧ UnaryHistory spine ∧ UnaryHistory route ∧ Cont n spine ledger ∧
    Cont ledger route provenance ∧ PkgSig bundle source pkg

theorem BitVectorSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {n spine ledger route provenance source : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    BitVectorSourcePacket n spine ledger route provenance source bundle pkg →
      UnaryHistory n ∧ UnaryHistory spine ∧ Cont n spine ledger ∧
        Cont ledger route provenance ∧ hsame ledger (append n spine) ∧
          hsame provenance (append ledger route) ∧ PkgSig bundle source pkg := by
  intro packet
  obtain ⟨nUnary, spineUnary, _routeUnary, ledgerRow, provenanceRow, pkgRow⟩ := packet
  exact ⟨nUnary, spineUnary, ledgerRow, provenanceRow, ledgerRow, provenanceRow, pkgRow⟩

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

end BEDC.Derived.BitVectorUp
