import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.TypeLevelSocketExposureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TypeLevelSocketExposureCarrier [AskSetup] [PackageSetup]
    (setup carrier classifier ledger refusal transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory setup ∧ UnaryHistory carrier ∧ UnaryHistory classifier ∧
    UnaryHistory ledger ∧ UnaryHistory refusal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont setup carrier classifier ∧ Cont classifier ledger refusal ∧
          Cont refusal transport route ∧ PkgSig bundle name pkg

theorem TypeLevelSocketExposureNamecertObligations [AskSetup] [PackageSetup]
    {setup carrier classifier ledger refusal transport route provenance name exposureRead
      refusalRead certRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
        provenance name bundle pkg ->
      Cont setup carrier exposureRead ->
        Cont classifier ledger refusalRead ->
          Cont route name certRead ->
            PkgSig bundle certRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal
                      transport route provenance name bundle pkg ∧
                    (hsame row exposureRead ∨ hsame row refusalRead ∨ hsame row certRead))
                (fun _row : BHist =>
                  Cont setup carrier exposureRead ∧ Cont classifier ledger refusalRead ∧
                    Cont route name certRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle certRead pkg)
                hsame ∧
                UnaryHistory exposureRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory certRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro exposureWitness setupCarrierExposure classifierLedgerRefusal routeNameCert certPkg
  have carrierInhabited :
      Exists
        (fun row : BHist =>
          TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
              provenance name bundle pkg ∧
            (hsame row exposureRead ∨ hsame row refusalRead ∨ hsame row certRead)) :=
    Exists.intro certRead ⟨exposureWitness, Or.inr (Or.inr (hsame_refl certRead))⟩
  obtain ⟨setupUnary, carrierUnary, classifierUnary, ledgerUnary, _refusalUnary,
    _transportUnary, routeUnary, _provenanceUnary, nameUnary, _setupCarrierClassifier,
    _classifierLedgerRefusal, _refusalTransportRoute, _namePkg⟩ := exposureWitness
  have exposureReadUnary : UnaryHistory exposureRead :=
    unary_cont_closed setupUnary carrierUnary setupCarrierExposure
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed classifierUnary ledgerUnary classifierLedgerRefusal
  have certReadUnary : UnaryHistory certRead :=
    unary_cont_closed routeUnary nameUnary routeNameCert
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
              provenance name bundle pkg ∧
            (hsame row exposureRead ∨ hsame row refusalRead ∨ hsame row certRead))
        (fun _row : BHist =>
          Cont setup carrier exposureRead ∧ Cont classifier ledger refusalRead ∧
            Cont route name certRead)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle certRead pkg)
        hsame := {
    core := {
      carrier_inhabited := carrierInhabited
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        cases source with
        | intro carrierSource sourceRead =>
            refine ⟨carrierSource, ?_⟩
            cases sourceRead with
            | inl sameExposure =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameExposure)
            | inr rest =>
                cases rest with
                | inl sameRefusal =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRefusal))
                | inr sameCert =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameCert))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨setupCarrierExposure, classifierLedgerRefusal, routeNameCert⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _carrierSource sourceRead =>
          cases sourceRead with
          | inl sameExposure =>
              exact ⟨unary_transport exposureReadUnary (hsame_symm sameExposure), certPkg⟩
          | inr rest =>
              cases rest with
              | inl sameRefusal =>
                  exact ⟨unary_transport refusalReadUnary (hsame_symm sameRefusal), certPkg⟩
              | inr sameCert =>
                  exact ⟨unary_transport certReadUnary (hsame_symm sameCert), certPkg⟩
  }
  exact ⟨cert, exposureReadUnary, refusalReadUnary, certReadUnary⟩

theorem TypeLevelSocketExposureLedgerNonescape [AskSetup] [PackageSetup]
    {setup carrier classifier ledger refusal transport route provenance name exposureRead
      refusalRead certRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
        provenance name bundle pkg →
      Cont setup carrier exposureRead →
        Cont classifier ledger refusalRead →
          Cont route name certRead →
            Cont certRead provenance consumerRead →
              PkgSig bundle certRead pkg →
                PkgSig bundle consumerRead pkg →
                  UnaryHistory exposureRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory certRead ∧ UnaryHistory consumerRead ∧
                      Cont setup carrier exposureRead ∧ Cont classifier ledger refusalRead ∧
                        Cont route name certRead ∧ Cont certRead provenance consumerRead ∧
                          PkgSig bundle certRead pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro exposureWitness setupCarrierExposure classifierLedgerRefusal routeNameCert
    certProvenanceConsumer certPkg consumerPkg
  have obligations :=
    TypeLevelSocketExposureNamecertObligations
      (setup := setup) (carrier := carrier) (classifier := classifier) (ledger := ledger)
      (refusal := refusal) (transport := transport) (route := route)
      (provenance := provenance) (name := name) (exposureRead := exposureRead)
      (refusalRead := refusalRead) (certRead := certRead) (bundle := bundle) (pkg := pkg)
      exposureWitness setupCarrierExposure classifierLedgerRefusal routeNameCert certPkg
  obtain ⟨_cert, exposureReadUnary, refusalReadUnary, certReadUnary⟩ := obligations
  obtain ⟨_setupUnary, _carrierUnary, _classifierUnary, _ledgerUnary, _refusalUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, _setupCarrierClassifier,
    _classifierLedgerRefusal, _refusalTransportRoute, _namePkg⟩ := exposureWitness
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed certReadUnary provenanceUnary certProvenanceConsumer
  exact
    ⟨exposureReadUnary, refusalReadUnary, certReadUnary, consumerReadUnary,
      setupCarrierExposure, classifierLedgerRefusal, routeNameCert, certProvenanceConsumer,
      certPkg, consumerPkg⟩

end BEDC.Derived.TypeLevelSocketExposureUp
