import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

theorem TypeLevelSocketExposureLedgerHostReturnExclusion [AskSetup] [PackageSetup]
    {setup carrier classifier ledger refusal transport route provenance name exposureRead
      refusalRead ledgerRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
        provenance name bundle pkg →
      Cont setup carrier exposureRead →
        Cont classifier ledger refusalRead →
          Cont ledger refusal ledgerRead →
            PkgSig bundle ledgerRead pkg →
              UnaryHistory exposureRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory ledgerRead ∧ PkgSig bundle ledgerRead pkg ∧
                  (Cont ledgerRead (BHist.e0 hostTail) ledger → False) ∧
                    (Cont ledgerRead (BHist.e1 hostTail) ledger → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro exposureWitness setupCarrierExposure classifierLedgerRefusal ledgerRefusalRead
    ledgerReadPkg
  obtain ⟨setupUnary, carrierUnary, classifierUnary, ledgerUnary, refusalUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _setupCarrierClassifier,
    _classifierLedgerRefusal, _refusalTransportRoute, _namePkg⟩ := exposureWitness
  have exposureReadUnary : UnaryHistory exposureRead :=
    unary_cont_closed setupUnary carrierUnary setupCarrierExposure
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed classifierUnary ledgerUnary classifierLedgerRefusal
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary refusalUnary ledgerRefusalRead
  exact
    ⟨exposureReadUnary, refusalReadUnary, ledgerReadUnary, ledgerReadPkg,
      cont_mutual_extension_right_tail_absurd.left ledgerRefusalRead,
      cont_mutual_extension_right_tail_absurd.right ledgerRefusalRead⟩

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

theorem TypeLevelSocketExposureRefusalExactness [AskSetup] [PackageSetup]
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
                  SemanticNameCert
                      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row setup ∨ hsame row carrier ∨ hsame row classifier ∨
                          hsame row ledger ∨ hsame row refusal ∨ hsame row refusalRead ∨
                            hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont setup carrier exposureRead ∧
                          Cont classifier ledger refusalRead ∧ Cont route name certRead ∧
                            Cont certRead provenance consumerRead ∧
                              PkgSig bundle consumerRead pkg)
                      hsame ∧
                    UnaryHistory refusalRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro exposureWitness setupCarrierExposure classifierLedgerRefusal routeNameCert
    certProvenanceConsumer _certPkg consumerPkg
  obtain ⟨setupUnary, carrierUnary, classifierUnary, ledgerUnary, _refusalUnary,
    _transportUnary, routeUnary, provenanceUnary, nameUnary, _setupCarrierClassifier,
    _classifierLedgerRefusal, _refusalTransportRoute, _namePkg⟩ := exposureWitness
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed classifierUnary ledgerUnary classifierLedgerRefusal
  have certReadUnary : UnaryHistory certRead :=
    unary_cont_closed routeUnary nameUnary routeNameCert
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed certReadUnary provenanceUnary certProvenanceConsumer
  have sourceRefusal :
      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row) refusalRead := by
    exact ⟨hsame_refl refusalRead, refusalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row setup ∨ hsame row carrier ∨ hsame row classifier ∨
              hsame row ledger ∨ hsame row refusal ∨ hsame row refusalRead ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont setup carrier exposureRead ∧
              Cont classifier ledger refusalRead ∧ Cont route name certRead ∧
                Cont certRead provenance consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, setupCarrierExposure, classifierLedgerRefusal, routeNameCert,
          certProvenanceConsumer, consumerPkg⟩
  }
  exact ⟨cert, refusalReadUnary, consumerReadUnary⟩

theorem TypeLevelSocketExposureScopeExactness [AskSetup] [PackageSetup]
    {setup carrier classifier ledger refusal transport route provenance name exposureRead
      refusalRead certRead consumerRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
        provenance name bundle pkg ->
      Cont setup carrier exposureRead ->
        Cont classifier ledger refusalRead ->
          Cont route name certRead ->
            Cont certRead provenance consumerRead ->
              Cont consumerRead transport scopeRead ->
                PkgSig bundle certRead pkg ->
                  PkgSig bundle consumerRead pkg ->
                    PkgSig bundle scopeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row setup ∨ hsame row carrier ∨ hsame row classifier ∨
                              hsame row ledger ∨ hsame row refusal ∨ hsame row transport ∨
                                hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                                  hsame row scopeRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont setup carrier exposureRead ∧
                              Cont classifier ledger refusalRead ∧ Cont route name certRead ∧
                                Cont certRead provenance consumerRead ∧
                                  Cont consumerRead transport scopeRead ∧
                                    PkgSig bundle scopeRead pkg)
                          hsame ∧
                        UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: TypeLevelSocketExposureCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro exposureWitness setupCarrierExposure classifierLedgerRefusal routeNameCert
    certProvenanceConsumer consumerTransportScope _certPkg _consumerPkg scopePkg
  obtain ⟨setupUnary, carrierUnary, classifierUnary, ledgerUnary, _refusalUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, _setupCarrierClassifier,
    _classifierLedgerRefusal, _refusalTransportRoute, _namePkg⟩ := exposureWitness
  have certReadUnary : UnaryHistory certRead :=
    unary_cont_closed routeUnary nameUnary routeNameCert
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed certReadUnary provenanceUnary certProvenanceConsumer
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed consumerReadUnary transportUnary consumerTransportScope
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row setup ∨ hsame row carrier ∨ hsame row classifier ∨
              hsame row ledger ∨ hsame row refusal ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont setup carrier exposureRead ∧
              Cont classifier ledger refusalRead ∧ Cont route name certRead ∧
                Cont certRead provenance consumerRead ∧
                  Cont consumerRead transport scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeReadUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, setupCarrierExposure, classifierLedgerRefusal, routeNameCert,
          certProvenanceConsumer, consumerTransportScope, scopePkg⟩
  }
  exact ⟨cert, scopeReadUnary⟩

theorem TypeLevelSocketExposureKernelGrounding [AskSetup] [PackageSetup]
    {setup carrier classifier ledger refusal transport route provenance name exposureRead
      refusalRead certRead consumerRead scopeRead kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypeLevelSocketExposureCarrier setup carrier classifier ledger refusal transport route
        provenance name bundle pkg ->
      Cont setup carrier exposureRead ->
        Cont classifier ledger refusalRead ->
          Cont route name certRead ->
            Cont certRead provenance consumerRead ->
              Cont consumerRead transport scopeRead ->
                Cont scopeRead route kernelRead ->
                  PkgSig bundle scopeRead pkg ->
                    PkgSig bundle kernelRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row setup ∨ hsame row carrier ∨ hsame row classifier ∨
                              hsame row ledger ∨ hsame row refusal ∨ hsame row transport ∨
                                hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                                  hsame row kernelRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont setup carrier exposureRead ∧
                              Cont classifier ledger refusalRead ∧ Cont route name certRead ∧
                                Cont certRead provenance consumerRead ∧
                                  Cont consumerRead transport scopeRead ∧
                                    Cont scopeRead route kernelRead ∧
                                      PkgSig bundle kernelRead pkg)
                          hsame ∧
                        UnaryHistory kernelRead := by
  -- BEDC touchpoint anchor: TypeLevelSocketExposureCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro exposureWitness setupCarrierExposure classifierLedgerRefusal routeNameCert
    certProvenanceConsumer consumerTransportScope scopeRouteKernel _scopePkg kernelPkg
  obtain ⟨setupUnary, carrierUnary, classifierUnary, ledgerUnary, _refusalUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, _setupCarrierClassifier,
    _classifierLedgerRefusal, _refusalTransportRoute, _namePkg⟩ := exposureWitness
  have certReadUnary : UnaryHistory certRead :=
    unary_cont_closed routeUnary nameUnary routeNameCert
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed certReadUnary provenanceUnary certProvenanceConsumer
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed consumerReadUnary transportUnary consumerTransportScope
  have kernelReadUnary : UnaryHistory kernelRead :=
    unary_cont_closed scopeReadUnary routeUnary scopeRouteKernel
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row setup ∨ hsame row carrier ∨ hsame row classifier ∨
              hsame row ledger ∨ hsame row refusal ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row kernelRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont setup carrier exposureRead ∧
              Cont classifier ledger refusalRead ∧ Cont route name certRead ∧
                Cont certRead provenance consumerRead ∧
                  Cont consumerRead transport scopeRead ∧ Cont scopeRead route kernelRead ∧
                    PkgSig bundle kernelRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro kernelRead ⟨hsame_refl kernelRead, kernelReadUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, setupCarrierExposure, classifierLedgerRefusal, routeNameCert,
          certProvenanceConsumer, consumerTransportScope, scopeRouteKernel, kernelPkg⟩
  }
  exact ⟨cert, kernelReadUnary⟩

end BEDC.Derived.TypeLevelSocketExposureUp
