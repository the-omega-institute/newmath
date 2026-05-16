import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HistTimeStreamCarrier [AskSetup] [PackageSetup]
    (source schedule start replay transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧ UnaryHistory replay ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      Cont schedule start replay ∧ Cont source replay provenance ∧
        hsame provenance replay ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem HistTimeStreamCarrier_namecert_obligation_sketch [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont schedule start replay →
        Cont source replay endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row endpoint)
                (fun row : BHist => hsame row replay)
                (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
                hsame ∧
              UnaryHistory endpoint ∧ Cont source replay endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier _scheduleReplay endpointRoute endpointPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary replayUnary endpointRoute
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic endpointRoute sourceReplayProvenance
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro carrierWitness (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row replay)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact hsame_trans sourceRow.right (hsame_trans endpointSameProvenance provenanceReplay)
      ledger_sound := by
        intro _row sourceRow
        exact And.intro (hsame_trans sourceRow.right endpointSameProvenance) endpointPkg
    }
  exact And.intro semantic (And.intro endpointUnary endpointRoute)

theorem HistTimeStreamCarrier_observation_carrier [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observation : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont source replay observation ->
        PkgSig bundle observation pkg ->
          UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
            UnaryHistory replay ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
              UnaryHistory name ∧ UnaryHistory observation ∧ Cont schedule start replay ∧
                Cont source replay observation ∧ hsame provenance replay ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle observation pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier sourceReplayObservation observationPkg
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary,
    provenanceUnary, nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    provenanceReplay, provenancePkg, namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sourceUnary replayUnary sourceReplayObservation
  exact
    ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, provenanceUnary,
      nameUnary, observationUnary, scheduleStartReplay, sourceReplayObservation,
      provenanceReplay, provenancePkg, namePkg, observationPkg⟩

theorem HistTimeStreamCarrier_schedule_classifier_stability [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont schedule start replay ->
        Cont source replay endpoint ->
          PkgSig bundle endpoint pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row endpoint)
                (fun row : BHist => Cont schedule start replay ∧ hsame row replay)
                (fun row : BHist => PkgSig bundle endpoint pkg ∧ hsame row provenance)
                hsame ∧
              UnaryHistory endpoint ∧ hsame endpoint provenance := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier scheduleReplay endpointRoute endpointPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary replayUnary endpointRoute
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic endpointRoute sourceReplayProvenance
  have endpointSameReplay : hsame endpoint replay :=
    hsame_trans endpointSameProvenance provenanceReplay
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro carrierWitness (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => Cont schedule start replay ∧ hsame row replay)
          (fun row : BHist => PkgSig bundle endpoint pkg ∧ hsame row provenance)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact And.intro scheduleReplay (hsame_trans sourceRow.right endpointSameReplay)
      ledger_sound := by
        intro _row sourceRow
        exact And.intro endpointPkg (hsame_trans sourceRow.right endpointSameProvenance)
    }
  exact And.intro semantic (And.intro endpointUnary endpointSameProvenance)

theorem HistTimeStreamCarrier_namecert_ledger_exhaustion [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont provenance name publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              HistTimeStreamCarrier source schedule start replay transport provenance name bundle
                pkg ∧ hsame row publicRead)
            (fun row : BHist =>
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
                UnaryHistory replay ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
                  UnaryHistory name ∧ UnaryHistory row)
            (fun _row : BHist =>
              Cont schedule start replay ∧ Cont source replay provenance ∧
                Cont provenance name publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier provenanceNamePublic publicPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, provenanceUnary,
    nameUnary, scheduleStartReplay, sourceReplayProvenance, _provenanceReplay, provenancePkg,
    namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNamePublic
  exact {
    core := {
      carrier_inhabited := Exists.intro publicRead
        (And.intro carrierWitness (hsame_refl publicRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro row sourceRow
      have rowUnary : UnaryHistory row :=
        unary_transport publicUnary (hsame_symm sourceRow.right)
      exact
        ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, provenanceUnary,
          nameUnary, rowUnary⟩
    ledger_sound := by
      intro _row _sourceRow
      exact
        ⟨scheduleStartReplay, sourceReplayProvenance, provenanceNamePublic, provenancePkg,
          namePkg, publicPkg⟩
  }

theorem HistTimeStreamCarrier_hsame_prefix_transport [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ->
      Cont schedule start replay ->
        Cont source replay endpoint ->
          hsame endpoint transported ->
            PkgSig bundle endpoint pkg ->
              PkgSig bundle transported pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      HistTimeStreamCarrier source schedule start replay transport provenance name
                        bundle pkg ∧ hsame row transported)
                    (fun row : BHist => Cont schedule start replay ∧ hsame row replay)
                    (fun row : BHist => hsame row endpoint ∧ PkgSig bundle transported pkg)
                    hsame ∧
                  UnaryHistory transported ∧ hsame transported provenance := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier scheduleReplay endpointRoute endpointTransported _endpointPkg transportedPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary replayUnary endpointRoute
  have transportedUnary : UnaryHistory transported :=
    unary_transport endpointUnary endpointTransported
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic endpointRoute sourceReplayProvenance
  have transportedSameProvenance : hsame transported provenance :=
    hsame_trans (hsame_symm endpointTransported) endpointSameProvenance
  have endpointSameReplay : hsame endpoint replay :=
    hsame_trans endpointSameProvenance provenanceReplay
  have transportedSameReplay : hsame transported replay :=
    hsame_trans (hsame_symm endpointTransported) endpointSameReplay
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row transported)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro transported
        (And.intro carrierWitness (hsame_refl transported))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row transported)
          (fun row : BHist => Cont schedule start replay ∧ hsame row replay)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle transported pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact And.intro scheduleReplay (hsame_trans sourceRow.right transportedSameReplay)
      ledger_sound := by
        intro _row sourceRow
        exact
          And.intro
            (hsame_trans sourceRow.right (hsame_symm endpointTransported))
            transportedPkg
    }
  exact And.intro semantic (And.intro transportedUnary transportedSameProvenance)

theorem HistTimeStreamCarrier_cont_replay_determinacy [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name prefixRow prefixRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont schedule start prefixRow →
        Cont schedule start prefixRow' →
          hsame prefixRow replay ∧ hsame prefixRow prefixRow' ∧ hsame prefixRow' replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame
  intro carrier prefixRoute prefixRoute'
  obtain ⟨_sourceUnary, _scheduleUnary, _startUnary, _replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  exact
    ⟨cont_deterministic prefixRoute scheduleStartReplay,
      cont_deterministic prefixRoute prefixRoute',
      cont_deterministic prefixRoute' scheduleStartReplay⟩

theorem HistTimeStreamObserverLocalityLatticeLink [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observation publicRead
      latticeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay observation →
        Cont provenance name publicRead →
          Cont observation publicRead latticeRead →
            PkgSig bundle latticeRead pkg →
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
                UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                  UnaryHistory observation ∧ UnaryHistory publicRead ∧
                    UnaryHistory latticeRead ∧ Cont schedule start replay ∧
                      Cont source replay observation ∧ Cont provenance name publicRead ∧
                        Cont observation publicRead latticeRead ∧ hsame provenance replay ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle latticeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig ProbeBundle UnaryHistory
  intro carrier sourceReplayObservation provenanceNamePublic observationPublicLattice latticePkg
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, _transportUnary,
    provenanceUnary, nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    provenanceReplay, provenancePkg, namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sourceUnary replayUnary sourceReplayObservation
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNamePublic
  have latticeReadUnary : UnaryHistory latticeRead :=
    unary_cont_closed observationUnary publicReadUnary observationPublicLattice
  exact
    ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, provenanceUnary, nameUnary,
      observationUnary, publicReadUnary, latticeReadUnary, scheduleStartReplay,
      sourceReplayObservation, provenanceNamePublic, observationPublicLattice,
      provenanceReplay, provenancePkg, namePkg, latticePkg⟩

end BEDC.Derived.HistTimeStreamUp
