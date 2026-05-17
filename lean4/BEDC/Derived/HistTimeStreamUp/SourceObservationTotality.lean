import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_source_observation_totality [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observation readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay observation →
        Cont observation transport readback →
          PkgSig bundle observation pkg →
            PkgSig bundle readback pkg →
              SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row readback)
                (fun row : BHist =>
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
                    UnaryHistory replay ∧ UnaryHistory observation ∧ UnaryHistory row)
                (fun _row : BHist =>
                  Cont source replay observation ∧ Cont observation transport readback ∧
                    PkgSig bundle observation pkg ∧ PkgSig bundle readback pkg)
                hsame ∧ UnaryHistory observation ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayObservation observationTransportReadback observationPkg readbackPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary,
    _provenanceUnary, _nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed sourceUnary replayUnary sourceReplayObservation
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed observationUnary transportUnary observationTransportReadback
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name
            bundle pkg ∧ hsame row readback)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro readback
        (And.intro carrierWitness (hsame_refl readback))
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
            bundle pkg ∧ hsame row readback)
        (fun row : BHist =>
          UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
            UnaryHistory replay ∧ UnaryHistory observation ∧ UnaryHistory row)
        (fun _row : BHist =>
          Cont source replay observation ∧ Cont observation transport readback ∧
            PkgSig bundle observation pkg ∧ PkgSig bundle readback pkg)
        hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, observationUnary,
            unary_transport readbackUnary (hsame_symm sourceRow.right)⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayObservation, observationTransportReadback, observationPkg, readbackPkg⟩
    }
  exact ⟨semantic, observationUnary, readbackUnary⟩

end BEDC.Derived.HistTimeStreamUp
