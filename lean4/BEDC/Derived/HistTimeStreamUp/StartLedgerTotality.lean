import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_start_ledger_totality [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont schedule start endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist =>
                HistTimeStreamCarrier source schedule start replay transport provenance name
                  bundle pkg ∧ hsame row endpoint)
              (fun row : BHist =>
                UnaryHistory schedule ∧ UnaryHistory start ∧ UnaryHistory endpoint ∧
                  hsame row endpoint)
              (fun _row : BHist =>
                Cont schedule start replay ∧ Cont schedule start endpoint ∧
                  PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory endpoint ∧ hsame endpoint replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier scheduleStartEndpoint endpointPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, scheduleUnary, startUnary, _replayUnary, _transportUnary,
    _provenanceUnary, _nameUnary, scheduleStartReplay, _sourceReplayProvenance,
    _provenanceReplay, _provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed scheduleUnary startUnary scheduleStartEndpoint
  have endpointSameReplay : hsame endpoint replay :=
    cont_deterministic scheduleStartEndpoint scheduleStartReplay
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
          (fun row : BHist =>
            UnaryHistory schedule ∧ UnaryHistory start ∧ UnaryHistory endpoint ∧
              hsame row endpoint)
          (fun _row : BHist =>
            Cont schedule start replay ∧ Cont schedule start endpoint ∧
              PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨scheduleUnary, startUnary, endpointUnary, sourceRow.right⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨scheduleStartReplay, scheduleStartEndpoint, endpointPkg⟩
    }
  exact And.intro semantic (And.intro endpointUnary endpointSameReplay)

end BEDC.Derived.HistTimeStreamUp
