import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_observer_locality_totality [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observerRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont provenance name observerRead →
        Cont observerRead replay endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row endpoint)
                (fun row : BHist => UnaryHistory row ∧ hsame row endpoint)
                (fun _row : BHist =>
                  Cont provenance name observerRead ∧ Cont observerRead replay endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg)
                hsame ∧
              UnaryHistory observerRead ∧ UnaryHistory endpoint ∧
                Cont provenance name observerRead ∧ Cont observerRead replay endpoint ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier provenanceNameObserver observerReplayEndpoint endpointPkg
  have carrierWitness := carrier
  obtain
    ⟨_sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
      provenanceUnary, nameUnary, _scheduleStartReplay, _sourceReplayProvenance,
      _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have observerUnary : UnaryHistory observerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameObserver
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed observerUnary replayUnary observerReplayEndpoint
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
          (fun row : BHist => UnaryHistory row ∧ hsame row endpoint)
          (fun _row : BHist =>
            Cont provenance name observerRead ∧ Cont observerRead replay endpoint ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact And.intro (unary_transport_symm endpointUnary sourceRow.right) sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨provenanceNameObserver, observerReplayEndpoint, provenancePkg, endpointPkg⟩
    }
  exact
    ⟨semantic, observerUnary, endpointUnary, provenanceNameObserver, observerReplayEndpoint,
      provenancePkg, endpointPkg⟩

end BEDC.Derived.HistTimeStreamUp
