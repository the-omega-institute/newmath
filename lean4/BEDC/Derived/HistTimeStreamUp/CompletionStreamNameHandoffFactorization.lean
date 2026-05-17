import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_completion_streamname_handoff_factorization
    [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name streamNameHandoff
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont provenance name streamNameHandoff →
        Cont streamNameHandoff transport completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row completionRead)
                (fun row : BHist => UnaryHistory row ∧ hsame row completionRead)
                (fun _row : BHist =>
                  Cont source replay provenance ∧ Cont provenance name streamNameHandoff ∧
                    Cont streamNameHandoff transport completionRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory streamNameHandoff ∧ UnaryHistory completionRead ∧
                Cont source replay provenance ∧ Cont provenance name streamNameHandoff ∧
                  Cont streamNameHandoff transport completionRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier provenanceNameHandoff handoffTransportCompletion completionPkg
  have carrierWitness :
      HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, transportUnary,
    provenanceUnary, nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have streamNameUnary : UnaryHistory streamNameHandoff :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameHandoff
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed streamNameUnary transportUnary handoffTransportCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row completionRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row completionRead)
          (fun _row : BHist =>
            Cont source replay provenance ∧ Cont provenance name streamNameHandoff ∧
              Cont streamNameHandoff transport completionRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle completionRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionRead
          ⟨carrierWitness, hsame_refl completionRead⟩
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
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨unary_transport completionUnary (hsame_symm source.right), source.right⟩
      ledger_sound := by
        intro _row _source
        exact
          ⟨sourceReplayProvenance, provenanceNameHandoff, handoffTransportCompletion,
            provenancePkg, completionPkg⟩
    }
  exact
    ⟨cert, streamNameUnary, completionUnary, sourceReplayProvenance, provenanceNameHandoff,
      handoffTransportCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.HistTimeStreamUp
