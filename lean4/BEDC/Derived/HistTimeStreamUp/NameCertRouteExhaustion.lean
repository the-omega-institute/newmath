import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamNameCertRouteExhaustion [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont source replay endpoint →
        Cont provenance name publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory replay ∧
                    UnaryHistory publicRead ∧ hsame row publicRead)
                (fun _row : BHist =>
                  Cont source replay provenance ∧ Cont source replay endpoint ∧
                    Cont provenance name publicRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory endpoint ∧ UnaryHistory publicRead ∧ hsame endpoint provenance := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sourceReplayEndpoint provenanceNamePublic publicPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    provenanceUnary, nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    _provenanceReplay, provenancePkg, namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary replayUnary sourceReplayEndpoint
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNamePublic
  have endpointSameProvenance : hsame endpoint provenance :=
    cont_deterministic sourceReplayEndpoint sourceReplayProvenance
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row publicRead)
        hsame := by
    exact {
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
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory replay ∧
              UnaryHistory publicRead ∧ hsame row publicRead)
          (fun _row : BHist =>
            Cont source replay provenance ∧ Cont source replay endpoint ∧
              Cont provenance name publicRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceUnary, scheduleUnary, replayUnary, publicUnary, sourceRow.right⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨sourceReplayProvenance, sourceReplayEndpoint, provenanceNamePublic, provenancePkg,
            namePkg, publicPkg⟩
    }
  exact ⟨semantic, endpointUnary, publicUnary, endpointSameProvenance⟩

end BEDC.Derived.HistTimeStreamUp
