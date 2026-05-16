import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_clock_refusal [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name clockRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont schedule start replay →
        Cont provenance name clockRead →
          PkgSig bundle clockRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row clockRead)
                (fun row : BHist => UnaryHistory row ∧ hsame row clockRead)
                (fun _row : BHist =>
                  Cont schedule start replay ∧ Cont source replay provenance ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle clockRead pkg)
                hsame ∧
              UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory replay ∧
                UnaryHistory clockRead ∧ Cont source replay provenance ∧
                  Cont provenance name clockRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle clockRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier scheduleStartReplayInput provenanceNameClock clockPkg
  have carrierPacket :
      HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, scheduleUnary, _startUnary, replayUnary, _transportUnary,
    provenanceUnary, nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have clockUnary : UnaryHistory clockRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameClock
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row clockRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row clockRead)
          (fun _row : BHist =>
            Cont schedule start replay ∧ Cont source replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle clockRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro clockRead (And.intro carrierPacket (hsame_refl clockRead))
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
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro row source
        exact And.intro (unary_transport clockUnary (hsame_symm source.right)) source.right
      ledger_sound := by
        intro _row _source
        exact
          ⟨scheduleStartReplayInput, sourceReplayProvenance, provenancePkg, clockPkg⟩
    }
  exact
    ⟨cert, sourceUnary, scheduleUnary, replayUnary, clockUnary, sourceReplayProvenance,
      provenanceNameClock, provenancePkg, clockPkg⟩

end BEDC.Derived.HistTimeStreamUp
