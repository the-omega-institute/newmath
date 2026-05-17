import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_no_global_clock_nonescape [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observerRead clockAttempt : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont provenance name observerRead →
        hsame clockAttempt observerRead →
          PkgSig bundle observerRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  HistTimeStreamCarrier source schedule start replay transport provenance name
                    bundle pkg ∧ hsame row observerRead)
                (fun row : BHist => UnaryHistory row ∧ hsame row observerRead)
                (fun _row : BHist =>
                  Cont source replay provenance ∧ Cont provenance name observerRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle observerRead pkg)
                hsame ∧
              UnaryHistory observerRead ∧ UnaryHistory clockAttempt ∧
                hsame clockAttempt observerRead ∧ Cont source replay provenance ∧
                  Cont provenance name observerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle observerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier provenanceNameObserver clockObserver observerPkg
  have carrierPacket :
      HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _scheduleUnary, _startUnary, replayUnary, _transportUnary,
    provenanceUnary, nameUnary, _scheduleStartReplay, sourceReplayProvenance,
    _provenanceReplay, provenancePkg, _namePkg⟩ := carrier
  have observerUnary : UnaryHistory observerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameObserver
  have clockUnary : UnaryHistory clockAttempt :=
    unary_transport observerUnary (hsame_symm clockObserver)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HistTimeStreamCarrier source schedule start replay transport provenance name
              bundle pkg ∧ hsame row observerRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row observerRead)
          (fun _row : BHist =>
            Cont source replay provenance ∧ Cont provenance name observerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle observerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro observerRead
          (And.intro carrierPacket (hsame_refl observerRead))
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
          intro _row _other sameRows sourceRow
          exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
      }
      pattern_sound := by
        intro _row sourceRow
        exact And.intro (unary_transport observerUnary (hsame_symm sourceRow.right))
          sourceRow.right
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨sourceReplayProvenance, provenanceNameObserver, provenancePkg, observerPkg⟩
    }
  exact
    ⟨cert, observerUnary, clockUnary, clockObserver, sourceReplayProvenance,
      provenanceNameObserver, provenancePkg, observerPkg⟩

end BEDC.Derived.HistTimeStreamUp
