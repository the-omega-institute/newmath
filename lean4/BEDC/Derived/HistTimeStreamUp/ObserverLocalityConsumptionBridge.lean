import BEDC.Derived.HistTimeStreamUp

namespace BEDC.Derived.HistTimeStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HistTimeStreamCarrier_observer_locality_consumption_bridge [AskSetup] [PackageSetup]
    {source schedule start replay transport provenance name observerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg →
      Cont provenance name observerRead →
        PkgSig bundle observerRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                HistTimeStreamCarrier source schedule start replay transport provenance name
                  bundle pkg ∧ hsame row observerRead)
              (fun row : BHist =>
                UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
                  UnaryHistory replay ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
                    UnaryHistory name ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont schedule start replay ∧ Cont source replay provenance ∧
                  Cont provenance name observerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle observerRead pkg)
              hsame ∧
            UnaryHistory observerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier provenanceNameObserver observerPkg
  have carrierWitness := carrier
  obtain ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary, provenanceUnary,
    nameUnary, scheduleStartReplay, sourceReplayProvenance, _provenanceReplay, provenancePkg,
    namePkg⟩ := carrier
  have observerUnary : UnaryHistory observerRead :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameObserver
  have certCore :
      NameCert
        (fun row : BHist =>
          HistTimeStreamCarrier source schedule start replay transport provenance name bundle pkg ∧
            hsame row observerRead)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro observerRead
        (And.intro carrierWitness (hsame_refl observerRead))
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
              bundle pkg ∧ hsame row observerRead)
          (fun row : BHist =>
            UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory start ∧
              UnaryHistory replay ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
                UnaryHistory name ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont schedule start replay ∧ Cont source replay provenance ∧
              Cont provenance name observerRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle observerRead pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport observerUnary (hsame_symm sourceRow.right)
        exact
          ⟨sourceUnary, scheduleUnary, startUnary, replayUnary, transportUnary,
            provenanceUnary, nameUnary, rowUnary⟩
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨scheduleStartReplay, sourceReplayProvenance, provenanceNameObserver,
            provenancePkg, namePkg, observerPkg⟩
    }
  exact And.intro semantic observerUnary

end BEDC.Derived.HistTimeStreamUp
