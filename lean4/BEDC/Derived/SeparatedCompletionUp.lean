import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparatedCompletionCarrier [AskSetup] [PackageSetup]
    (metric dense completion classifier unique transport replay ledger provenance nameRow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory metric ∧ UnaryHistory dense ∧ UnaryHistory completion ∧
    UnaryHistory classifier ∧ UnaryHistory unique ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
        UnaryHistory nameRow ∧ Cont metric dense completion ∧
          Cont completion classifier unique ∧ Cont unique transport replay ∧
            Cont replay ledger nameRow ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameRow pkg

theorem SeparatedCompletionCarrier_semantic_package [AskSetup] [PackageSetup]
    {metric dense completion classifier unique transport replay ledger provenance nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedCompletionCarrier metric dense completion classifier unique transport replay
        ledger provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row completion ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row dense ∨ hsame row completion ∨
              hsame row classifier ∨ hsame row unique)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
              hsame row completion)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  obtain ⟨_metricUnary, _denseUnary, completionUnary, _classifierUnary, _uniqueUnary,
    _transportUnary, _replayUnary, _ledgerUnary, _provenanceUnary, _nameRowUnary,
    _metricDenseCompletion, _completionClassifierUnique, _uniqueTransportReplay,
    _replayLedgerNameRow, provenancePkg, nameRowPkg⟩ := carrier
  have completionWitness :
      (fun row : BHist => hsame row completion ∧ UnaryHistory row) completion := by
    exact ⟨hsame_refl completion, completionUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro completion completionWitness
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, nameRowPkg, source.left⟩
  }

theorem SeparatedCompletionCarrier_semantic_name_certificate
    (M D C Z U H R T P N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro M (Or.inl (hsame_refl M))
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
        | inl sameM =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameM)
        | inr rest =>
            cases rest with
            | inl sameD =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameD))
            | inr rest =>
                cases rest with
                | inl sameC =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameC)))
                | inr rest =>
                    cases rest with
                    | inl sameZ =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameZ))))
                    | inr rest =>
                        cases rest with
                        | inl sameU =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl (hsame_trans (hsame_symm sameRows) sameU)))))
                        | inr rest =>
                            cases rest with
                            | inl sameH =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameH))))))
                            | inr rest =>
                                cases rest with
                                | inl sameR =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameR)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameT =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows) sameT))))))))
                                    | inr rest =>
                                        cases rest with
                                        | inl sameP =>
                                            exact
                                              Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameP)))))))))
                                        | inr sameN =>
                                            exact
                                              Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameN)))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem SeparatedCompletionCarrier_separated_limit_handoff
    {source dense handoff classifier unique : BHist} :
    UnaryHistory source →
      UnaryHistory dense →
        UnaryHistory classifier →
          Cont source dense handoff →
            Cont handoff classifier unique →
              UnaryHistory handoff ∧ UnaryHistory unique ∧
                Cont source dense handoff ∧ Cont handoff classifier unique := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary denseUnary classifierUnary sourceDenseHandoff handoffClassifierUnique
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sourceUnary denseUnary sourceDenseHandoff
  exact
    ⟨handoffUnary,
      unary_cont_closed handoffUnary classifierUnary handoffClassifierUnique,
      sourceDenseHandoff,
      handoffClassifierUnique⟩

end BEDC.Derived.SeparatedCompletionUp
