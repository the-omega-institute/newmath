import BEDC.Derived.RealApartnessCompletionUp

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionSeparatedSourceExactness [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName separatedRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont apartness separation separatedRead →
        Cont separatedRead completion completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                    hsame row separatedRead ∨ hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont apartness separation separatedRead ∧
                    Cont separatedRead completion completionRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory separatedRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute completionRoute completionPkg
  obtain ⟨apartnessUnary, separationUnary, completionUnary, _streamUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
      carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed apartnessUnary separationUnary separatedRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary completionUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row separatedRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation separatedRead ∧
              Cont separatedRead completion completionRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, separatedRoute, completionRoute, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, separatedUnary, completionReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp
