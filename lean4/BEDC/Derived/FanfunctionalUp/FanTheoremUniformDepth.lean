import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalFanTheoremUniformDepth [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead depthRead witnessRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg →
      Cont C B prefixRead →
        Cont F D depthRead →
          Cont depthRead W witnessRead →
            Cont witnessRead M modulusRead →
              PkgSig bundle P pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row depthRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row D ∨ hsame row depthRead ∨ hsame row W)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F D depthRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory prefixRead ∧ UnaryHistory depthRead ∧
                    UnaryHistory witnessRead ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier cantorBranchPrefix fanDepthRead depthWitnessRead witnessModulusRead pPkg
  obtain ⟨cantorUnary, fanUnary, _epsUnary, branchUnary, depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cantorUnary branchUnary cantorBranchPrefix
  have depthReadUnary : UnaryHistory depthRead :=
    unary_cont_closed fanUnary depthUnary fanDepthRead
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed depthReadUnary witnessUnary depthWitnessRead
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessReadUnary modulusUnary witnessModulusRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row depthRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row depthRead ∨ hsame row W)
          (fun row : BHist => UnaryHistory row ∧ Cont F D depthRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro depthRead ⟨hsame_refl depthRead, depthReadUnary⟩
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
      exact ⟨source.right, fanDepthRead, pPkg⟩
  }
  exact ⟨cert, prefixUnary, depthReadUnary, witnessReadUnary, modulusReadUnary⟩

end BEDC.Derived.FanfunctionalUp
