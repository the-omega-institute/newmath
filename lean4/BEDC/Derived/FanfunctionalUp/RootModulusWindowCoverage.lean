import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootModulusWindowCoverage [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead depthRead witnessRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg →
      Cont C B prefixRead →
        Cont F D depthRead →
          Cont prefixRead W witnessRead →
            Cont witnessRead M modulusRead →
              PkgSig bundle P pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row B ∨ hsame row W ∨
                        hsame row prefixRead ∨ hsame row witnessRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C B prefixRead ∧
                        Cont prefixRead W witnessRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory prefixRead ∧ UnaryHistory depthRead ∧
                    UnaryHistory witnessRead ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute depthRoute witnessRoute modulusRoute provenancePkg
  obtain ⟨cUnary, fUnary, _epsUnary, bUnary, dUnary, wUnary, mUnary, _hUnary, _kUnary,
    _pUnary, _nUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary bUnary prefixRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed fUnary dUnary depthRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed prefixUnary wUnary witnessRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary mUnary modulusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row B ∨ hsame row W ∨ hsame row prefixRead ∨
              hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C B prefixRead ∧ Cont prefixRead W witnessRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro witnessRead ⟨hsame_refl witnessRead, witnessUnary⟩
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
      exact ⟨source.right, prefixRoute, witnessRoute, provenancePkg⟩
  }
  exact ⟨cert, prefixUnary, depthUnary, witnessUnary, modulusUnary⟩

end BEDC.Derived.FanfunctionalUp
