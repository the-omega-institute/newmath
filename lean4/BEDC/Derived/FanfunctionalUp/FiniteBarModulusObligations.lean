import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalFiniteBarModulusObligations [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      depthRead witnessRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg →
      Cont branch depth depthRead →
        Cont depthRead witness witnessRead →
          Cont witnessRead modulus modulusRead →
            PkgSig bundle modulusRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row branch ∨ hsame row depth ∨ hsame row witness ∨
                      hsame row modulus ∨ hsame row modulusRead)
                  (fun row : BHist =>
                    hsame row modulusRead ∧ Cont branch depth depthRead ∧
                      Cont depthRead witness witnessRead ∧
                        Cont witnessRead modulus modulusRead ∧
                          PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory depthRead ∧ UnaryHistory witnessRead ∧
                  UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier branchDepthRead depthWitnessRead witnessModulusRead modulusReadPkg
  obtain ⟨_cantorUnary, _fanUnary, _toleranceUnary, branchUnary, depthUnary,
    witnessUnary, modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _carrierBranchDepthWitness,
    _carrierWitnessModulusReplay, provenancePkg⟩ := carrier
  have depthReadUnary : UnaryHistory depthRead :=
    unary_cont_closed branchUnary depthUnary branchDepthRead
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed depthReadUnary witnessUnary depthWitnessRead
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessReadUnary modulusUnary witnessModulusRead
  have sourceModulusRead :
      (fun row : BHist =>
        hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg) modulusRead := by
    exact ⟨hsame_refl modulusRead, modulusReadUnary, modulusReadPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row branch ∨ hsame row depth ∨ hsame row witness ∨
              hsame row modulus ∨ hsame row modulusRead)
          (fun row : BHist =>
            hsame row modulusRead ∧ Cont branch depth depthRead ∧
              Cont depthRead witness witnessRead ∧ Cont witnessRead modulus modulusRead ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceModulusRead
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, branchDepthRead, depthWitnessRead, witnessModulusRead, provenancePkg⟩
  }
  exact ⟨cert, depthReadUnary, witnessReadUnary, modulusReadUnary⟩

end BEDC.Derived.FanfunctionalUp
