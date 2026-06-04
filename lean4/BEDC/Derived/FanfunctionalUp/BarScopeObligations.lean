import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalBarScopeObligations [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance
      localName barRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg →
      Cont branch depth barRead →
        PkgSig bundle provenance pkg →
          SemanticNameCert
              (fun row : BHist => hsame row barRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cantor ∨ hsame row fan ∨ hsame row branch ∨
                  hsame row depth ∨ hsame row witness ∨ hsame row barRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont branch depth barRead ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory branch ∧ UnaryHistory depth ∧ UnaryHistory barRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier branchDepthBar provenancePkg
  obtain ⟨_cantorUnary, _fanUnary, _toleranceUnary, branchUnary, depthUnary,
    _witnessUnary, _modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _carrierBranchDepthWitness,
    _carrierWitnessModulusReplay, _carrierProvenancePkg⟩ := carrier
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed branchUnary depthUnary branchDepthBar
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row barRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row branch ∨ hsame row depth ∨
              hsame row witness ∨ hsame row barRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont branch depth barRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro barRead ⟨hsame_refl barRead, barUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, branchDepthBar, provenancePkg⟩
  }
  exact ⟨cert, branchUnary, depthUnary, barUnary⟩

end BEDC.Derived.FanfunctionalUp
