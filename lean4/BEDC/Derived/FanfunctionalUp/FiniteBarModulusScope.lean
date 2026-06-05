import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalFiniteBarModulusScope [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      barRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg →
      Cont cantor fan barRead →
        Cont barRead modulus modulusRead →
          PkgSig bundle modulusRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row cantor ∨ hsame row fan ∨ hsame row witness ∨ hsame row modulus ∨
                    hsame row modulusRead)
                (fun row : BHist =>
                  hsame row modulusRead ∧ Cont cantor fan barRead ∧
                    Cont barRead modulus modulusRead ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory barRead ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier cantorFanBar barModulusRead modulusReadPkg
  obtain ⟨cantorUnary, fanUnary, _toleranceUnary, _branchUnary, _depthUnary,
    _witnessUnary, modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _carrierBranchDepthWitness,
    _carrierWitnessModulusReplay, provenancePkg⟩ := carrier
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanBar
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed barUnary modulusUnary barModulusRead
  have sourceModulusRead :
      (fun row : BHist =>
        hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg) modulusRead := by
    exact ⟨hsame_refl modulusRead, modulusReadUnary, modulusReadPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row witness ∨ hsame row modulus ∨
              hsame row modulusRead)
          (fun row : BHist =>
            hsame row modulusRead ∧ Cont cantor fan barRead ∧
              Cont barRead modulus modulusRead ∧ PkgSig bundle provenance pkg)
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
      exact ⟨source.left, cantorFanBar, barModulusRead, provenancePkg⟩
  }
  exact ⟨cert, barUnary, modulusReadUnary⟩

end BEDC.Derived.FanfunctionalUp
