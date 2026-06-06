import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootUnblockCantorPrefix [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      prefixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport
        replay provenance localName bundle pkg ->
      Cont cantor fan prefixRead ->
        PkgSig bundle provenance pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row prefixRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cantor ∨ hsame row fan ∨ hsame row prefixRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont cantor fan prefixRead ∧
                  PkgSig bundle provenance pkg)
              hsame ∧ UnaryHistory prefixRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier cantorFanPrefix provenancePkg
  obtain ⟨cantorUnary, fanUnary, _toleranceUnary, _branchUnary, _depthUnary,
    _witnessUnary, _modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _branchDepthWitness,
    _witnessModulusReplay, _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanPrefix
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row prefixRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row prefixRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cantor fan prefixRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro prefixRead ⟨hsame_refl prefixRead, prefixUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cantorFanPrefix, provenancePkg⟩
  }
  exact ⟨cert, prefixUnary⟩

end BEDC.Derived.FanfunctionalUp
