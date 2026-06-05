import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalLocalObligationSurface [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance
      localName localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus
        transport replay provenance localName bundle pkg →
      Cont transport replay localRead →
        PkgSig bundle localRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨
                  hsame row branch ∨ hsame row depth ∨ hsame row witness ∨
                    hsame row modulus ∨ hsame row transport ∨ hsame row replay ∨
                      hsame row provenance ∨ hsame row localName ∨ hsame row localRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont transport replay localRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localRead pkg)
              hsame ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier transportReplayLocal localPkg
  obtain ⟨_cantorUnary, _fanUnary, _toleranceUnary, _branchUnary, _depthUnary,
    _witnessUnary, _modulusUnary, transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    provenancePkg⟩ := carrier
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed transportUnary replayUnary transportReplayLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨ hsame row branch ∨
              hsame row depth ∨ hsame row witness ∨ hsame row modulus ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport replay localRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, transportReplayLocal, provenancePkg, localPkg⟩
  }
  exact ⟨cert, localUnary⟩

end BEDC.Derived.FanfunctionalUp
