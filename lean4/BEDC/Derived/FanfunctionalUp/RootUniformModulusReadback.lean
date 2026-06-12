import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootUniformModulusReadback [AskSetup] [PackageSetup]
    {C F U B D W M H R P N compactRead uniformRead modulusRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F U B D W M H R P N bundle pkg →
      Cont C F compactRead →
        Cont compactRead U uniformRead →
          Cont W M modulusRead →
            Cont modulusRead N namedRead →
              PkgSig bundle P pkg →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row F ∨ hsame row U ∨ hsame row W ∨
                          hsame row M ∨ hsame row modulusRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C F compactRead ∧
                          Cont compactRead U uniformRead ∧ Cont W M modulusRead ∧
                            PkgSig bundle P pkg)
                      hsame ∧
                    UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
                      UnaryHistory modulusRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier cantorFanCompact compactToleranceUniform witnessModulusRead
    modulusNameRead pPkg _namedPkg
  obtain ⟨cantorUnary, fanUnary, toleranceUnary, _branchUnary, _depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary toleranceUnary compactToleranceUniform
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary modulusUnary witnessModulusRead
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed modulusReadUnary localNameUnary modulusNameRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row F ∨ hsame row U ∨ hsame row W ∨ hsame row M ∨
              hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C F compactRead ∧ Cont compactRead U uniformRead ∧
              Cont W M modulusRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead ⟨hsame_refl modulusRead, modulusReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cantorFanCompact, compactToleranceUniform, witnessModulusRead,
          pPkg⟩
  }
  exact ⟨cert, compactUnary, uniformUnary, modulusReadUnary, namedReadUnary⟩

end BEDC.Derived.FanfunctionalUp
