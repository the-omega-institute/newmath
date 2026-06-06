import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootChoiceFreeNonescape [AskSetup] [PackageSetup]
    {C F U B D W M H R P N rootWindowRead witnessRead modulusRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F U B D W M H R P N bundle pkg →
      Cont C B rootWindowRead →
        Cont rootWindowRead W witnessRead →
          Cont witnessRead M modulusRead →
            Cont modulusRead N publicRead →
              PkgSig bundle P pkg →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row B ∨ hsame row W ∨ hsame row M ∨
                          hsame row N ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C B rootWindowRead ∧
                          Cont rootWindowRead W witnessRead ∧
                            Cont witnessRead M modulusRead ∧ Cont modulusRead N publicRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
                      hsame ∧ UnaryHistory rootWindowRead ∧ UnaryHistory witnessRead ∧
                    UnaryHistory modulusRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier rootWindow witnessWindow witnessModulus modulusPublic provenancePkg publicPkg
  obtain ⟨cantorUnary, _fanUnary, _toleranceUnary, branchUnary, _depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay, _carrierProvenancePkg⟩ :=
    carrier
  have rootUnary : UnaryHistory rootWindowRead :=
    unary_cont_closed cantorUnary branchUnary rootWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed rootUnary witnessUnary witnessWindow
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessReadUnary modulusUnary witnessModulus
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed modulusReadUnary localNameUnary modulusPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row B ∨ hsame row W ∨ hsame row M ∨ hsame row N ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C B rootWindowRead ∧ Cont rootWindowRead W witnessRead ∧
              Cont witnessRead M modulusRead ∧ Cont modulusRead N publicRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        ⟨source.right, rootWindow, witnessWindow, witnessModulus, modulusPublic,
          provenancePkg, publicPkg⟩
  }
  exact ⟨cert, rootUnary, witnessReadUnary, modulusReadUnary, publicUnary⟩

end BEDC.Derived.FanfunctionalUp
