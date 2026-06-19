import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp.UniformWindowObligation

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived

theorem CauchyContinuousMap_uniform_window_obligation [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp) {imageRead sealRead boundaryRead modulusRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay boundaryRead →
            Cont boundaryRead M.localName modulusRead →
              Cont modulusRead M.transport uniformRead →
                PkgSig bundle uniformRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                            hsame row M.replay ∨ hsame row M.transport ∨
                              hsame row uniformRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                          Cont imageRead M.realSealHandoff sealRead ∧
                            Cont sealRead M.replay boundaryRead ∧
                              Cont boundaryRead M.localName modulusRead ∧
                                Cont modulusRead M.transport uniformRead ∧
                                  PkgSig bundle uniformRead pkg)
                      hsame ∧
                    UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute modulusRoute uniformRoute uniformPkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, sealUnary,
    transportUnary, replayUnary, _provenanceUnary, localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealUnaryRead : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnaryRead replayUnary boundaryRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundaryUnary localNameUnary modulusRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed modulusUnary transportUnary uniformRoute
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead :=
    ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.replay ∨ hsame row M.transport ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.replay boundaryRead ∧
                  Cont boundaryRead M.localName modulusRead ∧
                    Cont modulusRead M.transport uniformRead ∧
                      PkgSig bundle uniformRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, imageRoute, sealRoute, boundaryRoute, modulusRoute,
          uniformRoute, uniformPkg⟩
  }
  exact ⟨cert, imageUnary, sealUnaryRead, boundaryUnary, modulusUnary, uniformUnary⟩

end BEDC.Derived.CauchyContinuousMapUp.UniformWindowObligation
