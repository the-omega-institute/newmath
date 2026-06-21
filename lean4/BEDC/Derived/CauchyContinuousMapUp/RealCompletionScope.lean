import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp.RealCompletionScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived

theorem CauchyContinuousMapRealCompletionScope [AskSetup] [PackageSetup]
    (M : BEDC.Derived.CauchyContinuousMapUp)
    {imageRead sealRead boundaryRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.toleranceLedger imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay boundaryRead →
            Cont boundaryRead M.provenance completionRead →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M.windows ∨ hsame row M.toleranceLedger ∨
                        hsame row imageRead ∨ hsame row sealRead ∨
                          hsame row boundaryRead ∨ hsame row completionRead ∨
                            hsame row M.provenance)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M.windows M.toleranceLedger imageRead ∧
                        Cont imageRead M.realSealHandoff sealRead ∧
                          Cont sealRead M.replay boundaryRead ∧
                            Cont boundaryRead M.provenance completionRead ∧
                              PkgSig bundle completionRead pkg)
                    hsame ∧
                  UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute completionRoute completionPkg
  obtain ⟨windowsUnary, _imageReadbackUnary, toleranceUnary, sealUnary,
    _transportUnary, replayUnary, provenanceUnary, _localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary toleranceUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealReadUnary replayUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryUnary provenanceUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.toleranceLedger ∨ hsame row imageRead ∨
              hsame row sealRead ∨ hsame row boundaryRead ∨ hsame row completionRead ∨
                hsame row M.provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.toleranceLedger imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.replay boundaryRead ∧
                  Cont boundaryRead M.provenance completionRead ∧
                    PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, imageRoute, sealRoute, boundaryRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, imageUnary, sealReadUnary, boundaryUnary, completionUnary⟩

end BEDC.Derived.CauchyContinuousMapUp.RealCompletionScope
