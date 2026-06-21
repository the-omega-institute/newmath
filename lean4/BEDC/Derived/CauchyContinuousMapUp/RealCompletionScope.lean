import BEDC.Derived.CauchyContinuousMapUp.CompletionConsumerScope

namespace BEDC.Derived.CauchyContinuousMapUp.RealCompletionScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived
open BEDC.Derived.CauchyContinuousMapUp

theorem CauchyContinuousMap_real_completion_scope [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp)
    {imageRead sealRead boundaryRead modulusRead completionRead realCompletionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay boundaryRead →
            Cont boundaryRead M.localName modulusRead →
              Cont modulusRead M.provenance completionRead →
                Cont completionRead M.realSealHandoff realCompletionRead →
                  PkgSig bundle realCompletionRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M.windows ∨ hsame row M.imageReadback ∨
                            hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                              hsame row M.replay ∨ hsame row M.localName ∨
                                hsame row M.provenance ∨ hsame row realCompletionRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                            Cont imageRead M.realSealHandoff sealRead ∧
                              Cont sealRead M.replay boundaryRead ∧
                                Cont boundaryRead M.localName modulusRead ∧
                                  Cont modulusRead M.provenance completionRead ∧
                                    Cont completionRead M.realSealHandoff realCompletionRead ∧
                                      PkgSig bundle realCompletionRead pkg)
                        hsame ∧
                      UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory modulusRead ∧
                          UnaryHistory completionRead ∧ UnaryHistory realCompletionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute modulusRoute completionRoute
    realCompletionRoute realCompletionPkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, realSealUnary,
    _transportUnary, replayUnary, provenanceUnary, localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary realSealUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealReadUnary replayUnary boundaryRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundaryUnary localNameUnary modulusRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed modulusUnary provenanceUnary completionRoute
  have realCompletionUnary : UnaryHistory realCompletionRead :=
    unary_cont_closed completionUnary realSealUnary realCompletionRoute
  have sourceRealCompletion :
      (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
        realCompletionRead :=
    ⟨hsame_refl realCompletionRead, realCompletionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.replay ∨ hsame row M.localName ∨ hsame row M.provenance ∨
                  hsame row realCompletionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.replay boundaryRead ∧
                  Cont boundaryRead M.localName modulusRead ∧
                    Cont modulusRead M.provenance completionRead ∧
                      Cont completionRead M.realSealHandoff realCompletionRead ∧
                        PkgSig bundle realCompletionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realCompletionRead sourceRealCompletion
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
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, imageRoute, sealRoute, boundaryRoute, modulusRoute,
          completionRoute, realCompletionRoute, realCompletionPkg⟩
  }
  exact
    ⟨cert, imageUnary, sealReadUnary, boundaryUnary, modulusUnary, completionUnary,
      realCompletionUnary⟩

end BEDC.Derived.CauchyContinuousMapUp.RealCompletionScope
