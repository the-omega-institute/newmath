import BEDC.Derived.CauchyContinuousMapUp.CompletionConsumerScope

namespace BEDC.Derived.CauchyContinuousMapUp.SeparatedCompletionFactorization

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CauchyContinuousMapUp

theorem CauchyContinuousMap_separated_completion_factorization [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp)
    {imageRead sealRead completionRead separatedRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.provenance completionRead →
            Cont completionRead M.transport separatedRead →
              Cont separatedRead M.replay boundaryRead →
                PkgSig bundle boundaryRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.realSealHandoff ∨ hsame row M.provenance ∨
                            hsame row M.transport ∨ hsame row M.replay ∨
                              hsame row separatedRead ∨ hsame row boundaryRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundaryRead pkg)
                      hsame ∧
                    UnaryHistory completionRead ∧ UnaryHistory separatedRead ∧
                      UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute completionRoute separatedRoute boundaryRoute boundaryPkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, _localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary provenanceUnary completionRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed completionUnary transportUnary separatedRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed separatedUnary replayUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.realSealHandoff ∨ hsame row M.provenance ∨
                hsame row M.transport ∨ hsame row M.replay ∨
                  hsame row separatedRead ∨ hsame row boundaryRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, boundaryPkg⟩
  }
  exact ⟨cert, completionUnary, separatedUnary, boundaryUnary⟩

end BEDC.Derived.CauchyContinuousMapUp.SeparatedCompletionFactorization
