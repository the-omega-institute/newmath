import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived

theorem CauchyContinuousMap_bridge_scope [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp) {imageRead sealRead transportRead replayRead bridgeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.transport transportRead →
            Cont transportRead M.replay replayRead →
              Cont replayRead M.localName bridgeRead →
                PkgSig bundle bridgeRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                            hsame row M.transport ∨ hsame row M.replay ∨
                              hsame row M.provenance ∨ hsame row M.localName ∨
                                hsame row bridgeRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                          Cont imageRead M.realSealHandoff sealRead ∧
                            Cont sealRead M.transport transportRead ∧
                              Cont transportRead M.replay replayRead ∧
                                Cont replayRead M.localName bridgeRead ∧
                                  PkgSig bundle bridgeRead pkg)
                      hsame ∧
                    UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute transportRoute replayRoute bridgeRoute bridgePkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, realSealUnary,
    transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    _provenancePkg⟩ := packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary realSealUnary sealRoute
  have transportUnaryRead : UnaryHistory transportRead :=
    unary_cont_closed sealUnary transportUnary transportRoute
  have replayUnaryRead : UnaryHistory replayRead :=
    unary_cont_closed transportUnaryRead replayUnary replayRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed replayUnaryRead localNameUnary bridgeRoute
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead :=
    ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.transport ∨ hsame row M.replay ∨
                  hsame row M.provenance ∨ hsame row M.localName ∨
                    hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.transport transportRead ∧
                  Cont transportRead M.replay replayRead ∧
                    Cont replayRead M.localName bridgeRead ∧
                      PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceBridge
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
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, imageRoute, sealRoute, transportRoute, replayRoute,
          bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.CauchyContinuousMapUp
