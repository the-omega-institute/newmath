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

theorem CauchyContinuousMap_completion_consumer_scope [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp)
    {imageRead sealRead boundaryRead modulusRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay boundaryRead →
            Cont boundaryRead M.localName modulusRead →
              Cont modulusRead M.provenance completionRead →
                PkgSig bundle completionRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                            hsame row M.replay ∨ hsame row M.localName ∨
                              hsame row M.provenance ∨ hsame row completionRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                          Cont imageRead M.realSealHandoff sealRead ∧
                            Cont sealRead M.replay boundaryRead ∧
                              Cont boundaryRead M.localName modulusRead ∧
                                Cont modulusRead M.provenance completionRead ∧
                                  PkgSig bundle completionRead pkg)
                      hsame ∧
                    UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute modulusRoute completionRoute completionPkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, sealUnary,
    _transportUnary, replayUnary, provenanceUnary, localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealUnaryRead : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnaryRead replayUnary boundaryRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundaryUnary localNameUnary modulusRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed modulusUnary provenanceUnary completionRoute
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead :=
    ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.replay ∨ hsame row M.localName ∨
                  hsame row M.provenance ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.replay boundaryRead ∧
                  Cont boundaryRead M.localName modulusRead ∧
                    Cont modulusRead M.provenance completionRead ∧
                      PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
          completionRoute, completionPkg⟩
  }
  exact
    ⟨cert, imageUnary, sealUnaryRead, boundaryUnary, modulusUnary, completionUnary⟩

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
                        (fun row : BHist => hsame row realCompletionRead ∧
                          UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M.windows ∨ hsame row M.imageReadback ∨
                            hsame row M.toleranceLedger ∨
                              hsame row M.realSealHandoff ∨ hsame row M.replay ∨
                                hsame row M.localName ∨ hsame row M.provenance ∨
                                  hsame row completionRead ∨ hsame row realCompletionRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                            Cont imageRead M.realSealHandoff sealRead ∧
                              Cont sealRead M.replay boundaryRead ∧
                                Cont boundaryRead M.localName modulusRead ∧
                                  Cont modulusRead M.provenance completionRead ∧
                                    Cont completionRead M.realSealHandoff
                                      realCompletionRead ∧
                                      PkgSig bundle realCompletionRead pkg)
                        hsame ∧
                      UnaryHistory imageRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory modulusRead ∧
                          UnaryHistory completionRead ∧
                            UnaryHistory realCompletionRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute modulusRoute completionRoute realRoute
    realPkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, sealUnary,
    _transportUnary, replayUnary, provenanceUnary, localNameUnary, _provenancePkg⟩ :=
    packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealUnaryRead : UnaryHistory sealRead :=
    unary_cont_closed imageUnary sealUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnaryRead replayUnary boundaryRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundaryUnary localNameUnary modulusRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed modulusUnary provenanceUnary completionRoute
  have realCompletionUnary : UnaryHistory realCompletionRead :=
    unary_cont_closed completionUnary sealUnary realRoute
  have sourceReal :
      (fun row : BHist => hsame row realCompletionRead ∧
        UnaryHistory row) realCompletionRead := by
    exact ⟨hsame_refl realCompletionRead, realCompletionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.replay ∨ hsame row M.localName ∨ hsame row M.provenance ∨
                  hsame row completionRead ∨ hsame row realCompletionRead)
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
      carrier_inhabited := Exists.intro realCompletionRead sourceReal
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
        ⟨source.right, imageRoute, sealRoute, boundaryRoute, modulusRoute,
          completionRoute, realRoute, realPkg⟩
  }
  exact
    ⟨cert, imageUnary, sealUnaryRead, boundaryUnary, modulusUnary, completionUnary,
      realCompletionUnary⟩

theorem CauchyContinuousMap_bridge_readback_factorization [AskSetup] [PackageSetup]
    (M : CauchyContinuousMapUp)
    {imageRead sealRead boundaryRead completionRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousMapPacket M.windows M.imageReadback M.toleranceLedger
        M.realSealHandoff M.transport M.replay M.provenance M.localName bundle pkg →
      Cont M.windows M.imageReadback imageRead →
        Cont imageRead M.realSealHandoff sealRead →
          Cont sealRead M.replay boundaryRead →
            Cont boundaryRead M.transport completionRead →
              Cont completionRead M.localName bridgeRead →
                PkgSig bundle bridgeRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M.windows ∨ hsame row M.imageReadback ∨
                          hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                            hsame row M.transport ∨ hsame row M.replay ∨
                              hsame row M.localName ∨ hsame row bridgeRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
                          Cont imageRead M.realSealHandoff sealRead ∧
                            Cont sealRead M.replay boundaryRead ∧
                              Cont boundaryRead M.transport completionRead ∧
                                Cont completionRead M.localName bridgeRead ∧
                                  PkgSig bundle bridgeRead pkg)
                      hsame ∧
                    UnaryHistory bridgeRead ∧
                      hsame bridgeRead
                        (append (append (append (append (append M.windows M.imageReadback)
                          M.realSealHandoff) M.replay) M.transport) M.localName) := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro packet imageRoute sealRoute boundaryRoute completionRoute bridgeRoute bridgePkg
  obtain ⟨windowsUnary, imageReadbackUnary, _toleranceUnary, realSealUnary,
    transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    _provenancePkg⟩ := packet
  have imageUnary : UnaryHistory imageRead :=
    unary_cont_closed windowsUnary imageReadbackUnary imageRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed imageUnary realSealUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnary replayUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryUnary transportUnary completionRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed completionUnary localNameUnary bridgeRoute
  have sealExact :
      hsame sealRead (append (append M.windows M.imageReadback) M.realSealHandoff) :=
    sealRoute.trans (congrArg (fun row => append row M.realSealHandoff) imageRoute)
  have boundaryExact :
      hsame boundaryRead
        (append (append (append M.windows M.imageReadback) M.realSealHandoff) M.replay) :=
    boundaryRoute.trans (congrArg (fun row => append row M.replay) sealExact)
  have completionExact :
      hsame completionRead
        (append (append (append (append M.windows M.imageReadback) M.realSealHandoff)
          M.replay) M.transport) :=
    completionRoute.trans (congrArg (fun row => append row M.transport) boundaryExact)
  have bridgeExact :
      hsame bridgeRead
        (append (append (append (append (append M.windows M.imageReadback)
          M.realSealHandoff) M.replay) M.transport) M.localName) :=
    bridgeRoute.trans (congrArg (fun row => append row M.localName) completionExact)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M.windows ∨ hsame row M.imageReadback ∨
              hsame row M.toleranceLedger ∨ hsame row M.realSealHandoff ∨
                hsame row M.transport ∨ hsame row M.replay ∨
                  hsame row M.localName ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M.windows M.imageReadback imageRead ∧
              Cont imageRead M.realSealHandoff sealRead ∧
                Cont sealRead M.replay boundaryRead ∧
                  Cont boundaryRead M.transport completionRead ∧
                    Cont completionRead M.localName bridgeRead ∧
                      PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, imageRoute, sealRoute, boundaryRoute, completionRoute, bridgeRoute,
          bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary, bridgeExact⟩

end BEDC.Derived.CauchyContinuousMapUp
