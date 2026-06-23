import BEDC.Derived.DyadicIntervalCoverUp.BridgeHandoff

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverContentSplitRoute [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead readbackRead coverRead sealRead
      subcoverRead namedRead publicRead coverBridgeRead sealBridgeRead bridgeRead
      realFacingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont windowRead R readbackRead →
            Cont readbackRead V coverRead →
              Cont coverRead A sealRead →
                Cont endpointRead sealRead subcoverRead →
                  Cont subcoverRead N namedRead →
                    Cont namedRead P publicRead →
                      Cont M R coverBridgeRead →
                        Cont coverBridgeRead A sealBridgeRead →
                          Cont endpointRead sealBridgeRead bridgeRead →
                            Cont bridgeRead A realFacingRead →
                              PkgSig bundle publicRead pkg →
                                PkgSig bundle bridgeRead pkg →
                                  PkgSig bundle realFacingRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row realFacingRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row L ∨ hsame row U ∨ hsame row M ∨
                                            hsame row R ∨ hsame row V ∨ hsame row W ∨
                                              hsame row Q ∨ hsame row A ∨ hsame row H ∨
                                                hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                  hsame row publicRead ∨
                                                    hsame row bridgeRead ∨
                                                      hsame row realFacingRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont bridgeRead A realFacingRead ∧
                                              PkgSig bundle realFacingRead pkg)
                                        hsame ∧ UnaryHistory bridgeRead ∧
                                      UnaryHistory realFacingRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
    namedRoute publicRoute coverBridgeRoute sealBridgeRoute bridgeRoute realFacingRoute
    publicPkg bridgePkg realFacingPkg
  have bridgeCert :=
    DyadicIntervalCoverBridgeHandoff
      surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
      namedRoute publicRoute coverBridgeRoute sealBridgeRoute bridgeRoute publicPkg bridgePkg
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have realFacingUnary : UnaryHistory realFacingRead :=
    unary_cont_closed bridgeCert.right aUnary realFacingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realFacingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row publicRead ∨ hsame row bridgeRead ∨
                  hsame row realFacingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bridgeRead A realFacingRead ∧
              PkgSig bundle realFacingRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realFacingRead ⟨hsame_refl realFacingRead, realFacingUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realFacingRoute, realFacingPkg⟩
  }
  exact ⟨cert, bridgeCert.right, realFacingUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
