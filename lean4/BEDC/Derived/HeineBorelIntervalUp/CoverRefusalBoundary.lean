import BEDC.Derived.HeineBorelIntervalUp.PublicFiniteNetExport

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalCoverRefusalBoundary [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N net mesh coverageRead stableRead inductionRead sealRead
      publicRead consumerRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net mesh coverageRead bundle pkg →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory N →
            Cont coverageRead T stableRead →
              HeineBorelIntervalFiniteNetInductionRoute
                  (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                  stableRead inductionRead bundle pkg →
                Cont inductionRead E sealRead →
                  Cont sealRead N publicRead →
                    Cont publicRead C consumerRead →
                      Cont consumerRead N refusalRead →
                        PkgSig bundle stableRead pkg →
                          PkgSig bundle sealRead pkg →
                            PkgSig bundle publicRead pkg →
                              PkgSig bundle consumerRead pkg →
                                PkgSig bundle refusalRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row refusalRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row coverageRead ∨ hsame row stableRead ∨
                                          hsame row inductionRead ∨ hsame row sealRead ∨
                                            hsame row publicRead ∨ hsame row consumerRead ∨
                                              hsame row refusalRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont coverageRead T stableRead ∧
                                            Cont inductionRead E sealRead ∧
                                              Cont sealRead N publicRead ∧
                                                Cont publicRead C consumerRead ∧
                                                  Cont consumerRead N refusalRead ∧
                                                    PkgSig bundle refusalRead pkg)
                                      hsame ∧
                                    UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro coverageRoute tailUnary eUnary nUnary coverageTailStable inductionRoute
    inductionSeal sealPublic publicConsumer consumerRefusal stablePkg sealPkg publicPkg
    consumerPkg refusalPkg
  have publicResult :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                Cont publicRead C consumerRead ∧ PkgSig bundle consumerRead pkg)
          hsame ∧
        UnaryHistory consumerRead :=
    HeineBorelIntervalPublicFiniteNetExport
      coverageRoute tailUnary eUnary nUnary coverageTailStable inductionRoute
      inductionSeal sealPublic publicConsumer stablePkg sealPkg publicPkg consumerPkg
  have consumerUnary : UnaryHistory consumerRead := publicResult.right
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed consumerUnary nUnary consumerRefusal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead ∨ hsame row consumerRead ∨
                hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                Cont publicRead C consumerRead ∧ Cont consumerRead N refusalRead ∧
                  PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead
        ⟨hsame_refl refusalRead, refusalUnary⟩
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
        ⟨source.right, coverageTailStable, inductionSeal, sealPublic, publicConsumer,
          consumerRefusal, refusalPkg⟩
  }
  exact ⟨cert, refusalUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
