import BEDC.Derived.HeineBorelIntervalUp.PublicFiniteNetExport

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalClosedIntervalNetExtraction [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N net mesh coverageRead stableRead inductionRead
      sealRead publicRead consumerRead extractionRead : BHist}
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
                      Cont consumerRead Q extractionRead →
                        PkgSig bundle extractionRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row extractionRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row K ∨ hsame row M ∨ hsame row Z ∨
                                  hsame row F ∨ hsame row Q ∨ hsame row C ∨
                                    hsame row N ∨ hsame row coverageRead ∨
                                      hsame row stableRead ∨ hsame row inductionRead ∨
                                        hsame row sealRead ∨ hsame row publicRead ∨
                                          hsame row consumerRead ∨
                                            hsame row extractionRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont consumerRead Q extractionRead ∧
                                  PkgSig bundle extractionRead pkg)
                              hsame ∧
                            UnaryHistory extractionRead := by
  -- BEDC touchpoint anchor: HeineBorelIntervalUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro coverageRoute tailUnary eUnary nUnary coverageTailStable inductionRoute
    inductionSeal sealPublic publicConsumer consumerExtract extractionPkg
  obtain ⟨kUnary, mUnary, zUnary, _fUnary, qUnary, cUnary, _pUnary, _nUnary,
    netRoute, coverageThroughMesh, _finiteCoverageRoute, _replayRoute, meshSame,
    _coveragePkg⟩ := coverageRoute
  have netUnary : UnaryHistory net :=
    unary_cont_closed kUnary mUnary netRoute
  have meshUnary : UnaryHistory mesh :=
    unary_transport_symm mUnary meshSame
  have coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed netUnary meshUnary coverageThroughMesh
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed coverageUnary tailUnary coverageTailStable
  obtain ⟨_zRouteUnary, _fRouteUnary, _cRouteUnary, _pRouteUnary, _nRouteUnary,
    stableInduction, _finiteReplay, _packageReplay, _inductionPkg⟩ := inductionRoute
  have inductionUnary : UnaryHistory inductionRead :=
    unary_cont_closed stableUnary zUnary stableInduction
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed inductionUnary eUnary inductionSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary nUnary sealPublic
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed publicUnary cUnary publicConsumer
  have extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed consumerUnary qUnary consumerExtract
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row extractionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row M ∨ hsame row Z ∨ hsame row F ∨ hsame row Q ∨
              hsame row C ∨ hsame row N ∨ hsame row coverageRead ∨ hsame row stableRead ∨
                hsame row inductionRead ∨ hsame row sealRead ∨ hsame row publicRead ∨
                  hsame row consumerRead ∨ hsame row extractionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont consumerRead Q extractionRead ∧
              PkgSig bundle extractionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro extractionRead
        ⟨hsame_refl extractionRead, extractionUnary⟩
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
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, consumerExtract, extractionPkg⟩
  }
  exact ⟨cert, extractionUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
