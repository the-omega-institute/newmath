import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootFiniteOrderCompatibility [AskSetup] [PackageSetup]
    {K E C R O L H T P N coverRead refinementRead overlapRead orderRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont E C coverRead →
        Cont coverRead R refinementRead →
          Cont refinementRead H overlapRead →
            Cont overlapRead O orderRead →
              Cont orderRead T replayRead →
                PkgSig bundle replayRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row R ∨ hsame row H ∨ hsame row O ∨
                          hsame row T ∨ hsame row coverRead ∨
                            hsame row refinementRead ∨ hsame row overlapRead ∨
                              hsame row orderRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont E C coverRead ∧
                          Cont coverRead R refinementRead ∧
                            Cont refinementRead H overlapRead ∧
                              Cont overlapRead O orderRead ∧ Cont orderRead T replayRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
                      hsame ∧
                    UnaryHistory coverRead ∧ UnaryHistory refinementRead ∧
                      UnaryHistory overlapRead ∧ UnaryHistory orderRead ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute refinementRoute overlapRoute orderRoute replayRoute replayPkg
  obtain ⟨_KUnary, EUnary, CUnary, RUnary, OUnary, _LUnary, HUnary, TUnary,
    _PUnary, _NUnary, _KEC, _CRO, _OLT, _HTP, provenancePkg, _localNamePkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed EUnary CUnary coverRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverReadUnary RUnary refinementRoute
  have overlapReadUnary : UnaryHistory overlapRead :=
    unary_cont_closed refinementReadUnary HUnary overlapRoute
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed overlapReadUnary OUnary orderRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed orderReadUnary TUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row R ∨ hsame row H ∨ hsame row O ∨ hsame row T ∨
              hsame row coverRead ∨ hsame row refinementRead ∨ hsame row overlapRead ∨
                hsame row orderRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E C coverRead ∧
              Cont coverRead R refinementRead ∧ Cont refinementRead H overlapRead ∧
                Cont overlapRead O orderRead ∧ Cont orderRead T replayRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, refinementRoute, overlapRoute, orderRoute,
          replayRoute, provenancePkg, replayPkg⟩
  }
  exact
    ⟨cert, coverReadUnary, refinementReadUnary, overlapReadUnary, orderReadUnary,
      replayReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
