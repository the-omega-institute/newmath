import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRefinementOrderRootRoute [AskSetup] [PackageSetup]
    {K E C R O L H T P N coverRead refinementRead orderRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont E C coverRead →
        Cont coverRead R refinementRead →
          Cont refinementRead O orderRead →
            Cont orderRead N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row R ∨ hsame row O ∨
                        hsame row coverRead ∨ hsame row refinementRead ∨
                          hsame row orderRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont E C coverRead ∧
                        Cont coverRead R refinementRead ∧
                          Cont refinementRead O orderRead ∧ Cont orderRead N namedRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory coverRead ∧ UnaryHistory refinementRead ∧
                    UnaryHistory orderRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute refinementRoute orderRoute namedRoute namedPkg
  obtain ⟨_KUnary, EUnary, CUnary, RUnary, OUnary, _LUnary, _HUnary, _TUnary,
    _PUnary, NUnary, _KECover, _CROrder, _OLTReplay, _HTProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed EUnary CUnary coverRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary RUnary refinementRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed refinementUnary OUnary orderRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed orderUnary NUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
          ⟨source.right, coverRoute, refinementRoute, orderRoute, namedRoute,
            provenancePkg, namedPkg⟩
    }
  · exact ⟨coverUnary, refinementUnary, orderUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
