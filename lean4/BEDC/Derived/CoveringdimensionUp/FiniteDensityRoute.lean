import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteDensityRoute [AskSetup] [PackageSetup]
    {K E C R O L H T P N densityRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont E C densityRead →
        Cont densityRead O orderRead →
          PkgSig bundle orderRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                    hsame row O ∨ hsame row L ∨ hsame row densityRead ∨
                      hsame row orderRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont E C densityRead ∧
                    Cont densityRead O orderRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle orderRead pkg)
                hsame ∧
              UnaryHistory densityRead ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier densityRoute orderRoute orderPkg
  obtain ⟨_KUnary, EUnary, CUnary, _RUnary, OUnary, _LUnary, _HUnary, _TUnary,
    _PUnary, _NUnary, _KECover, _CROrder, _OLReplay, _HTProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed EUnary CUnary densityRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed densityUnary OUnary orderRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro orderRead ⟨hsame_refl orderRead, orderUnary⟩
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
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, densityRoute, orderRoute, provenancePkg, orderPkg⟩
    }
  · exact ⟨densityUnary, orderUnary⟩

end BEDC.Derived.CoveringdimensionUp
