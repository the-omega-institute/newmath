import BEDC.Derived.CoveringdimensionUp.CompactNetRealSeparabilityHandoff

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityCoverPullback [AskSetup] [PackageSetup]
    {K E C R O L M S Q A H T P N realSealRead coverPullback orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteRefinementCarrier K E C R O L M S Q A H T P N bundle pkg →
      Cont R Q realSealRead →
        Cont realSealRead E coverPullback →
          Cont coverPullback A orderRead →
            PkgSig bundle orderRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row S ∨
                      hsame row A ∨ hsame row orderRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R Q realSealRead ∧
                      Cont realSealRead E coverPullback ∧
                        Cont coverPullback A orderRead ∧ PkgSig bundle orderRead pkg)
                  hsame ∧
                UnaryHistory realSealRead ∧ UnaryHistory coverPullback ∧
                  UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier realSealRoute pullbackRoute orderRoute orderPkg
  obtain ⟨_KUnary, EUnary, _CUnary, RUnary, _OUnary, _LUnary, _MUnary, SUnary, QUnary,
    AUnary, _HUnary, _TUnary, _PUnary, _NUnary, _KELedger, _CROrder, _OLTReplay,
    _SMAWindow, _AGTransport, _HTProvenance, _provenancePkg, _namePkg⟩ := carrier
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed RUnary QUnary realSealRoute
  have pullbackUnary : UnaryHistory coverPullback :=
    unary_cont_closed realSealUnary EUnary pullbackRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed pullbackUnary AUnary orderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row S ∨ hsame row A ∨
              hsame row orderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R Q realSealRead ∧
              Cont realSealRead E coverPullback ∧ Cont coverPullback A orderRead ∧
                PkgSig bundle orderRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro orderRead ⟨hsame_refl orderRead, orderUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealRoute, pullbackRoute, orderRoute, orderPkg⟩
  }
  exact ⟨cert, realSealUnary, pullbackUnary, orderUnary⟩

end BEDC.Derived.CoveringdimensionUp
