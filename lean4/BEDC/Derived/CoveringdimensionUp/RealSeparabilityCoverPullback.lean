import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityCoverPullback [AskSetup] [PackageSetup]
    {K M E U R Q S A H T P N realPull coverPull nerveRead orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K M E U A S H T P N bundle pkg ->
      UnaryHistory R ->
        UnaryHistory Q ->
          Cont R Q realPull ->
            Cont realPull E coverPull ->
              Cont coverPull S nerveRead ->
                Cont nerveRead A orderRead ->
                  PkgSig bundle orderRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row U ∨
                            hsame row S ∨ hsame row A ∨ hsame row realPull ∨
                              hsame row coverPull ∨ hsame row nerveRead ∨
                                hsame row orderRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont R Q realPull ∧
                            Cont realPull E coverPull ∧ Cont coverPull S nerveRead ∧
                              Cont nerveRead A orderRead ∧ PkgSig bundle orderRead pkg)
                        hsame ∧
                      UnaryHistory realPull ∧ UnaryHistory coverPull ∧
                        UnaryHistory nerveRead ∧ UnaryHistory orderRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier RUnary QUnary realRoute coverRoute nerveRoute orderRoute orderPkg
  obtain ⟨_KUnary, _MUnary, EUnary, _UUnary, AUnary, SUnary, _HUnary, _TUnary,
    _PUnary, _NUnary, _KME, _EUAS, _ASHT, _HTPN, _PPkg, _NPkg⟩ := carrier
  have realUnary : UnaryHistory realPull :=
    unary_cont_closed RUnary QUnary realRoute
  have coverUnary : UnaryHistory coverPull :=
    unary_cont_closed realUnary EUnary coverRoute
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed coverUnary SUnary nerveRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed nerveUnary AUnary orderRoute
  have sourceOrder :
      (fun row : BHist => hsame row orderRead ∧ UnaryHistory row) orderRead := by
    exact ⟨hsame_refl orderRead, orderUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row U ∨ hsame row S ∨
              hsame row A ∨ hsame row realPull ∨ hsame row coverPull ∨
                hsame row nerveRead ∨ hsame row orderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R Q realPull ∧ Cont realPull E coverPull ∧
              Cont coverPull S nerveRead ∧ Cont nerveRead A orderRead ∧
                PkgSig bundle orderRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro orderRead sourceOrder
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realRoute, coverRoute, nerveRoute, orderRoute, orderPkg⟩
  }
  exact ⟨cert, realUnary, coverUnary, nerveUnary, orderUnary⟩

end BEDC.Derived.CoveringdimensionUp
