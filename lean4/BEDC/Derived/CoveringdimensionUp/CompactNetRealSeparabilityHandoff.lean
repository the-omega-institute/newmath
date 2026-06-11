import BEDC.Derived.CoveringdimensionUp.FiniteRefinementNameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactNetRealSeparabilityHandoff [AskSetup] [PackageSetup]
    {K E C R O L M S Q A H T P N compactNet densityRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteRefinementCarrier K E C R O L M S Q A H T P N bundle pkg →
      Cont K E compactNet →
        Cont compactNet S densityRead →
          Cont densityRead O handoffRead →
            PkgSig bundle handoffRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row L ∨
                      hsame row S ∨ hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K E compactNet ∧
                      Cont compactNet S densityRead ∧ Cont densityRead O handoffRead ∧
                        PkgSig bundle handoffRead pkg)
                  hsame ∧
                UnaryHistory compactNet ∧ UnaryHistory densityRead ∧
                  UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteRefinementCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute densityRoute handoffRoute handoffPkg
  obtain ⟨KUnary, EUnary, CUnary, _RUnary, OUnary, LUnary, MUnary, SUnary, _QUnary,
    _AUnary, _HUnary, _TUnary, _PUnary, _NUnary, _KELedger, _CROrder, _OLTReplay,
    _SMAWindow, _AGTransport, _HTProvenance, _provenancePkg, _namePkg⟩ := carrier
  have compactUnary : UnaryHistory compactNet :=
    unary_cont_closed KUnary EUnary compactRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed compactUnary SUnary densityRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed densityUnary OUnary handoffRoute
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row L ∨ hsame row S ∨
              hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K E compactNet ∧ Cont compactNet S densityRead ∧
              Cont densityRead O handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact ⟨source.right, compactRoute, densityRoute, handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, compactUnary, densityUnary, handoffUnary⟩

end BEDC.Derived.CoveringdimensionUp
