import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_majorant_consumer_coverage [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N selectedRoute endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      hsame selectedRoute M ->
        Cont selectedRoute E endpointRead ->
          PkgSig bundle endpointRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row selectedRoute ∨ hsame row E ∨
                    hsame row endpointRead)
                (fun row : BHist => PkgSig bundle endpointRead pkg ∧ UnaryHistory row)
                hsame ∧
              UnaryHistory M ∧ UnaryHistory selectedRoute ∧ UnaryHistory E ∧
                UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier selectedSame endpointRoute endpointPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, _WUnary, _SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, _pkgSig⟩ := carrier
  have selectedUnary : UnaryHistory selectedRoute :=
    unary_transport MUnary (hsame_symm selectedSame)
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed selectedUnary EUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row selectedRoute ∨ hsame row E ∨
              hsame row endpointRead)
          (fun row : BHist => PkgSig bundle endpointRead pkg ∧ UnaryHistory row)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead
        ⟨hsame_refl endpointRead, endpointUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨endpointPkg, sourceRow.right⟩
  }
  exact ⟨cert, MUnary, selectedUnary, EUnary, endpointUnary⟩

end BEDC.Derived.RealPowerSeriesUp
