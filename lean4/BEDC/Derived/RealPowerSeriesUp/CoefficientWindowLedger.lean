import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_coefficient_window_ledger [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coefficientRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coefficientRead ->
        PkgSig bundle coefficientRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row coefficientRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A ∨ hsame row W ∨ hsame row S ∨ Cont A W coefficientRead)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle coefficientRead pkg ∧
                  hsame row coefficientRead)
              hsame ∧
            UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
              UnaryHistory coefficientRead ∧ Cont A W coefficientRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle coefficientRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier coefficientRoute coefficientPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed AUnary WUnary coefficientRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coefficientRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row S ∨ Cont A W coefficientRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle coefficientRead pkg ∧
              hsame row coefficientRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro coefficientRead ⟨hsame_refl coefficientRead, coefficientUnary⟩
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
      exact Or.inr (Or.inr (Or.inr coefficientRoute))
    ledger_sound := by
      intro _row source
      exact ⟨pkgSig, coefficientPkg, source.left⟩
  }
  exact
    ⟨cert, AUnary, WUnary, SUnary, coefficientUnary, coefficientRoute, pkgSig,
      coefficientPkg⟩

end BEDC.Derived.RealPowerSeriesUp
