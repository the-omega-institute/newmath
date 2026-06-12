import BEDC.Derived.BaireMetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricCarrier_ultrametric_window_obligations [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead parentRead strongRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg ->
      Cont ultrametricRead R parentRead ->
        Cont parentRead U strongRead ->
          SemanticNameCert
              (fun row : BHist => hsame row strongRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                  hsame row R ∨ hsame row U ∨ hsame row strongRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont radiusRead D ultrametricRead ∧
                  Cont ultrametricRead R parentRead ∧ Cont parentRead U strongRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory parentRead ∧ UnaryHistory strongRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier parentRoute strongRoute
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, _radiusRoute, ultrametricRoute, provenancePkg, localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB _radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have parentUnary : UnaryHistory parentRead :=
    unary_cont_closed ultrametricUnary unaryR parentRoute
  have strongUnary : UnaryHistory strongRead :=
    unary_cont_closed parentUnary unaryU strongRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row strongRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row U ∨ hsame row strongRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont radiusRead D ultrametricRead ∧
              Cont ultrametricRead R parentRead ∧ Cont parentRead U strongRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro strongRead ⟨hsame_refl strongRead, strongUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, ultrametricRoute, parentRoute, strongRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, parentUnary, strongUnary⟩

end BEDC.Derived.BaireMetricUp
