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

theorem BaireMetricPrefixCylinderCoverage [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead cylinderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont ultrametricRead W cylinderRead →
        PkgSig bundle cylinderRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row cylinderRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                  hsame row radiusRead ∨ hsame row ultrametricRead ∨
                    hsame row cylinderRead)
              (fun row : BHist =>
                hsame row cylinderRead ∧ PkgSig bundle cylinderRead pkg ∧
                  PkgSig bundle P pkg)
              hsame ∧
            UnaryHistory cylinderRead ∧ Cont S B radiusRead ∧
              Cont radiusRead D ultrametricRead := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier cylinderRoute cylinderPkg
  obtain ⟨unaryS, unaryB, unaryW, unaryD, _unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have cylinderUnary : UnaryHistory cylinderRead :=
    unary_cont_closed ultrametricUnary unaryW cylinderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cylinderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
              hsame row radiusRead ∨ hsame row ultrametricRead ∨
                hsame row cylinderRead)
          (fun row : BHist =>
            hsame row cylinderRead ∧ PkgSig bundle cylinderRead pkg ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cylinderRead
        ⟨hsame_refl cylinderRead, cylinderUnary⟩
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
      exact ⟨source.left, cylinderPkg, provenancePkg⟩
  }
  exact ⟨cert, cylinderUnary, radiusRoute, ultrametricRoute⟩

end BEDC.Derived.BaireMetricUp
