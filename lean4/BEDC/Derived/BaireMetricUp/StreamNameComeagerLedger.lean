import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricStreamNameComeagerLedger [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B publicRead →
        PkgSig bundle P pkg →
          UnaryHistory publicRead ∧
            SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                  hsame row U ∨ Cont S B publicRead)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row publicRead)
              hsame := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier publicRoute provenancePkg
  obtain ⟨unaryS, unaryB, _unaryW, _unaryD, _unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, _radiusRoute, _ultrametricRoute, _carrierPkg, _carrierNamePkg⟩ :=
    carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryS unaryB publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row U ∨ Cont S B publicRead)
          (fun row : BHist => PkgSig bundle P pkg ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr publicRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.left⟩
  }
  exact ⟨publicUnary, cert⟩

end BEDC.Derived.BaireMetricUp
