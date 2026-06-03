import BEDC.Derived.BaireMetricUp.PrefixWindowAdmission

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricStreamNameNameCertScope [AskSetup] [PackageSetup]
    {B W D R U S H C P N prefixRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricCarrier B W D R U S H C P N bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W radiusRead →
          SemanticNameCert
              (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row prefixRead ∨
                  hsame row radiusRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead := by
  -- BEDC touchpoint anchor: BaireMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute radiusRoute
  obtain ⟨bUnary, wUnary, _dUnary, _rUnary, _uUnary, sUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierSBW, _carrierWDR, _carrierRUC, _carrierCNP,
    carrierPkg, carrierNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sUnary bUnary prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed prefixUnary wUnary radiusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row prefixRead ∨
              hsame row radiusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont prefixRead W radiusRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro radiusRead ⟨hsame_refl radiusRead, radiusUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixRoute, radiusRoute, carrierPkg, carrierNamePkg⟩
  }
  exact ⟨cert, prefixUnary, radiusUnary⟩

end BEDC.Derived.BaireMetricUp
