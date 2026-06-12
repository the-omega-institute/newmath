import BEDC.Derived.DyadicMidpointUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicMidpointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicMidpointSelectedWindowDenominatorSeal [AskSetup] [PackageSetup]
    {left right scale midpoint branch window sameRows transport route provenance nameCert
      endpoint selectedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMidpointCarrier left right scale midpoint branch window sameRows transport route
        provenance nameCert endpoint bundle pkg →
      Cont scale midpoint selectedRead →
        Cont selectedRead branch sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row scale ∨ hsame row midpoint ∨ hsame row branch ∨
                    hsame row window ∨ hsame row selectedRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont scale midpoint selectedRead ∧
                    Cont selectedRead branch sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧ UnaryHistory selectedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scaleMidpointSelected selectedBranchSeal sealPkg
  obtain ⟨_leftUnary, _rightUnary, scaleUnary, midpointUnary, branchUnary, _windowUnary,
    _sameRowsUnary, _routeUnary, _transportUnary, _provenanceUnary, _nameCertUnary,
    _endpointUnary, _midpointRow, _endpointRoute, _scaleRoute, _midpointWindowRoute,
    _branchWindowRoute, _endpointPkg, _provenancePkg, _nameCertPkg⟩ := carrier
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed scaleUnary midpointUnary scaleMidpointSelected
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectedReadUnary branchUnary selectedBranchSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scale ∨ hsame row midpoint ∨ hsame row branch ∨ hsame row window ∨
              hsame row selectedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont scale midpoint selectedRead ∧
              Cont selectedRead branch sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact ⟨source.right, scaleMidpointSelected, selectedBranchSeal, sealPkg⟩
  }
  exact ⟨cert, selectedReadUnary, sealReadUnary⟩

end BEDC.Derived.DyadicMidpointUp
