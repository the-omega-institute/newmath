import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberWindowRadiusLedgerCoherence [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius radiusLedger ->
        PkgSig bundle radiusLedger pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row radiusLedger ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row window ∨ hsame row radius ∨ hsame row radiusLedger)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle radiusLedger pkg ∧
                  hsame row radiusLedger)
              hsame ∧
            UnaryHistory window ∧ UnaryHistory radius ∧ UnaryHistory radiusLedger ∧
              Cont window radius radiusLedger ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle radiusLedger pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier windowRadiusLedger radiusLedgerPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory radiusLedger :=
    unary_cont_closed windowUnary radiusUnary windowRadiusLedger
  have sourceLedger :
      (fun row : BHist => hsame row radiusLedger ∧ UnaryHistory row) radiusLedger := by
    exact ⟨hsame_refl radiusLedger, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row radiusLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row radius ∨ hsame row radiusLedger)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle radiusLedger pkg ∧
              hsame row radiusLedger)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro radiusLedger sourceLedger
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, radiusLedgerPkg, source.left⟩
    }
  exact
    ⟨cert, windowUnary, radiusUnary, ledgerUnary, windowRadiusLedger, provenancePkg,
      radiusLedgerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
