import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberWindowRadiusSourceLock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow radiusLedger meshRead
      sourceLock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius radiusLedger ->
        Cont radiusLedger mesh meshRead ->
          Cont meshRead route sourceLock ->
            PkgSig bundle sourceLock pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
                      hsame row radiusLedger ∨ hsame row sourceLock)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle sourceLock pkg ∧
                      hsame row sourceLock)
                  hsame ∧
                UnaryHistory window ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
                  UnaryHistory radiusLedger ∧ UnaryHistory meshRead ∧
                    UnaryHistory sourceLock ∧ Cont window radius radiusLedger ∧
                      Cont radiusLedger mesh meshRead ∧ Cont meshRead route sourceLock := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier windowRadius radiusMesh meshRoute sourcePkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have radiusLedgerUnary : UnaryHistory radiusLedger :=
    unary_cont_closed windowUnary radiusUnary windowRadius
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed radiusLedgerUnary meshUnary radiusMesh
  have sourceUnary : UnaryHistory sourceLock :=
    unary_cont_closed meshReadUnary routeUnary meshRoute
  have sourceLockCarrier :
      (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row) sourceLock := by
    exact ⟨hsame_refl sourceLock, sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceLock ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row radiusLedger ∨ hsame row sourceLock)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle sourceLock pkg ∧
              hsame row sourceLock)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sourceLock sourceLockCarrier
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, sourcePkg, source.left⟩
    }
  exact
    ⟨cert, windowUnary, radiusUnary, meshUnary, radiusLedgerUnary, meshReadUnary,
      sourceUnary, windowRadius, radiusMesh, meshRoute⟩

end BEDC.Derived.FiniteLebesgueNumberUp
