import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactConsumerNonchoiceBoundary [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead route totalRead ->
          PkgSig bundle totalRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
                    hsame row compactRead ∨ hsame row totalRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg ∧
                    hsame row totalRead)
                hsame ∧
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory mesh ∧ UnaryHistory compactRead ∧ UnaryHistory totalRead ∧
                  Cont cover window radius ∧ Cont radius mesh compactRead ∧
                    Cont compactRead route totalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier radiusMeshCompact compactRouteTotal totalReadPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, compactUnary, totalUnary,
    coverWindowRadius, radiusCompactRoute, compactTotalRoute, provenancePkg,
    totalPackage⟩ :=
    FiniteLebesgueNumberCarrier_total_bounded_handoff carrier radiusMeshCompact
      compactRouteTotal totalReadPkg
  have sourceTotal :
      (fun row : BHist => hsame row totalRead ∧ UnaryHistory row) totalRead := by
    exact ⟨hsame_refl totalRead, totalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row compactRead ∨ hsame row totalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle totalRead pkg ∧
              hsame row totalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro totalRead sourceTotal
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
      exact ⟨provenancePkg, totalPackage, source.left⟩
  }
  exact
    ⟨cert, coverUnary, windowUnary, radiusUnary, meshUnary, compactUnary, totalUnary,
      coverWindowRadius, radiusCompactRoute, compactTotalRoute⟩

end BEDC.Derived.FiniteLebesgueNumberUp
