import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusUp_StdBridge [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg →
      UnaryHistory pointwise →
        Cont bundleRow radius compactRead →
          Cont compactRead pointwise pointwiseRead →
            Cont pointwiseRead transport exported →
              PkgSig bundle exported pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row exported ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    Cont pointwiseRead transport row ∧ Cont bundleRow radius compactRead)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧ Cont compactRead pointwise pointwiseRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet pointwiseUnary compactRoute pointwiseRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, _precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    coverageRoute, transportRoute, _precisionRadiusFoldLedger, _foldNameProvenance,
    _provenancePkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary coverageRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed coverageUnary pointwiseUnary transportRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed pointwiseReadUnary transportUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm source.left), compactRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, pointwiseRoute⟩
  }

end BEDC.Derived.UniformModulusUp
