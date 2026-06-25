import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_cauchy_refusal_link [AskSetup] [PackageSetup]
    {e a t v h c p n cauchyRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a v ->
        Cont v h refusalRead ->
          Cont refusalRead c cauchyRead ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle cauchyRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row v ∨ hsame row refusalRead ∨ hsame row cauchyRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle cauchyRead pkg ∧
                        PkgSig bundle n pkg)
                    hsame ∧
                  UnaryHistory cauchyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier eAV vHRefusal refusalCCauchy _refusalPkg cauchyPkg
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, _pPkg, nPkg, _hN⟩ := carrier
  have vUnary : UnaryHistory v :=
    unary_cont_closed eUnary aUnary eAV
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed refusalUnary cUnary refusalCCauchy
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row v ∨ hsame row refusalRead ∨ hsame row cauchyRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle cauchyRead pkg ∧ PkgSig bundle n pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro cauchyRead
          (And.intro (hsame_refl cauchyRead) cauchyUnary)
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact And.intro source.right (And.intro cauchyPkg nPkg)
    }
  exact And.intro cert cauchyUnary

end BEDC.Derived.QuotientSoundnessBoundaryUp
