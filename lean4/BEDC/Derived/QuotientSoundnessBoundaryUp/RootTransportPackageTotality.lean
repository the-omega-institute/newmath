import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_root_transport_package_totality
    [AskSetup] [PackageSetup]
    {e a t v h c p n transportRead packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont t h transportRead →
        Cont transportRead c packageRead →
          PkgSig bundle transportRead pkg →
            PkgSig bundle packageRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                    hsame row packageRead)
                (fun row : BHist =>
                  Cont e a v ∧ Cont e t h ∧ Cont t h transportRead ∧
                    Cont transportRead c row)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle transportRead pkg ∧
                    PkgSig bundle packageRead pkg ∧ hsame h n)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier transportRoute packageRoute transportPkg packagePkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨_eUnary, _aUnary, tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    eAV, eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed tUnary hUnary transportRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed transportUnary cUnary packageRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro packageRead
        (And.intro carrierWitness (hsame_refl packageRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨eAV, eTH, transportRoute,
          cont_result_hsame_transport packageRoute (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport packageUnary (hsame_symm source.right), transportPkg,
          packagePkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
