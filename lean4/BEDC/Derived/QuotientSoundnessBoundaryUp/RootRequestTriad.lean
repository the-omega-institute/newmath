import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_root_request_triad [AskSetup] [PackageSetup]
    {e a t v h c p n rootDemand : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a rootDemand ->
        PkgSig bundle rootDemand pkg ->
          SemanticNameCert
            (fun row : BHist =>
              QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                hsame row rootDemand)
            (fun row : BHist => Cont e a row ∧ PkgSig bundle rootDemand pkg)
            (fun row : BHist =>
              UnaryHistory row ∧ UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory v ∧
                hsame h n)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier rootRequest rootPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, _tUnary, vUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have rootUnary : UnaryHistory rootDemand :=
    unary_cont_closed eUnary aUnary rootRequest
  exact {
    core := {
      carrier_inhabited := Exists.intro rootDemand
        (And.intro carrierWitness (hsame_refl rootDemand))
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
      exact And.intro (cont_result_hsame_transport rootRequest (hsame_symm source.right))
        rootPkg
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport rootUnary (hsame_symm source.right), eUnary, aUnary, vUnary, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
