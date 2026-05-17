import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_root_request_accountability [AskSetup] [PackageSetup]
    {e a t v h c p n rootDemand refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont e a rootDemand ->
        Cont v t refusalRead ->
          PkgSig bundle rootDemand pkg ->
            PkgSig bundle refusalRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                    Cont e a rootDemand ∧ Cont v t refusalRead ∧ hsame row refusalRead)
                (fun row : BHist =>
                  Cont e a rootDemand ∧ Cont v t row ∧ PkgSig bundle refusalRead pkg)
                (fun row : BHist =>
                  UnaryHistory row ∧ UnaryHistory e ∧ UnaryHistory a ∧
                    PkgSig bundle rootDemand pkg ∧ PkgSig bundle refusalRead pkg ∧ hsame h n)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier rootRequest vTRefusal rootPkg refusalPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, tUnary, vUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _eAV, _eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary tUnary vTRefusal
  exact {
    core := {
      carrier_inhabited := Exists.intro refusalRead
        (And.intro carrierWitness
          (And.intro rootRequest (And.intro vTRefusal (hsame_refl refusalRead))))
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
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.right.left,
          cont_result_hsame_transport vTRefusal (hsame_symm source.right.right.right),
          refusalPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport refusalUnary (hsame_symm source.right.right.right), eUnary, aUnary,
          rootPkg, refusalPkg, hN⟩
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
