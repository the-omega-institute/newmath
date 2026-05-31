import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BolzanoWeierstrassCarrier_ledger_refusal [AskSetup] [PackageSetup]
    {S K R Q E H C P N refusedLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      PkgSig bundle refusedLedger pkg →
        SemanticNameCert
          (fun row : BHist =>
            hsame row refusedLedger ∧
              BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ Cont H C P)
          (fun row : BHist =>
            hsame row refusedLedger ∧ PkgSig bundle P pkg ∧
              PkgSig bundle refusedLedger pkg)
          hsame ∧ Cont H C P ∧ PkgSig bundle P pkg ∧
            PkgSig bundle refusedLedger pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier refusedPkg
  have carrierWitness :
      BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg := carrier
  obtain ⟨_SUnary, _KUnary, _RUnary, _QUnary, _EUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceIntervalRoute, _readbackSealRoute,
    transportReplayRoute, carrierPkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row refusedLedger ∧
            BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
        (fun row : BHist =>
          hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
            hsame row E ∨ Cont H C P)
        (fun row : BHist =>
          hsame row refusedLedger ∧ PkgSig bundle P pkg ∧
            PkgSig bundle refusedLedger pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedLedger ⟨hsame_refl refusedLedger, carrierWitness⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr transportReplayRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, carrierPkg, refusedPkg⟩
  }
  exact ⟨cert, transportReplayRoute, carrierPkg, refusedPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
