import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_carrier_exposure [AskSetup] [PackageSetup]
    {e a t v h c p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧ hsame row n)
          (fun row : BHist =>
            hsame row e ∨ hsame row a ∨ hsame row t ∨ hsame row v ∨ hsame row h ∨
              hsame row c ∨ hsame row p ∨ hsame row n)
          (fun row : BHist => PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧ hsame row n)
          hsame ∧
        UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
          UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
            Cont e a v ∧ Cont e t h ∧ Cont h c n ∧ PkgSig bundle p pkg ∧
              PkgSig bundle n pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, pUnary, nUnary, eAV,
    eTH, hCN, pPkg, nPkg, hN⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧ hsame row n)
        (fun row : BHist =>
          hsame row e ∨ hsame row a ∨ hsame row t ∨ hsame row v ∨ hsame row h ∨
            hsame row c ∨ hsame row p ∨ hsame row n)
        (fun row : BHist => PkgSig bundle p pkg ∧ PkgSig bundle n pkg ∧ hsame row n)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro n ⟨carrierWitness, hsame_refl n⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))))
      ledger_sound := by
        intro _row source
        exact ⟨pPkg, nPkg, source.right⟩
    }
  exact
    ⟨cert, eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, pUnary, nUnary, eAV, eTH,
      hCN, pPkg, nPkg, hN⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
