import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryFormalTargetFrontier [AskSetup] [PackageSetup]
    {e a t v h c p n refusal replacement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont e a v →
        Cont v h refusal →
          Cont h c replacement →
            PkgSig bundle refusal pkg →
              PkgSig bundle replacement pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ∧
                      (hsame row refusal ∨ hsame row replacement))
                  (fun row : BHist =>
                    Cont e a v ∧ (Cont v h row ∨ Cont h c row))
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle refusal pkg ∨ PkgSig bundle replacement pkg))
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier eAV vHRefusal hCReplacement refusalPkg replacementPkg
  have carrierWitness :
      QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg := carrier
  obtain ⟨eUnary, aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, _nUnary,
    _carrierEAV, _eTH, _hCN, _pPkg, _nPkg, _hN⟩ := carrier
  have vUnary : UnaryHistory v := unary_cont_closed eUnary aUnary eAV
  have refusalUnary : UnaryHistory refusal := unary_cont_closed vUnary hUnary vHRefusal
  have replacementUnary : UnaryHistory replacement :=
    unary_cont_closed hUnary cUnary hCReplacement
  exact {
    core := {
      carrier_inhabited := Exists.intro refusal
        (And.intro carrierWitness (Or.inl (hsame_refl refusal)))
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
        cases source.right with
        | inl rowRefusal =>
            exact And.intro source.left
              (Or.inl (hsame_trans (hsame_symm sameRows) rowRefusal))
        | inr rowReplacement =>
            exact And.intro source.left
              (Or.inr (hsame_trans (hsame_symm sameRows) rowReplacement))
    }
    pattern_sound := by
      intro row source
      cases source.right with
      | inl rowRefusal =>
          exact And.intro eAV
            (Or.inl (cont_result_hsame_transport vHRefusal (hsame_symm rowRefusal)))
      | inr rowReplacement =>
          exact And.intro eAV
            (Or.inr (cont_result_hsame_transport hCReplacement
              (hsame_symm rowReplacement)))
    ledger_sound := by
      intro row source
      cases source.right with
      | inl rowRefusal =>
          exact And.intro (unary_transport refusalUnary (hsame_symm rowRefusal))
            (Or.inl refusalPkg)
      | inr rowReplacement =>
          exact And.intro (unary_transport replacementUnary (hsame_symm rowReplacement))
            (Or.inr replacementPkg)
  }

end BEDC.Derived.QuotientSoundnessBoundaryUp
