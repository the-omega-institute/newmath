import BEDC.Derived.CauchyOscillationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCompletionConsumerRefusal [AskSetup] [PackageSetup]
    {W M Q T S H C P N sourceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M sourceRead ->
        Cont sourceRead Q sealRead ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sourceRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                    hsame row S ∨ hsame row sourceRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧ (hsame row sourceRead ∨ hsame row sealRead))
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute sealRoute pkgSig
  obtain ⟨wUnary, mUnary, qUnary, _tUnary, _sUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _tailModulusTolerance, _modulusToleranceLedger, _ledgerSeal,
    _routesNameCert, _carrierPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed wUnary mUnary sourceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary qUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
              hsame row S ∨ hsame row sourceRead ∨ hsame row sealRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row sourceRead ∨ hsame row sealRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead (Or.inl (hsame_refl sourceRead))
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
        intro _row other sameRows source
        cases source with
        | inl sameSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
        | inr sameSeal =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSource)))))
      | inr sameSeal =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨pkgSig, source⟩
  }
  exact ⟨cert, sourceUnary, sealUnary⟩

end BEDC.Derived.CauchyOscillationUp
