import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_stream_window_stability [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N windowRead regularRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B W windowRead ->
        Cont windowRead R regularRead ->
          Cont regularRead E sealedRead ->
            PkgSig bundle sealedRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row windowRead ∨ hsame row regularRead ∨ hsame row sealedRead)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row R ∨
                      hsame row E ∨ hsame row windowRead ∨ hsame row sealedRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ (hsame row windowRead ∨ hsame row sealedRead))
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute sealedRoute _sealedPkg
  obtain ⟨bUnary, _aUnary, _mUnary, _lUnary, _tUnary, _sUnary, _dUnary, _qUnary,
    wUnary, rUnary, _gUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary eUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row windowRead ∨ hsame row regularRead ∨ hsame row sealedRead)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row windowRead ∨ hsame row sealedRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ (hsame row windowRead ∨ hsame row sealedRead))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro windowRead (Or.inl (hsame_refl windowRead))
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
        | inl sameWindow =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameWindow)
        | inr rest =>
            cases rest with
            | inl sameRegular =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRegular))
            | inr sameSealed =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSealed))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameWindow =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameWindow)))))
      | inr rest =>
          cases rest with
          | inl sameRegular =>
              have sameSealedRegular : hsame sealedRead regularRead := by
                cases _eEmpty
                exact cont_right_unit_result sealedRoute
              have sameRowSealed : hsame _row sealedRead :=
                hsame_trans sameRegular (hsame_symm sameSealedRegular)
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRowSealed)))))
          | inr sameSealed =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSealed)))))
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameWindow =>
          exact ⟨provenancePkg, Or.inl sameWindow⟩
      | inr rest =>
          cases rest with
          | inl sameRegular =>
              have sameSealedRegular : hsame sealedRead regularRead := by
                cases _eEmpty
                exact cont_right_unit_result sealedRoute
              have sameRowSealed : hsame _row sealedRead :=
                hsame_trans sameRegular (hsame_symm sameSealedRegular)
              exact ⟨provenancePkg, Or.inr sameRowSealed⟩
          | inr sameSealed =>
              exact ⟨provenancePkg, Or.inr sameSealed⟩
  }
  exact ⟨cert, windowUnary, regularUnary, sealedUnary⟩

end BEDC.Derived.FareySequenceUp
