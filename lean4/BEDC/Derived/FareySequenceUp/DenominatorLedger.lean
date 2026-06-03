import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_denominator_ledger [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N denominatorRead streamRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont L T denominatorRead ->
        Cont denominatorRead W streamRead ->
          Cont streamRead R regularRead ->
            SemanticNameCert
                (fun row : BHist => hsame row denominatorRead ∨ hsame row regularRead)
                (fun row : BHist =>
                  hsame row L ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
                    hsame row denominatorRead ∨ hsame row streamRead ∨
                      hsame row regularRead)
                (fun row : BHist =>
                  PkgSig bundle P pkg ∧
                    (hsame row denominatorRead ∨ hsame row regularRead))
                hsame ∧
              UnaryHistory denominatorRead ∧ UnaryHistory streamRead ∧
                UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier denominatorRoute streamRoute regularRoute
  obtain ⟨_bUnary, _aUnary, _mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    wUnary, rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have denominatorUnary : UnaryHistory denominatorRead :=
    unary_cont_closed lUnary tUnary denominatorRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed denominatorUnary wUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary rUnary regularRoute
  have sourceDenominator :
      (fun row : BHist => hsame row denominatorRead ∨ hsame row regularRead)
          denominatorRead := by
    exact Or.inl (hsame_refl denominatorRead)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denominatorRead ∨ hsame row regularRead)
          (fun row : BHist =>
            hsame row L ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
              hsame row denominatorRead ∨ hsame row streamRead ∨ hsame row regularRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧
              (hsame row denominatorRead ∨ hsame row regularRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denominatorRead sourceDenominator
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameDenominator =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDenominator))))
      | inr sameRegular =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRegular)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source⟩
  }
  exact ⟨cert, denominatorUnary, streamUnary, regularUnary⟩

end BEDC.Derived.FareySequenceUp
