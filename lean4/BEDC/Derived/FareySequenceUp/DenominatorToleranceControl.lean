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

theorem FareySequenceDenominatorToleranceControl [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N denomRead toleranceRead approxRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont M L denomRead →
        Cont denomRead T toleranceRead →
          Cont toleranceRead G approxRead →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row denomRead ∨ hsame row toleranceRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row L ∨ hsame row T ∨ hsame row G ∨
                      hsame row denomRead ∨ hsame row toleranceRead ∨
                        hsame row approxRead ∨ hsame row N)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M L denomRead ∧
                      Cont denomRead T toleranceRead ∧ Cont toleranceRead G approxRead ∧
                        PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory denomRead ∧ UnaryHistory toleranceRead ∧
                  UnaryHistory approxRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier mediantLevelDenom denomToleranceRead toleranceGapApprox namedPkg
  obtain ⟨_bUnary, _aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    _wUnary, _rUnary, gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _provenancePkg⟩ := carrier
  have denomUnary : UnaryHistory denomRead :=
    unary_cont_closed mUnary lUnary mediantLevelDenom
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denomUnary tUnary denomToleranceRead
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed toleranceUnary gUnary toleranceGapApprox
  have sourceDenom :
      (fun row : BHist =>
        (hsame row denomRead ∨ hsame row toleranceRead) ∧ UnaryHistory row) denomRead := by
    exact ⟨Or.inl (hsame_refl denomRead), denomUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row denomRead ∨ hsame row toleranceRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row L ∨ hsame row T ∨ hsame row G ∨
              hsame row denomRead ∨ hsame row toleranceRead ∨ hsame row approxRead ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M L denomRead ∧ Cont denomRead T toleranceRead ∧
              Cont toleranceRead G approxRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denomRead sourceDenom
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
        constructor
        · cases source.left with
          | inl sameDenom =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDenom)
          | inr sameTolerance =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameTolerance)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDenom =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDenom))))
      | inr sameTolerance =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTolerance)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, mediantLevelDenom, denomToleranceRead, toleranceGapApprox, namedPkg⟩
  }
  exact ⟨cert, denomUnary, toleranceUnary, approxUnary⟩

end BEDC.Derived.FareySequenceUp
