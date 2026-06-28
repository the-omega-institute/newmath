import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived.HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_separated_quotient_row
    {P S M C W R E T K G N quotientRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N ->
      Cont P S quotientRead ->
        SemanticNameCert
            (fun row : BHist => hsame row quotientRead /\ UnaryHistory row)
            (fun row : BHist =>
              hsame row P \/ hsame row S \/ hsame row W \/ hsame row R \/
                hsame row E \/ hsame row quotientRead)
            (fun row : BHist =>
              UnaryHistory row /\ HausdorffizationCarrier P S M C W R E T K G N /\
                Cont P S quotientRead)
            hsame /\ UnaryHistory quotientRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData quotientRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨pUnary, sUnary, _mUnary, _cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, _gUnary, _nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have quotientUnary : UnaryHistory quotientRead :=
    unary_cont_closed pUnary sUnary quotientRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row quotientRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row P \/ hsame row S \/ hsame row W \/ hsame row R \/
              hsame row E \/ hsame row quotientRead)
          (fun row : BHist =>
            UnaryHistory row /\ HausdorffizationCarrier P S M C W R E T K G N /\
              Cont P S quotientRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro quotientRead ⟨hsame_refl quotientRead, quotientUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, quotientRoute⟩
  }
  exact ⟨cert, quotientUnary⟩

end BEDC.Derived.HausdorffizationUp
