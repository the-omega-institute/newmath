import BEDC.Derived.HausdorffizationUp

namespace BEDC.Derived

namespace HausdorffizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem HausdorffizationCarrier_namecert_scope_package
    {P S M C W R E T K G N nameRead : BHist} :
    HausdorffizationCarrier P S M C W R E T K G N →
      Cont G N nameRead →
        SemanticNameCert
            (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
                hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨
                  hsame row G ∨ hsame row N ∨ hsame row nameRead)
            (fun row : BHist =>
              UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
                Cont G N nameRead)
            hsame ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData nameRoute
  have carrierOriginal : HausdorffizationCarrier P S M C W R E T K G N := carrierData
  obtain ⟨_pUnary, _sUnary, _mUnary, _cUnary, _wUnary, _rUnary, _eUnary, _tUnary,
    _kUnary, gUnary, nUnary, _sourceRoute, _handoffRoute⟩ := carrierData
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed gUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row S ∨ hsame row M ∨ hsame row C ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row K ∨ hsame row G ∨
                hsame row N ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ HausdorffizationCarrier P S M C W R E T K G N ∧
              Cont G N nameRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierOriginal, nameRoute⟩
  }
  exact ⟨cert, nameUnary⟩

end HausdorffizationUp

end BEDC.Derived
