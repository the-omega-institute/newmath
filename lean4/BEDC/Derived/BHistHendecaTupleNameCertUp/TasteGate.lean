import BEDC.Derived.BHistHendecaTupleNameCertUp

namespace BEDC.Derived.BHistHendecaTupleNameCertUp

open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem BHistHendecaTupleTagExhaustion (x : BHistHendecaTupleNameCertUp) :
    ∃ R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L : BHist,
      x = BHistHendecaTupleNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L ∧
        bHistHendecaTupleNameCertFields x =
          [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P L =>
      exact
        ⟨R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, H, C, P, L, rfl, rfl⟩

end BEDC.Derived.BHistHendecaTupleNameCertUp
