import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive BHistHendecaEventFlowNameCertUp : Type where
  | mk (R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P N : FKernel.Hist.BHist) :
      BHistHendecaEventFlowNameCertUp
  deriving DecidableEq

namespace BHistHendecaEventFlowNameCertUp

open BEDC.FKernel.Hist

def fields : BEDC.Derived.BHistHendecaEventFlowNameCertUp -> List BHist
  | BHistHendecaEventFlowNameCertUp.mk R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H C P N =>
      [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, H, C, P, N]

theorem fields_faithful :
    forall x y : BHistHendecaEventFlowNameCertUp, fields x = fields y -> x = y := by
  intro x y hfields
  cases x with
  | mk R01 R11 R21 R31 R41 R51 R61 R71 R81 R91 R101 H1 C1 P1 N1 =>
      cases y with
      | mk R02 R12 R22 R32 R42 R52 R62 R72 R82 R92 R102 H2 C2 P2 N2 =>
          cases hfields
          rfl

theorem eleven_event_rows_visible :
    forall x : BHistHendecaEventFlowNameCertUp, (fields x).length = 15 := by
  intro x
  cases x
  rfl

end BEDC.Derived.BHistHendecaEventFlowNameCertUp
