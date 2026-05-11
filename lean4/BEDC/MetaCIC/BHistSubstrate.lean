import BEDC.FKernel.Hist

namespace BEDC.MetaCIC.BHistSubstrate

/-- BHist 上的自然数等价物。 -/
abbrev BHistIdx : Type := BEDC.FKernel.Hist.BHist

/-- BHist 长度作为 Nat，用来转换。 -/
def bhistLen : BHistIdx → Nat
  | BEDC.FKernel.Hist.BHist.Empty => 0
  | BEDC.FKernel.Hist.BHist.e0 rest => bhistLen rest + 1
  | BEDC.FKernel.Hist.BHist.e1 rest => bhistLen rest + 1

/-- Nat → BHist 的一元编码。 -/
def natToBHist : Nat → BHistIdx
  | 0 => BEDC.FKernel.Hist.BHist.Empty
  | n + 1 => BEDC.FKernel.Hist.BHist.e0 (natToBHist n)

theorem bhistLen_natToBHist (n : Nat) : bhistLen (natToBHist n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold natToBHist bhistLen
      rw [ih]

end BEDC.MetaCIC.BHistSubstrate
