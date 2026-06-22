import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyCofinalModulusUp : Type where
  | mk
      (source cofinal modulus tolerance window readback realSeal transport replay provenance name :
        BHist) :
      RegularCauchyCofinalModulusUp
  deriving DecidableEq

namespace RegularCauchyCofinalModulusUp

def rows : RegularCauchyCofinalModulusUp -> List BHist
  | mk source cofinal modulus tolerance window readback realSeal transport replay provenance name =>
      [source, cofinal, modulus, tolerance, window, readback, realSeal, transport, replay,
        provenance, name]

theorem rows_length (x : RegularCauchyCofinalModulusUp) : (rows x).length = 11 := by
  cases x
  rfl

end RegularCauchyCofinalModulusUp

end BEDC.Derived
