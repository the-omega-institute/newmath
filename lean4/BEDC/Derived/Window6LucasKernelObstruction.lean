import BEDC.Derived.Window6TransferMatrix
import BEDC.Derived.Window6LucasCount

namespace BEDC.Derived.Window6LucasKernelObstruction

/--
The Lucas-kernel obstruction is the matrix realization of the
minimal-polynomial relation `x^20 - 123*x^10 + 1 = 0` in
`Z[x]/(x^2 - x - 1)`, with `M = [[1,1],[1,0]]` the companion matrix.

它记录了 golden `phi^10`-spaced exponent slots 上的
Lucas-kernel `(1,-123,1)` 湮灭关系。The coefficient `123` is the Lucas
number `L_10`, certified below from the existing Lucas recurrence.
-/
def lucasKernelCombo : BEDC.Derived.Window6Transfer.Mat2 :=
  let A := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 20
  let B := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 10
  ⟨A.a - 123 * B.a + 1,
    A.b - 123 * B.b,
    A.c - 123 * B.c,
    A.d - 123 * B.d + 1⟩

theorem lucas_kernel_M_zero :
    lucasKernelCombo = ⟨0, 0, 0, 0⟩ := by
  decide

theorem lucas_coeff_eq_L10 :
    (BEDC.Derived.Window6Lucas.lucas 10 : Int) = 123 := by
  decide

/--
The same Lucas-kernel relation shifted to the Window6 seam slots
`7, 17, 27`.
-/
def seamSlotCombo : BEDC.Derived.Window6Transfer.Mat2 :=
  let C := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 27
  let D := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 17
  let E := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 7
  ⟨C.a - 123 * D.a + E.a,
    C.b - 123 * D.b + E.b,
    C.c - 123 * D.c + E.c,
    C.d - 123 * D.d + E.d⟩

theorem seam_slot_kernel_zero :
    seamSlotCombo = ⟨0, 0, 0, 0⟩ := by
  decide

def lucasKernelComboL10 : BEDC.Derived.Window6Transfer.Mat2 :=
  let A := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 20
  let B := BEDC.Derived.Window6Transfer.npow BEDC.Derived.Window6Transfer.M 10
  let L10 : Int := BEDC.Derived.Window6Lucas.lucas 10
  ⟨A.a - L10 * B.a + 1,
    A.b - L10 * B.b,
    A.c - L10 * B.c,
    A.d - L10 * B.d + 1⟩

theorem lucas_kernel_M_zero_L10 :
    lucasKernelComboL10 = ⟨0, 0, 0, 0⟩ := by
  decide

end BEDC.Derived.Window6LucasKernelObstruction
