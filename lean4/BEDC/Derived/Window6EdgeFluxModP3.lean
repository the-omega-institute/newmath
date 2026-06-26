namespace BEDC.Derived.Window6EdgeFluxModP3

/--
Finite integer certificate for the Window6 edge-flux matrix
`[[28, 63, 23, 20], [63, 21, 21, 6], [23, 21, 2, 6], [20, 6, 6, 2]]`.

The determinant is divisible by `3` and by `9`; the characteristic polynomial
also vanishes at zero modulo `3`.  This is the arithmetic certificate that the
edge-flux matrix is singular over `F_3`, giving the finite basis for the
mod-three left-kernel obstruction.  The Smith normal form
`diag(1, 1, 3, 3450)` is not formalized here; only its determinant product
consistency is recorded.
-/

def det3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : Int) : Int :=
  a11 * (a22 * a33 - a23 * a32)
    - a12 * (a21 * a33 - a23 * a31)
    + a13 * (a21 * a32 - a22 * a31)

def det4
    (a11 a12 a13 a14
      a21 a22 a23 a24
      a31 a32 a33 a34
      a41 a42 a43 a44 : Int) : Int :=
  a11 * det3 a22 a23 a24 a32 a33 a34 a42 a43 a44
    - a12 * det3 a21 a23 a24 a31 a33 a34 a41 a43 a44
    + a13 * det3 a21 a22 a24 a31 a32 a34 a41 a42 a44
    - a14 * det3 a21 a22 a23 a31 a32 a33 a41 a42 a43

def detE : Int :=
  det4 28 63 23 20
    63 21 21 6
    23 21 2 6
    20 6 6 2

theorem det_E : detE = 10350 := by
  decide

theorem det_factorization : (10350 : Int) = 2 * 3 ^ 2 * 5 ^ 2 * 23 := by
  decide

theorem det_mod_3 : (10350 : Int) % 3 = 0 := by
  decide

theorem det_divisible_by_3 : (3 : Int) ∣ 10350 := by
  exact ⟨3450, by decide⟩

theorem det_mod_9 : (10350 : Int) % 9 = 0 := by
  decide

theorem invariant_factor_product : (1 * 1 * 3 * 3450 : Int) = 10350 := by
  decide

def chiE (t : Int) : Int :=
  t ^ 4 - 53 * t ^ 3 - 4623 * t ^ 2 - 32241 * t + 10350

theorem chiE_zero : chiE 0 = 10350 := by
  rfl

theorem chiE_zero_mod_3 : chiE 0 % 3 = 0 := by
  decide

theorem detE_mod_3 : detE % 3 = 0 := by
  decide

theorem edge_flux_mod3_singular : detE % 3 = 0 ∧ chiE 0 % 3 = 0 := by
  exact ⟨detE_mod_3, chiE_zero_mod_3⟩

end BEDC.Derived.Window6EdgeFluxModP3
