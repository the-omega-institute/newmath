namespace BEDC.Derived.Window6ModP571Singularity

/--
Finite integer certificate for the Window6 reduced Laplacian
`[[106, -63, -23], [-63, 90, -21], [-23, -21, 50]]`.

The determinant vanishes modulo 571, while the derivative of the characteristic
polynomial at zero is nonzero modulo 571.  Thus the modular zero eigenvalue is
certified by the simple-root test, not by a repeated-root collision.
-/

def det3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : Int) : Int :=
  a11 * (a22 * a33 - a23 * a32)
    - a12 * (a21 * a33 - a23 * a31)
    + a13 * (a21 * a32 - a22 * a31)

def detLr : Int :=
  det3 106 (-63) (-23)
    (-63) 90 (-21)
    (-23) (-21) 50

theorem det_Lr : detLr = 123336 := by
  decide

theorem det_factorization : (123336 : Int) = 2 ^ 3 * 3 ^ 3 * 571 := by
  decide

theorem det_mod_571 : (123336 : Int) % 571 = 0 := by
  decide

theorem det_divisible_by_571 : (571 : Int) ∣ 123336 := by
  exact ⟨216, by decide⟩

def chiL (t : Int) : Int :=
  t ^ 3 - 246 * t ^ 2 + 14401 * t - 123336

def chiLderiv (t : Int) : Int :=
  3 * t ^ 2 - 492 * t + 14401

theorem chiL_zero : chiL 0 = -123336 := by
  decide

theorem chiL_zero_mod_571 : chiL 0 % 571 = 0 := by
  decide

theorem chiL_t_coeff : chiLderiv 0 = 14401 := by
  decide

theorem chiLderiv_zero_mod_571 : chiLderiv 0 % 571 = 126 := by
  decide

theorem chiLderiv_zero_ne_zero_mod_571 : chiLderiv 0 % 571 ≠ 0 := by
  decide

theorem simple_modular_zero_not_repeated :
    chiL 0 % 571 = 0 ∧ chiLderiv 0 % 571 ≠ 0 := by
  exact ⟨chiL_zero_mod_571, chiLderiv_zero_ne_zero_mod_571⟩

end BEDC.Derived.Window6ModP571Singularity
