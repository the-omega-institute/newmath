import BEDC.Real.ZetaCertDy
import BEDC.Derived.RHRoute.EulerHasseRegroup

set_option autoImplicit false

namespace BEDC
namespace ZetaCert
namespace Hasse24

def den24 : Int :=
  16777216

def coeffNum24 : Array Int :=
  #[
    16777215, -16777191, 16776915, -16774891,
    16764265, -16721761, 16587165, -16241061,
    15505590, -14198086, 12236830, -9740686,
    7036530, -4540386, 2579130, -1271626,
    536155, -190051, 55455, -12951,
    2325, -301, 25, -1
  ]

def coeff24N (i : Nat) : Dy.I :=
  Dy.pointM ((coeffNum24.getD i 0) * Dy.two72)

def pow2 : Nat -> Int
  | 0 => 1
  | Nat.succ n => 2 * pow2 n

def binom : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, Nat.succ k => binom n k + binom n (Nat.succ k)

def sumRange (lo len : Nat) (f : Nat -> Int) : Int :=
  match len with
  | 0 => 0
  | Nat.succ n => f lo + sumRange (lo + 1) n f

def coeffNumGen (M m : Nat) : Int :=
  let k := m - 1
  let raw :=
    sumRange k (M - k) (fun n =>
      ((binom n k : Nat) : Int) * pow2 (M - 1 - n))
  if k % 2 = 0 then raw else -raw

def coeffNum24List : List Int :=
  coeffNum24.toList

def coeffNum24GenList : List Int :=
  List.map (fun i => coeffNumGen 24 (i + 1)) (List.range 24)

theorem coeffNum24_size :
    coeffNum24.size = 24 := by
  decide

theorem coeffNum24_eq_gen_list :
    coeffNum24List = coeffNum24GenList := by
  decide

theorem den24_pos : (0 : Int) < den24 := by
  decide

theorem den24_pow2 :
    den24 = pow2 24 := by
  decide

theorem dy_scale_factor :
    den24 * Dy.two72 = Dy.S := by
  decide

end Hasse24
end ZetaCert
end BEDC
