import BEDC.Algebra.FiniteFold
import BEDC.Derived.BernoulliUp
import BEDC.Derived.RHRoute.FinitePrimeWindow

namespace BEDC.Derived.RHRoute.UnitaryBalance

open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RationalUp

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

structure PrimeLocalChannel where
  window : PrimeWindow
  amp_num : Nat -> Int
  amp_den : Nat -> Nat
  den_pos : (p : Nat) -> window.mem p -> 0 < amp_den p
  supported : (p : Nat) -> Not (window.mem p) -> amp_num p = 0

def channelAmplitude (C : PrimeLocalChannel) (p : Nat) : RatNum :=
  BEDC.Derived.BernoulliUp.ratOfIntOverNat (C.amp_num p) (C.amp_den p - 1)

def channelAmplitudeSq (C : PrimeLocalChannel) (p : Nat) : RatNum :=
  ratMul (channelAmplitude C p) (channelAmplitude C p)

def ratListSum : List RatNum -> RatNum
  | [] => ratZero
  | x :: xs => ratAdd x (ratListSum xs)

def squaredNormOnWindow (C : PrimeLocalChannel) : RatNum :=
  ratListSum (List.map (channelAmplitudeSq C) C.window.elems)

structure UnitaryBalanceSurface where
  channel : PrimeLocalChannel
  norm_one : RatEq (squaredNormOnWindow channel) ratOne

theorem channel_supported_off_window (C : PrimeLocalChannel) (p : Nat) :
    Not (C.window.mem p) -> C.amp_num p = 0 := by
  intro outside
  exact C.supported p outside

def singlePrimeWindow : PrimeWindow where
  elems := [2]
  nodup := NoDup.cons (by intro member; cases member) NoDup.nil
  all_prime := All.cons
    BEDC.Derived.PrimeUp.NatPrime_first_pair.left
    All.nil

def singlePrimeChannel : PrimeLocalChannel where
  window := singlePrimeWindow
  amp_num := fun p => if p = 2 then 1 else 0
  amp_den := fun _p => 1
  den_pos := by
    intro _p _member
    exact Nat.succ_pos 0
  supported := by
    intro p outside
    by_cases hp : p = 2
    · have member : singlePrimeWindow.mem p := by
        unfold singlePrimeWindow PrimeWindow.mem
        exact hp.symm ▸ List.Mem.head []
      exact False.elim (outside member)
    · exact if_neg hp

theorem singlePrimeChannel_supported (p : Nat) :
    Not (singlePrimeChannel.window.mem p) -> singlePrimeChannel.amp_num p = 0 := by
  intro outside
  exact singlePrimeChannel.supported p outside

theorem singlePrimeChannel_den_pos (p : Nat) :
    singlePrimeChannel.window.mem p -> 0 < singlePrimeChannel.amp_den p := by
  intro member
  exact singlePrimeChannel.den_pos p member

theorem singlePrimeChannel_squaredNorm :
    RatEq (squaredNormOnWindow singlePrimeChannel) ratOne := by
  exact RatEq_refl ratOne

def singlePrimeUnitaryBalanceSurface : UnitaryBalanceSurface where
  channel := singlePrimeChannel
  norm_one := singlePrimeChannel_squaredNorm

theorem singlePrimeUnitaryBalanceSurface_norm_one :
    RatEq (squaredNormOnWindow singlePrimeUnitaryBalanceSurface.channel) ratOne :=
  singlePrimeUnitaryBalanceSurface.norm_one

end BEDC.Derived.RHRoute.UnitaryBalance
