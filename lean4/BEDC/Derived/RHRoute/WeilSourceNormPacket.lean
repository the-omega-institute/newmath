import BEDC.Derived.RHRoute.WeilPositivityRoute
import BEDC.Derived.RHRoute.IntervalMatrixPSD

set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.WeilSourceNormPacket

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.WeilPositivityRoute
open BEDC.Derived.RHRoute.IntervalMatrixPSD

abbrev Rat : Type := RatNum

def finiteRatSum : Nat -> (Nat -> Rat) -> Rat
  | 0, _f => ratZero
  | Nat.succ n, f => ratAdd (finiteRatSum n f) (f n)

def sourceDot (size : Nat) (v c : Nat -> Rat) : Rat :=
  finiteRatSum size (fun i => ratMul (v i) (c i))

structure SourceSquareTerm (size : Nat) where
  weight : Rat
  vectorAt : Nat -> Rat
  weight_nonnegative : ratLe ratZero weight

namespace SourceSquareTerm

def entry {size : Nat} (term : SourceSquareTerm size) (i j : Nat) : Rat :=
  ratMul term.weight (ratMul (term.vectorAt i) (term.vectorAt j))

def value {size : Nat} (term : SourceSquareTerm size) (coeff : Nat -> Rat) : Rat :=
  ratMul term.weight
    (ratMul (sourceDot size term.vectorAt coeff)
      (sourceDot size term.vectorAt coeff))

theorem value_nonnegative {size : Nat}
    (term : SourceSquareTerm size) (coeff : Nat -> Rat) :
    ratLe ratZero (term.value coeff) := by
  exact psd_1x1 term.weight (sourceDot size term.vectorAt coeff)
    term.weight_nonnegative

end SourceSquareTerm

structure SourceNormPacket (size : Nat) where
  terms : List (SourceSquareTerm size)

namespace SourceNormPacket

def value {size : Nat} (packet : SourceNormPacket size)
    (coeff : Nat -> Rat) : Rat :=
  ratListSum (packet.terms.map (fun term => term.value coeff))

theorem value_nonnegative {size : Nat}
    (packet : SourceNormPacket size) (coeff : Nat -> Rat) :
    ratLe ratZero (packet.value coeff) := by
  unfold value
  exact ratListSum_nonnegative
    (packet.terms.map (fun term => term.value coeff))
    (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨term, _hmem, rfl⟩
      exact SourceSquareTerm.value_nonnegative term coeff)

theorem readback_nonnegative {size : Nat}
    (packet : SourceNormPacket size) (coeff : Nat -> Rat)
    (matrixQuadratic : Rat)
    (readback : RatEq matrixQuadratic (packet.value coeff)) :
    ratLe ratZero matrixQuadratic := by
  have hpacket : ratLe ratZero (packet.value coeff) :=
    packet.value_nonnegative coeff
  exact ratLe_of_RatEq_right hpacket (RatEq_symm readback)

end SourceNormPacket

def unitSourceSquareTerm : SourceSquareTerm 1 where
  weight := ratOne
  vectorAt := fun _i => ratOne
  weight_nonnegative := ratOne_nonneg

def unitSourceNormPacket : SourceNormPacket 1 where
  terms := [unitSourceSquareTerm]

theorem unit_source_norm_packet_nonnegative (coeff : Nat -> Rat) :
    ratLe ratZero (unitSourceNormPacket.value coeff) := by
  exact SourceNormPacket.value_nonnegative unitSourceNormPacket coeff

end BEDC.Derived.RHRoute.WeilSourceNormPacket
