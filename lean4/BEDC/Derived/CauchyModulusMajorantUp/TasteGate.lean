import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusMajorantUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusMajorantUp : Type where
  | mk (A D S R E G H C P N : BHist) : CauchyModulusMajorantUp
  deriving DecidableEq

def cauchyModulusMajorantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusMajorantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusMajorantEncodeBHist h

def cauchyModulusMajorantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusMajorantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusMajorantDecodeBHist tail)

private theorem CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyModulusMajorantDecodeBHist
        (cauchyModulusMajorantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusMajorantFields : CauchyModulusMajorantUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusMajorantUp.mk A D S R E G H C P N =>
      [A, D, S, R, E, G, H, C, P, N]

def cauchyModulusMajorantToEventFlow : CauchyModulusMajorantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusMajorantFields x).map cauchyModulusMajorantEncodeBHist

def cauchyModulusMajorantFromEventFlow : EventFlow → Option CauchyModulusMajorantUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: D :: S :: R :: E :: G :: H :: C :: P :: N :: [] =>
      some
        (CauchyModulusMajorantUp.mk
          (cauchyModulusMajorantDecodeBHist A)
          (cauchyModulusMajorantDecodeBHist D)
          (cauchyModulusMajorantDecodeBHist S)
          (cauchyModulusMajorantDecodeBHist R)
          (cauchyModulusMajorantDecodeBHist E)
          (cauchyModulusMajorantDecodeBHist G)
          (cauchyModulusMajorantDecodeBHist H)
          (cauchyModulusMajorantDecodeBHist C)
          (cauchyModulusMajorantDecodeBHist P)
          (cauchyModulusMajorantDecodeBHist N))
  | _ => none

private theorem CauchyModulusMajorantTasteGate_single_carrier_alignment_round_trip
    (x : CauchyModulusMajorantUp) :
    cauchyModulusMajorantFromEventFlow
      (cauchyModulusMajorantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A D S R E G H C P N =>
      change
        some
          (CauchyModulusMajorantUp.mk
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist A))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist D))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist S))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist R))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist E))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist G))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist H))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist C))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist P))
            (cauchyModulusMajorantDecodeBHist (cauchyModulusMajorantEncodeBHist N))) =
          some (CauchyModulusMajorantUp.mk A D S R E G H C P N)
      rw [CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode A,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode S,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode E,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode G,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyModulusMajorantTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusMajorantUp} :
    cauchyModulusMajorantToEventFlow x =
      cauchyModulusMajorantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusMajorantFromEventFlow
          (cauchyModulusMajorantToEventFlow x) =
        cauchyModulusMajorantFromEventFlow
          (cauchyModulusMajorantToEventFlow y) :=
    congrArg cauchyModulusMajorantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyModulusMajorantTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusMajorantTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyModulusMajorantBHistCarrier : BHistCarrier CauchyModulusMajorantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusMajorantToEventFlow
  fromEventFlow := cauchyModulusMajorantFromEventFlow

instance cauchyModulusMajorantChapterTasteGate :
    ChapterTasteGate CauchyModulusMajorantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusMajorantFromEventFlow
        (cauchyModulusMajorantToEventFlow x) = some x
    exact CauchyModulusMajorantTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyModulusMajorantTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusMajorantUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusMajorantChapterTasteGate

theorem CauchyModulusMajorantTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusMajorantDecodeBHist
        (cauchyModulusMajorantEncodeBHist h) = h) ∧
      (∀ A D S R E G H C P N : BHist,
        cauchyModulusMajorantFields
          (CauchyModulusMajorantUp.mk A D S R E G H C P N) =
            [A, D, S, R, E, G, H, C, P, N]) ∧
        cauchyModulusMajorantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyModulusMajorantTasteGate_single_carrier_alignment_decode_encode,
      (fun _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.CauchyModulusMajorantUp.TasteGate
