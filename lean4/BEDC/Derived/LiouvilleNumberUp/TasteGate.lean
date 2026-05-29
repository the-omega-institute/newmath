import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LiouvilleNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LiouvilleNumberUp : Type where
  | mk (Q D S R A E H C P N : BHist) : LiouvilleNumberUp
  deriving DecidableEq

def liouvilleNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: liouvilleNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: liouvilleNumberEncodeBHist h

def liouvilleNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (liouvilleNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (liouvilleNumberDecodeBHist tail)

private theorem LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def liouvilleNumberToEventFlow : LiouvilleNumberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LiouvilleNumberUp.mk Q D S R A E H C P N =>
      [liouvilleNumberEncodeBHist Q,
        liouvilleNumberEncodeBHist D,
        liouvilleNumberEncodeBHist S,
        liouvilleNumberEncodeBHist R,
        liouvilleNumberEncodeBHist A,
        liouvilleNumberEncodeBHist E,
        liouvilleNumberEncodeBHist H,
        liouvilleNumberEncodeBHist C,
        liouvilleNumberEncodeBHist P,
        liouvilleNumberEncodeBHist N]

def liouvilleNumberFromEventFlow : EventFlow → Option LiouvilleNumberUp
  -- BEDC touchpoint anchor: BHist BMark
  | Q :: D :: S :: R :: A :: E :: H :: C :: P :: N :: [] =>
      some
        (LiouvilleNumberUp.mk
          (liouvilleNumberDecodeBHist Q)
          (liouvilleNumberDecodeBHist D)
          (liouvilleNumberDecodeBHist S)
          (liouvilleNumberDecodeBHist R)
          (liouvilleNumberDecodeBHist A)
          (liouvilleNumberDecodeBHist E)
          (liouvilleNumberDecodeBHist H)
          (liouvilleNumberDecodeBHist C)
          (liouvilleNumberDecodeBHist P)
          (liouvilleNumberDecodeBHist N))
  | _ => none

private theorem LiouvilleNumberTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LiouvilleNumberUp,
      liouvilleNumberFromEventFlow (liouvilleNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk Q D S R A E H C P N =>
      change
        some
          (LiouvilleNumberUp.mk
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist Q))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist D))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist S))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist R))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist A))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist E))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist H))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist C))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist P))
            (liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist N))) =
          some (LiouvilleNumberUp.mk Q D S R A E H C P N)
      rw [LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode Q,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode D,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode S,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode R,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode A,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode E,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode H,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode C,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode P,
        LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode N]

private theorem LiouvilleNumberTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LiouvilleNumberUp} :
    liouvilleNumberToEventFlow x = liouvilleNumberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      liouvilleNumberFromEventFlow (liouvilleNumberToEventFlow x) =
        liouvilleNumberFromEventFlow (liouvilleNumberToEventFlow y) :=
    congrArg liouvilleNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LiouvilleNumberTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LiouvilleNumberTasteGate_single_carrier_alignment_round_trip y)))

instance liouvilleNumberBHistCarrier : BHistCarrier LiouvilleNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := liouvilleNumberToEventFlow
  fromEventFlow := liouvilleNumberFromEventFlow

instance liouvilleNumberChapterTasteGate : ChapterTasteGate LiouvilleNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change liouvilleNumberFromEventFlow (liouvilleNumberToEventFlow x) = some x
    exact LiouvilleNumberTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LiouvilleNumberTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LiouvilleNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist, liouvilleNumberDecodeBHist (liouvilleNumberEncodeBHist h) = h) ∧
      liouvilleNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨LiouvilleNumberTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.LiouvilleNumberUp
