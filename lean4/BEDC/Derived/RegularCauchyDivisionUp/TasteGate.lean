import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDivisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDivisionUp : Type where
  | mk (X Y A I P W R E H C Q N : BHist) : RegularCauchyDivisionUp
  deriving DecidableEq

def regularCauchyDivisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDivisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDivisionEncodeBHist h

def regularCauchyDivisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDivisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDivisionDecodeBHist tail)

private theorem RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDivisionFields : RegularCauchyDivisionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDivisionUp.mk X Y A I P W R E H C Q N => [X, Y, A, I, P, W, R, E, H, C, Q, N]

def regularCauchyDivisionToEventFlow : RegularCauchyDivisionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyDivisionFields x).map regularCauchyDivisionEncodeBHist

private def regularCauchyDivisionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDivisionEventAtDefault index rest

def regularCauchyDivisionFromEventFlow (ef : EventFlow) :
    Option RegularCauchyDivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyDivisionUp.mk
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 0 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 1 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 2 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 3 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 4 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 5 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 6 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 7 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 8 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 9 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 10 ef))
      (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEventAtDefault 11 ef)))

private theorem RegularCauchyDivisionUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyDivisionUp,
      regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y A I P W R E H C Q N =>
      change
        some
          (RegularCauchyDivisionUp.mk
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist X))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist Y))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist A))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist I))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist P))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist W))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist R))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist E))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist H))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist C))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist Q))
            (regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist N))) =
          some (RegularCauchyDivisionUp.mk X Y A I P W R E H C Q N)
      rw [RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode X,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode Y,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode A,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode I,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode P,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode W,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode R,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode E,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode H,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode C,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode N]

private theorem regularCauchyDivisionToEventFlow_injective
    {x y : RegularCauchyDivisionUp} :
    regularCauchyDivisionToEventFlow x = regularCauchyDivisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) =
        regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow y) :=
    congrArg regularCauchyDivisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyDivisionUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyDivisionUpTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyDivisionBHistCarrier : BHistCarrier RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDivisionToEventFlow
  fromEventFlow := regularCauchyDivisionFromEventFlow

instance regularCauchyDivisionChapterTasteGate :
    ChapterTasteGate RegularCauchyDivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyDivisionFromEventFlow (regularCauchyDivisionToEventFlow x) =
      some x
    exact RegularCauchyDivisionUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDivisionToEventFlow_injective heq)

theorem RegularCauchyDivisionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyDivisionDecodeBHist (regularCauchyDivisionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyDivisionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyDivisionUp) ∧
          regularCauchyDivisionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨RegularCauchyDivisionUpTasteGate_single_carrier_alignment_decode,
      ⟨regularCauchyDivisionBHistCarrier⟩,
      ⟨regularCauchyDivisionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyDivisionUp
