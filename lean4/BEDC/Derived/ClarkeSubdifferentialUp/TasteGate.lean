import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClarkeSubdifferentialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClarkeSubdifferentialUp : Type where
  | mk (X F P D T R H C G N : BHist) : ClarkeSubdifferentialUp
  deriving DecidableEq

def clarkeSubdifferentialEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: clarkeSubdifferentialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: clarkeSubdifferentialEncodeBHist h

def clarkeSubdifferentialDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (clarkeSubdifferentialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (clarkeSubdifferentialDecodeBHist tail)

private theorem ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, clarkeSubdifferentialDecodeBHist
      (clarkeSubdifferentialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def clarkeSubdifferentialFields :
    ClarkeSubdifferentialUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClarkeSubdifferentialUp.mk X F P D T R H C G N => [X, F, P, D, T, R, H, C, G, N]

def clarkeSubdifferentialToEventFlow :
    ClarkeSubdifferentialUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (clarkeSubdifferentialFields x).map clarkeSubdifferentialEncodeBHist

private def clarkeSubdifferentialEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => clarkeSubdifferentialEventAtDefault index rest

def clarkeSubdifferentialFromEventFlow
    (ef : EventFlow) : Option ClarkeSubdifferentialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClarkeSubdifferentialUp.mk
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 0 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 1 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 2 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 3 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 4 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 5 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 6 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 7 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 8 ef))
      (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEventAtDefault 9 ef)))

private theorem ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_round_trip
    (x : ClarkeSubdifferentialUp) :
    clarkeSubdifferentialFromEventFlow
      (clarkeSubdifferentialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X F P D T R H C G N =>
      change
        some
          (ClarkeSubdifferentialUp.mk
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist X))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist F))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist P))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist D))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist T))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist R))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist H))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist C))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist G))
            (clarkeSubdifferentialDecodeBHist (clarkeSubdifferentialEncodeBHist N))) =
          some (ClarkeSubdifferentialUp.mk X F P D T R H C G N)
      rw [ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode X,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode F,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode P,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode D,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode T,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode R,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode H,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode C,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode G,
        ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClarkeSubdifferentialUp} :
    clarkeSubdifferentialToEventFlow x =
      clarkeSubdifferentialToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      clarkeSubdifferentialFromEventFlow
          (clarkeSubdifferentialToEventFlow x) =
        clarkeSubdifferentialFromEventFlow
          (clarkeSubdifferentialToEventFlow y) :=
    congrArg clarkeSubdifferentialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_round_trip y)))

instance clarkeSubdifferentialBHistCarrier :
    BHistCarrier ClarkeSubdifferentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := clarkeSubdifferentialToEventFlow
  fromEventFlow := clarkeSubdifferentialFromEventFlow

instance clarkeSubdifferentialChapterTasteGate :
    ChapterTasteGate ClarkeSubdifferentialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change clarkeSubdifferentialFromEventFlow
      (clarkeSubdifferentialToEventFlow x) = some x
    exact ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def ClarkeSubdifferentialUpTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ClarkeSubdifferentialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  clarkeSubdifferentialChapterTasteGate

theorem ClarkeSubdifferentialUpTasteGate_single_carrier_alignment :
    ChapterTasteGate ClarkeSubdifferentialUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact clarkeSubdifferentialChapterTasteGate

end BEDC.Derived.ClarkeSubdifferentialUp
