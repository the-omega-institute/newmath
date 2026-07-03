import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SystemFUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SystemFUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (X A L E T B I H C P N : BHist) : SystemFUp

def systemFEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: systemFEncodeBHist h
  | BHist.e1 h => BMark.b1 :: systemFEncodeBHist h

def systemFDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (systemFDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (systemFDecodeBHist tail)

private theorem SystemFTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, systemFDecodeBHist (systemFEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def systemFFields : SystemFUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SystemFUp.mk X A L E T B I H C P N => [X, A, L, E, T, B, I, H, C, P, N]

def systemFToEventFlow : SystemFUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (systemFFields x).map systemFEncodeBHist

private def systemFRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => systemFRawAt index rest

def systemFFromEventFlow (flow : EventFlow) : Option SystemFUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SystemFUp.mk
      (systemFDecodeBHist (systemFRawAt 0 flow))
      (systemFDecodeBHist (systemFRawAt 1 flow))
      (systemFDecodeBHist (systemFRawAt 2 flow))
      (systemFDecodeBHist (systemFRawAt 3 flow))
      (systemFDecodeBHist (systemFRawAt 4 flow))
      (systemFDecodeBHist (systemFRawAt 5 flow))
      (systemFDecodeBHist (systemFRawAt 6 flow))
      (systemFDecodeBHist (systemFRawAt 7 flow))
      (systemFDecodeBHist (systemFRawAt 8 flow))
      (systemFDecodeBHist (systemFRawAt 9 flow))
      (systemFDecodeBHist (systemFRawAt 10 flow)))

private theorem SystemFTasteGate_single_carrier_alignment_round_trip
    (x : SystemFUp) :
    systemFFromEventFlow (systemFToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X A L E T B I H C P N =>
      change
        some
          (SystemFUp.mk
            (systemFDecodeBHist (systemFEncodeBHist X))
            (systemFDecodeBHist (systemFEncodeBHist A))
            (systemFDecodeBHist (systemFEncodeBHist L))
            (systemFDecodeBHist (systemFEncodeBHist E))
            (systemFDecodeBHist (systemFEncodeBHist T))
            (systemFDecodeBHist (systemFEncodeBHist B))
            (systemFDecodeBHist (systemFEncodeBHist I))
            (systemFDecodeBHist (systemFEncodeBHist H))
            (systemFDecodeBHist (systemFEncodeBHist C))
            (systemFDecodeBHist (systemFEncodeBHist P))
            (systemFDecodeBHist (systemFEncodeBHist N))) =
          some (SystemFUp.mk X A L E T B I H C P N)
      rw [SystemFTasteGate_single_carrier_alignment_decode X,
        SystemFTasteGate_single_carrier_alignment_decode A,
        SystemFTasteGate_single_carrier_alignment_decode L,
        SystemFTasteGate_single_carrier_alignment_decode E,
        SystemFTasteGate_single_carrier_alignment_decode T,
        SystemFTasteGate_single_carrier_alignment_decode B,
        SystemFTasteGate_single_carrier_alignment_decode I,
        SystemFTasteGate_single_carrier_alignment_decode H,
        SystemFTasteGate_single_carrier_alignment_decode C,
        SystemFTasteGate_single_carrier_alignment_decode P,
        SystemFTasteGate_single_carrier_alignment_decode N]

private theorem systemFToEventFlow_injective {x y : SystemFUp} :
    systemFToEventFlow x = systemFToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      systemFFromEventFlow (systemFToEventFlow x) =
        systemFFromEventFlow (systemFToEventFlow y) :=
    congrArg systemFFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SystemFTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SystemFTasteGate_single_carrier_alignment_round_trip y)))

instance systemFBHistCarrier : BHistCarrier SystemFUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := systemFToEventFlow
  fromEventFlow := systemFFromEventFlow

instance systemFChapterTasteGate : ChapterTasteGate SystemFUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change systemFFromEventFlow (systemFToEventFlow x) = some x
    exact SystemFTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (systemFToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SystemFUp :=
  -- BEDC touchpoint anchor: BHist BMark
  systemFChapterTasteGate

theorem SystemFTasteGate_single_carrier_alignment :
    (∀ h : BHist, systemFDecodeBHist (systemFEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SystemFUp) ∧
        Nonempty (ChapterTasteGate SystemFUp) ∧
          systemFEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨SystemFTasteGate_single_carrier_alignment_decode,
      ⟨systemFBHistCarrier⟩,
      ⟨systemFChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SystemFUp
