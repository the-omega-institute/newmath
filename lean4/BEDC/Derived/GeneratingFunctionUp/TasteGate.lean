import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratingFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeneratingFunctionUp : Type where
  | mk (A W Q L Pd M H C P N : BHist) : GeneratingFunctionUp
  deriving DecidableEq

def generatingFunctionFields : GeneratingFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GeneratingFunctionUp.mk A W Q L Pd M H C P N => [A, W, Q, L, Pd, M, H, C, P, N]

def generatingFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatingFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatingFunctionEncodeBHist h

def generatingFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatingFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatingFunctionDecodeBHist tail)

private theorem GeneratingFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, generatingFunctionDecodeBHist (generatingFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def generatingFunctionToEventFlow : GeneratingFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (generatingFunctionFields x).map generatingFunctionEncodeBHist

private def generatingFunctionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => generatingFunctionRawAt n rest

def generatingFunctionFromEventFlow (flow : EventFlow) : Option GeneratingFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GeneratingFunctionUp.mk
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 0 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 1 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 2 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 3 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 4 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 5 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 6 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 7 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 8 flow))
      (generatingFunctionDecodeBHist (generatingFunctionRawAt 9 flow)))

private theorem GeneratingFunctionTasteGate_single_carrier_alignment_round_trip
    (x : GeneratingFunctionUp) :
    generatingFunctionFromEventFlow (generatingFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A W Q L Pd M H C P N =>
      change
        some
          (GeneratingFunctionUp.mk
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist A))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist W))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist Q))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist L))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist Pd))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist M))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist H))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist C))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist P))
            (generatingFunctionDecodeBHist (generatingFunctionEncodeBHist N))) =
          some (GeneratingFunctionUp.mk A W Q L Pd M H C P N)
      rw [GeneratingFunctionTasteGate_single_carrier_alignment_decode A,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode W,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode Q,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode L,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode Pd,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode M,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode H,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode C,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode P,
        GeneratingFunctionTasteGate_single_carrier_alignment_decode N]

private theorem GeneratingFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GeneratingFunctionUp} :
    generatingFunctionToEventFlow x = generatingFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatingFunctionFromEventFlow (generatingFunctionToEventFlow x) =
        generatingFunctionFromEventFlow (generatingFunctionToEventFlow y) :=
    congrArg generatingFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GeneratingFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GeneratingFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance generatingFunctionBHistCarrier : BHistCarrier GeneratingFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatingFunctionToEventFlow
  fromEventFlow := generatingFunctionFromEventFlow

instance generatingFunctionChapterTasteGate : ChapterTasteGate GeneratingFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change generatingFunctionFromEventFlow (generatingFunctionToEventFlow x) = some x
    exact GeneratingFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GeneratingFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GeneratingFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, generatingFunctionDecodeBHist (generatingFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier GeneratingFunctionUp) ∧
      Nonempty (ChapterTasteGate GeneratingFunctionUp) ∧
      generatingFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨GeneratingFunctionTasteGate_single_carrier_alignment_decode,
      ⟨generatingFunctionBHistCarrier⟩, ⟨generatingFunctionChapterTasteGate⟩, rfl⟩

end BEDC.Derived.GeneratingFunctionUp
