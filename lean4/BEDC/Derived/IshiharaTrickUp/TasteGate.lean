import BEDC.Derived.IshiharaTrickUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IshiharaTrickUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def ishiharaTrickEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ishiharaTrickEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ishiharaTrickEncodeBHist h

def ishiharaTrickDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ishiharaTrickDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ishiharaTrickDecodeBHist tail)

private theorem ishiharaTrickDecodeEncodeBHist :
    ∀ h : BHist, ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ishiharaTrickFields : IshiharaTrickUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IshiharaTrickUp.mk schedule readback tolerance realSeal branchRow transport replay provenance
      localName =>
      [schedule, readback, tolerance, realSeal, branchRow, transport, replay, provenance, localName]

def ishiharaTrickToEventFlow : IshiharaTrickUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ishiharaTrickFields x).map ishiharaTrickEncodeBHist

def ishiharaTrickFromEventFlow : EventFlow → Option IshiharaTrickUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | schedule :: rest0 =>
      match rest0 with
      | [] => none
      | readback :: rest1 =>
          match rest1 with
          | [] => none
          | tolerance :: rest2 =>
              match rest2 with
              | [] => none
              | realSeal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | branchRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (IshiharaTrickUp.mk
                                              (ishiharaTrickDecodeBHist schedule)
                                              (ishiharaTrickDecodeBHist readback)
                                              (ishiharaTrickDecodeBHist tolerance)
                                              (ishiharaTrickDecodeBHist realSeal)
                                              (ishiharaTrickDecodeBHist branchRow)
                                              (ishiharaTrickDecodeBHist transport)
                                              (ishiharaTrickDecodeBHist replay)
                                              (ishiharaTrickDecodeBHist provenance)
                                              (ishiharaTrickDecodeBHist localName))
                                      | _ :: _ => none

private theorem ishiharaTrick_round_trip :
    ∀ x : IshiharaTrickUp,
      ishiharaTrickFromEventFlow (ishiharaTrickToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk schedule readback tolerance realSeal branchRow transport replay provenance localName =>
      change
        some
          (IshiharaTrickUp.mk
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist schedule))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist readback))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist tolerance))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist realSeal))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist branchRow))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist transport))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist replay))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist provenance))
            (ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist localName))) =
          some
            (IshiharaTrickUp.mk schedule readback tolerance realSeal branchRow transport replay
              provenance localName)
      rw [ishiharaTrickDecodeEncodeBHist schedule,
        ishiharaTrickDecodeEncodeBHist readback,
        ishiharaTrickDecodeEncodeBHist tolerance,
        ishiharaTrickDecodeEncodeBHist realSeal,
        ishiharaTrickDecodeEncodeBHist branchRow,
        ishiharaTrickDecodeEncodeBHist transport,
        ishiharaTrickDecodeEncodeBHist replay,
        ishiharaTrickDecodeEncodeBHist provenance,
        ishiharaTrickDecodeEncodeBHist localName]

private theorem ishiharaTrickToEventFlow_injective {x y : IshiharaTrickUp} :
    ishiharaTrickToEventFlow x = ishiharaTrickToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ishiharaTrickFromEventFlow (ishiharaTrickToEventFlow x) =
        ishiharaTrickFromEventFlow (ishiharaTrickToEventFlow y) :=
    congrArg ishiharaTrickFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ishiharaTrick_round_trip x).symm
      (Eq.trans hread (ishiharaTrick_round_trip y)))

instance ishiharaTrickBHistCarrier : BHistCarrier IshiharaTrickUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ishiharaTrickToEventFlow
  fromEventFlow := ishiharaTrickFromEventFlow

instance ishiharaTrickChapterTasteGate : ChapterTasteGate IshiharaTrickUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ishiharaTrickFromEventFlow (ishiharaTrickToEventFlow x) = some x
    exact ishiharaTrick_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ishiharaTrickToEventFlow_injective heq)

def taste_gate : ChapterTasteGate IshiharaTrickUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ishiharaTrickChapterTasteGate

theorem IshiharaTrickTasteGate_single_carrier_alignment :
    (∀ h : BHist, ishiharaTrickDecodeBHist (ishiharaTrickEncodeBHist h) = h) ∧
      (∀ x : IshiharaTrickUp,
        ishiharaTrickFromEventFlow (ishiharaTrickToEventFlow x) = some x) ∧
        (∀ x y : IshiharaTrickUp,
          ishiharaTrickToEventFlow x = ishiharaTrickToEventFlow y → x = y) ∧
          ishiharaTrickEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ishiharaTrickDecodeEncodeBHist
  · constructor
    · exact ishiharaTrick_round_trip
    · constructor
      · intro x y heq
        exact ishiharaTrickToEventFlow_injective heq
      · rfl

end BEDC.Derived.IshiharaTrickUp
