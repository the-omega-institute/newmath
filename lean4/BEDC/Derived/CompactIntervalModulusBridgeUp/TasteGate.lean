import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalModulusBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalModulusBridgeUp : Type where
  | mk (E N R U M S Q H C P L : BHist) : CompactIntervalModulusBridgeUp
  deriving DecidableEq

def compactIntervalModulusBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalModulusBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalModulusBridgeEncodeBHist h

def compactIntervalModulusBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalModulusBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalModulusBridgeDecodeBHist tail)

private theorem CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactIntervalModulusBridgeDecodeBHist
          (compactIntervalModulusBridgeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalModulusBridgeToEventFlow :
    CompactIntervalModulusBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalModulusBridgeUp.mk E N R U M S Q H C P L =>
      [compactIntervalModulusBridgeEncodeBHist E,
        compactIntervalModulusBridgeEncodeBHist N,
        compactIntervalModulusBridgeEncodeBHist R,
        compactIntervalModulusBridgeEncodeBHist U,
        compactIntervalModulusBridgeEncodeBHist M,
        compactIntervalModulusBridgeEncodeBHist S,
        compactIntervalModulusBridgeEncodeBHist Q,
        compactIntervalModulusBridgeEncodeBHist H,
        compactIntervalModulusBridgeEncodeBHist C,
        compactIntervalModulusBridgeEncodeBHist P,
        compactIntervalModulusBridgeEncodeBHist L]

def compactIntervalModulusBridgeFromEventFlow :
    EventFlow → Option CompactIntervalModulusBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | E :: restN =>
      match restN with
      | [] => none
      | N :: restR =>
          match restR with
          | [] => none
          | R :: restU =>
              match restU with
              | [] => none
              | U :: restM =>
                  match restM with
                  | [] => none
                  | M :: restS =>
                      match restS with
                      | [] => none
                      | S :: restQ =>
                          match restQ with
                          | [] => none
                          | Q :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restL =>
                                          match restL with
                                          | [] => none
                                          | L :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (CompactIntervalModulusBridgeUp.mk
                                                      (compactIntervalModulusBridgeDecodeBHist E)
                                                      (compactIntervalModulusBridgeDecodeBHist N)
                                                      (compactIntervalModulusBridgeDecodeBHist R)
                                                      (compactIntervalModulusBridgeDecodeBHist U)
                                                      (compactIntervalModulusBridgeDecodeBHist M)
                                                      (compactIntervalModulusBridgeDecodeBHist S)
                                                      (compactIntervalModulusBridgeDecodeBHist Q)
                                                      (compactIntervalModulusBridgeDecodeBHist H)
                                                      (compactIntervalModulusBridgeDecodeBHist C)
                                                      (compactIntervalModulusBridgeDecodeBHist P)
                                                      (compactIntervalModulusBridgeDecodeBHist L))
                                              | _ :: _ => none

private theorem CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactIntervalModulusBridgeUp,
      compactIntervalModulusBridgeFromEventFlow
          (compactIntervalModulusBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk E N R U M S Q H C P L =>
      change
        some
          (CompactIntervalModulusBridgeUp.mk
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist E))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist N))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist R))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist U))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist M))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist S))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist Q))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist H))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist C))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist P))
            (compactIntervalModulusBridgeDecodeBHist
              (compactIntervalModulusBridgeEncodeBHist L))) =
          some (CompactIntervalModulusBridgeUp.mk E N R U M S Q H C P L)
      rw [CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode E,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode N,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode R,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode U,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode M,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode S,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode Q,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode H,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode C,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode P,
        CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode L]

private theorem CompactIntervalModulusBridgeToEventFlow_injective
    {x y : CompactIntervalModulusBridgeUp} :
    compactIntervalModulusBridgeToEventFlow x =
        compactIntervalModulusBridgeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalModulusBridgeFromEventFlow
          (compactIntervalModulusBridgeToEventFlow x) =
        compactIntervalModulusBridgeFromEventFlow
          (compactIntervalModulusBridgeToEventFlow y) :=
    congrArg compactIntervalModulusBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_round_trip y)))

instance compactIntervalModulusBridgeBHistCarrier :
    BHistCarrier CompactIntervalModulusBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalModulusBridgeToEventFlow
  fromEventFlow := compactIntervalModulusBridgeFromEventFlow

instance compactIntervalModulusBridgeChapterTasteGate :
    ChapterTasteGate CompactIntervalModulusBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactIntervalModulusBridgeFromEventFlow
          (compactIntervalModulusBridgeToEventFlow x) =
        some x
    exact CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactIntervalModulusBridgeToEventFlow_injective heq)

theorem CompactIntervalModulusBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactIntervalModulusBridgeDecodeBHist
            (compactIntervalModulusBridgeEncodeBHist h) =
          h) ∧
      (∀ x : CompactIntervalModulusBridgeUp,
        compactIntervalModulusBridgeFromEventFlow
            (compactIntervalModulusBridgeToEventFlow x) =
          some x) ∧
        (∀ x y : CompactIntervalModulusBridgeUp,
          compactIntervalModulusBridgeToEventFlow x =
              compactIntervalModulusBridgeToEventFlow y →
            x = y) ∧
          compactIntervalModulusBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_decode,
      ⟨CompactIntervalModulusBridgeTasteGate_single_carrier_alignment_round_trip,
        ⟨fun x y h => CompactIntervalModulusBridgeToEventFlow_injective h, rfl⟩⟩⟩

end BEDC.Derived.CompactIntervalModulusBridgeUp
