import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSmithNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSmithNetUp : Type where
  | mk (D V T F U H C P N : BHist) : MooreSmithNetUp
  deriving DecidableEq

def mooreSmithNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSmithNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSmithNetEncodeBHist h

def mooreSmithNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSmithNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSmithNetDecodeBHist tail)

private theorem MooreSmithNetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSmithNetFields : MooreSmithNetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSmithNetUp.mk D V T F U H C P N => [D, V, T, F, U, H, C, P, N]

def mooreSmithNetToEventFlow : MooreSmithNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mooreSmithNetFields x).map mooreSmithNetEncodeBHist

def mooreSmithNetFromEventFlow : EventFlow → Option MooreSmithNetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: restV =>
      match restV with
      | [] => none
      | V :: restT =>
          match restT with
          | [] => none
          | T :: restF =>
              match restF with
              | [] => none
              | F :: restU =>
                  match restU with
                  | [] => none
                  | U :: restH =>
                      match restH with
                      | [] => none
                      | H :: restC =>
                          match restC with
                          | [] => none
                          | C :: restP =>
                              match restP with
                              | [] => none
                              | P :: restN =>
                                  match restN with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (MooreSmithNetUp.mk
                                              (mooreSmithNetDecodeBHist D)
                                              (mooreSmithNetDecodeBHist V)
                                              (mooreSmithNetDecodeBHist T)
                                              (mooreSmithNetDecodeBHist F)
                                              (mooreSmithNetDecodeBHist U)
                                              (mooreSmithNetDecodeBHist H)
                                              (mooreSmithNetDecodeBHist C)
                                              (mooreSmithNetDecodeBHist P)
                                              (mooreSmithNetDecodeBHist N))
                                      | _ :: _ => none

private theorem MooreSmithNetTasteGate_single_carrier_alignment_round_trip
    (x : MooreSmithNetUp) :
    mooreSmithNetFromEventFlow (mooreSmithNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D V T F U H C P N =>
      change
        some
          (MooreSmithNetUp.mk
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist D))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist V))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist T))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist F))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist U))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist H))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist C))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist P))
            (mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist N))) =
          some (MooreSmithNetUp.mk D V T F U H C P N)
      rw [MooreSmithNetTasteGate_single_carrier_alignment_decode_encode D,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode V,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode T,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode F,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode U,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode H,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode C,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode P,
        MooreSmithNetTasteGate_single_carrier_alignment_decode_encode N]

private theorem MooreSmithNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MooreSmithNetUp} :
    mooreSmithNetToEventFlow x = mooreSmithNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSmithNetFromEventFlow (mooreSmithNetToEventFlow x) =
        mooreSmithNetFromEventFlow (mooreSmithNetToEventFlow y) :=
    congrArg mooreSmithNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MooreSmithNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MooreSmithNetTasteGate_single_carrier_alignment_round_trip y)))

instance mooreSmithNetBHistCarrier : BHistCarrier MooreSmithNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSmithNetToEventFlow
  fromEventFlow := mooreSmithNetFromEventFlow

instance mooreSmithNetChapterTasteGate :
    ChapterTasteGate MooreSmithNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreSmithNetFromEventFlow (mooreSmithNetToEventFlow x) = some x
    exact MooreSmithNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreSmithNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MooreSmithNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, mooreSmithNetDecodeBHist (mooreSmithNetEncodeBHist h) = h) ∧
      (∀ x : MooreSmithNetUp,
        mooreSmithNetFromEventFlow (mooreSmithNetToEventFlow x) = some x) ∧
        (∀ x y : MooreSmithNetUp,
          mooreSmithNetToEventFlow x = mooreSmithNetToEventFlow y → x = y) ∧
          mooreSmithNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MooreSmithNetTasteGate_single_carrier_alignment_decode_encode,
      MooreSmithNetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MooreSmithNetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MooreSmithNetUp
