import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BisectionRootIsolationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BisectionRootIsolationUp : Type where
  | mk
      (J B F E W R S H C P N : BHist) :
      BisectionRootIsolationUp
  deriving DecidableEq

def bisectionRootIsolationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bisectionRootIsolationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bisectionRootIsolationEncodeBHist h

def bisectionRootIsolationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bisectionRootIsolationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bisectionRootIsolationDecodeBHist tail)

private theorem BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bisectionRootIsolationToEventFlow : BisectionRootIsolationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BisectionRootIsolationUp.mk J B F E W R S H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        bisectionRootIsolationEncodeBHist J,
        bisectionRootIsolationEncodeBHist B,
        bisectionRootIsolationEncodeBHist F,
        bisectionRootIsolationEncodeBHist E,
        bisectionRootIsolationEncodeBHist W,
        bisectionRootIsolationEncodeBHist R,
        bisectionRootIsolationEncodeBHist S,
        bisectionRootIsolationEncodeBHist H,
        bisectionRootIsolationEncodeBHist C,
        bisectionRootIsolationEncodeBHist P,
        bisectionRootIsolationEncodeBHist N]

def bisectionRootIsolationFromEventFlow : EventFlow → Option BisectionRootIsolationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restJ =>
      match restJ with
      | [] => none
      | J :: restB =>
          match restB with
          | [] => none
          | B :: restF =>
              match restF with
              | [] => none
              | F :: restE =>
                  match restE with
                  | [] => none
                  | E :: restW =>
                      match restW with
                      | [] => none
                      | W :: restR =>
                          match restR with
                          | [] => none
                          | R :: restS =>
                              match restS with
                              | [] => none
                              | S :: restH =>
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
                                                        (BisectionRootIsolationUp.mk
                                                          (bisectionRootIsolationDecodeBHist J)
                                                          (bisectionRootIsolationDecodeBHist B)
                                                          (bisectionRootIsolationDecodeBHist F)
                                                          (bisectionRootIsolationDecodeBHist E)
                                                          (bisectionRootIsolationDecodeBHist W)
                                                          (bisectionRootIsolationDecodeBHist R)
                                                          (bisectionRootIsolationDecodeBHist S)
                                                          (bisectionRootIsolationDecodeBHist H)
                                                          (bisectionRootIsolationDecodeBHist C)
                                                          (bisectionRootIsolationDecodeBHist P)
                                                          (bisectionRootIsolationDecodeBHist N))
                                                  | _ :: _ => none

private theorem BisectionRootIsolationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BisectionRootIsolationUp,
      bisectionRootIsolationFromEventFlow (bisectionRootIsolationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J B F E W R S H C P N =>
      change
        some
          (BisectionRootIsolationUp.mk
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist J))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist B))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist F))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist E))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist W))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist R))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist S))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist H))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist C))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist P))
            (bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist N))) =
          some (BisectionRootIsolationUp.mk J B F E W R S H C P N)
      rw [BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode J,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode B,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode F,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode E,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode W,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode R,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode S,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode H,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode C,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode P,
        BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode N]

private theorem BisectionRootIsolationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BisectionRootIsolationUp} :
    bisectionRootIsolationToEventFlow x = bisectionRootIsolationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bisectionRootIsolationFromEventFlow (bisectionRootIsolationToEventFlow x) =
        bisectionRootIsolationFromEventFlow (bisectionRootIsolationToEventFlow y) :=
    congrArg bisectionRootIsolationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BisectionRootIsolationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BisectionRootIsolationTasteGate_single_carrier_alignment_round_trip y)))

instance bisectionRootIsolationBHistCarrier : BHistCarrier BisectionRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bisectionRootIsolationToEventFlow
  fromEventFlow := bisectionRootIsolationFromEventFlow

instance bisectionRootIsolationChapterTasteGate :
    ChapterTasteGate BisectionRootIsolationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bisectionRootIsolationFromEventFlow (bisectionRootIsolationToEventFlow x) = some x
    exact BisectionRootIsolationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BisectionRootIsolationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BisectionRootIsolationTasteGate_single_carrier_alignment :
    (∀ h : BHist, bisectionRootIsolationDecodeBHist (bisectionRootIsolationEncodeBHist h) = h) ∧
      (∀ x : BisectionRootIsolationUp,
        bisectionRootIsolationFromEventFlow (bisectionRootIsolationToEventFlow x) = some x) ∧
        (∀ x y : BisectionRootIsolationUp,
          bisectionRootIsolationToEventFlow x = bisectionRootIsolationToEventFlow y → x = y) ∧
          bisectionRootIsolationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BisectionRootIsolationTasteGate_single_carrier_alignment_decode_encode,
      BisectionRootIsolationTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        BisectionRootIsolationTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BisectionRootIsolationUp
