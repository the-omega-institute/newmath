import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorDiagonalRealUncountabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorDiagonalRealUncountabilityUp : Type where
  | mk (E W B Q R S H K P N : BHist) : CantorDiagonalRealUncountabilityUp
  deriving DecidableEq

def cantorDiagonalRealUncountabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorDiagonalRealUncountabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorDiagonalRealUncountabilityEncodeBHist h

def cantorDiagonalRealUncountabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorDiagonalRealUncountabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorDiagonalRealUncountabilityDecodeBHist tail)

private theorem CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cantorDiagonalRealUncountabilityDecodeBHist
        (cantorDiagonalRealUncountabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorDiagonalRealUncountabilityToEventFlow :
    CantorDiagonalRealUncountabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CantorDiagonalRealUncountabilityUp.mk E W B Q R S H K P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        cantorDiagonalRealUncountabilityEncodeBHist E,
        cantorDiagonalRealUncountabilityEncodeBHist W,
        cantorDiagonalRealUncountabilityEncodeBHist B,
        cantorDiagonalRealUncountabilityEncodeBHist Q,
        cantorDiagonalRealUncountabilityEncodeBHist R,
        cantorDiagonalRealUncountabilityEncodeBHist S,
        cantorDiagonalRealUncountabilityEncodeBHist H,
        cantorDiagonalRealUncountabilityEncodeBHist K,
        cantorDiagonalRealUncountabilityEncodeBHist P,
        cantorDiagonalRealUncountabilityEncodeBHist N]

def cantorDiagonalRealUncountabilityFromEventFlow :
    EventFlow → Option CantorDiagonalRealUncountabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restE =>
      match restE with
      | [] => none
      | E :: restW =>
          match restW with
          | [] => none
          | W :: restB =>
              match restB with
              | [] => none
              | B :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restR =>
                      match restR with
                      | [] => none
                      | R :: restS =>
                          match restS with
                          | [] => none
                          | S :: restH =>
                              match restH with
                              | [] => none
                              | H :: restK =>
                                  match restK with
                                  | [] => none
                                  | K :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (CantorDiagonalRealUncountabilityUp.mk
                                                      (cantorDiagonalRealUncountabilityDecodeBHist E)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist W)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist B)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist Q)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist R)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist S)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist H)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist K)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist P)
                                                      (cantorDiagonalRealUncountabilityDecodeBHist N))
                                              | _ :: _ => none

private theorem CantorDiagonalRealUncountabilityUp_single_carrier_alignment_round_trip :
    ∀ x : CantorDiagonalRealUncountabilityUp,
      cantorDiagonalRealUncountabilityFromEventFlow
        (cantorDiagonalRealUncountabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E W B Q R S H K P N =>
      change
        some
          (CantorDiagonalRealUncountabilityUp.mk
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist E))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist W))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist B))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist Q))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist R))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist S))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist H))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist K))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist P))
            (cantorDiagonalRealUncountabilityDecodeBHist
              (cantorDiagonalRealUncountabilityEncodeBHist N))) =
          some (CantorDiagonalRealUncountabilityUp.mk E W B Q R S H K P N)
      rw [CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode E,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode W,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode B,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode Q,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode R,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode S,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode H,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode K,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode P,
        CantorDiagonalRealUncountabilityUp_single_carrier_alignment_decode_encode N]

private theorem CantorDiagonalRealUncountabilityUp_single_carrier_alignment_toEventFlow_injective
    {x y : CantorDiagonalRealUncountabilityUp} :
    cantorDiagonalRealUncountabilityToEventFlow x =
      cantorDiagonalRealUncountabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorDiagonalRealUncountabilityFromEventFlow
          (cantorDiagonalRealUncountabilityToEventFlow x) =
        cantorDiagonalRealUncountabilityFromEventFlow
          (cantorDiagonalRealUncountabilityToEventFlow y) :=
    congrArg cantorDiagonalRealUncountabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CantorDiagonalRealUncountabilityUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CantorDiagonalRealUncountabilityUp_single_carrier_alignment_round_trip y)))

instance cantorDiagonalRealUncountabilityBHistCarrier :
    BHistCarrier CantorDiagonalRealUncountabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorDiagonalRealUncountabilityToEventFlow
  fromEventFlow := cantorDiagonalRealUncountabilityFromEventFlow

instance cantorDiagonalRealUncountabilityChapterTasteGate :
    ChapterTasteGate CantorDiagonalRealUncountabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cantorDiagonalRealUncountabilityFromEventFlow
        (cantorDiagonalRealUncountabilityToEventFlow x) = some x
    exact CantorDiagonalRealUncountabilityUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CantorDiagonalRealUncountabilityUp_single_carrier_alignment_toEventFlow_injective heq)

theorem CantorDiagonalRealUncountabilityUp_single_carrier_alignment :
    Nonempty (BHistCarrier CantorDiagonalRealUncountabilityUp) ∧
      Nonempty (ChapterTasteGate CantorDiagonalRealUncountabilityUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨Nonempty.intro cantorDiagonalRealUncountabilityBHistCarrier,
      Nonempty.intro cantorDiagonalRealUncountabilityChapterTasteGate⟩

end BEDC.Derived.CantorDiagonalRealUncountabilityUp
