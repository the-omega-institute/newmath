import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AitkenDeltaSquaredUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AitkenDeltaSquaredUp : Type where
  | mk (S W O F G Q K R E H C P N : BHist) : AitkenDeltaSquaredUp
  deriving DecidableEq

def aitkenDeltaSquaredEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: aitkenDeltaSquaredEncodeBHist h
  | BHist.e1 h => BMark.b1 :: aitkenDeltaSquaredEncodeBHist h

def aitkenDeltaSquaredDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (aitkenDeltaSquaredDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (aitkenDeltaSquaredDecodeBHist tail)

private theorem aitkenDeltaSquaredDecode_encode_bhist :
    ∀ h : BHist, aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def aitkenDeltaSquaredFields : AitkenDeltaSquaredUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AitkenDeltaSquaredUp.mk S W O F G Q K R E H C P N => [S, W, O, F, G, Q, K, R, E, H, C, P, N]

def aitkenDeltaSquaredToEventFlow : AitkenDeltaSquaredUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (aitkenDeltaSquaredFields x).map aitkenDeltaSquaredEncodeBHist

def aitkenDeltaSquaredFromEventFlow : EventFlow → Option AitkenDeltaSquaredUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restW =>
      match restW with
      | [] => none
      | W :: restO =>
          match restO with
          | [] => none
          | O :: restF =>
              match restF with
              | [] => none
              | F :: restG =>
                  match restG with
                  | [] => none
                  | G :: restQ =>
                      match restQ with
                      | [] => none
                      | Q :: restK =>
                          match restK with
                          | [] => none
                          | K :: restR =>
                              match restR with
                              | [] => none
                              | R :: restE =>
                                  match restE with
                                  | [] => none
                                  | E :: restH =>
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
                                                            (AitkenDeltaSquaredUp.mk
                                                              (aitkenDeltaSquaredDecodeBHist S)
                                                              (aitkenDeltaSquaredDecodeBHist W)
                                                              (aitkenDeltaSquaredDecodeBHist O)
                                                              (aitkenDeltaSquaredDecodeBHist F)
                                                              (aitkenDeltaSquaredDecodeBHist G)
                                                              (aitkenDeltaSquaredDecodeBHist Q)
                                                              (aitkenDeltaSquaredDecodeBHist K)
                                                              (aitkenDeltaSquaredDecodeBHist R)
                                                              (aitkenDeltaSquaredDecodeBHist E)
                                                              (aitkenDeltaSquaredDecodeBHist H)
                                                              (aitkenDeltaSquaredDecodeBHist C)
                                                              (aitkenDeltaSquaredDecodeBHist P)
                                                              (aitkenDeltaSquaredDecodeBHist N))
                                                      | _ :: _ => none

private theorem aitkenDeltaSquared_round_trip :
    ∀ x : AitkenDeltaSquaredUp,
      aitkenDeltaSquaredFromEventFlow (aitkenDeltaSquaredToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W O F G Q K R E H C P N =>
      change
        some
          (AitkenDeltaSquaredUp.mk
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist S))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist W))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist O))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist F))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist G))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist Q))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist K))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist R))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist E))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist H))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist C))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist P))
            (aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist N))) =
          some (AitkenDeltaSquaredUp.mk S W O F G Q K R E H C P N)
      rw [aitkenDeltaSquaredDecode_encode_bhist S, aitkenDeltaSquaredDecode_encode_bhist W,
        aitkenDeltaSquaredDecode_encode_bhist O, aitkenDeltaSquaredDecode_encode_bhist F,
        aitkenDeltaSquaredDecode_encode_bhist G, aitkenDeltaSquaredDecode_encode_bhist Q,
        aitkenDeltaSquaredDecode_encode_bhist K, aitkenDeltaSquaredDecode_encode_bhist R,
        aitkenDeltaSquaredDecode_encode_bhist E, aitkenDeltaSquaredDecode_encode_bhist H,
        aitkenDeltaSquaredDecode_encode_bhist C, aitkenDeltaSquaredDecode_encode_bhist P,
        aitkenDeltaSquaredDecode_encode_bhist N]

private theorem aitkenDeltaSquaredToEventFlow_injective {x y : AitkenDeltaSquaredUp} :
    aitkenDeltaSquaredToEventFlow x = aitkenDeltaSquaredToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      aitkenDeltaSquaredFromEventFlow (aitkenDeltaSquaredToEventFlow x) =
        aitkenDeltaSquaredFromEventFlow (aitkenDeltaSquaredToEventFlow y) :=
    congrArg aitkenDeltaSquaredFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (aitkenDeltaSquared_round_trip x).symm
      (Eq.trans hread (aitkenDeltaSquared_round_trip y)))

instance aitkenDeltaSquaredBHistCarrier : BHistCarrier AitkenDeltaSquaredUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := aitkenDeltaSquaredToEventFlow
  fromEventFlow := aitkenDeltaSquaredFromEventFlow

instance aitkenDeltaSquaredChapterTasteGate : ChapterTasteGate AitkenDeltaSquaredUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change aitkenDeltaSquaredFromEventFlow (aitkenDeltaSquaredToEventFlow x) = some x
    exact aitkenDeltaSquared_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (aitkenDeltaSquaredToEventFlow_injective heq)

theorem AitkenDeltaSquaredTasteGate_single_carrier_alignment :
    (∀ h : BHist, aitkenDeltaSquaredDecodeBHist (aitkenDeltaSquaredEncodeBHist h) = h) ∧
      (∀ x : AitkenDeltaSquaredUp,
        aitkenDeltaSquaredFromEventFlow (aitkenDeltaSquaredToEventFlow x) = some x) ∧
        (∀ x y : AitkenDeltaSquaredUp,
          aitkenDeltaSquaredToEventFlow x = aitkenDeltaSquaredToEventFlow y → x = y) ∧
          aitkenDeltaSquaredEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨aitkenDeltaSquaredDecode_encode_bhist,
      aitkenDeltaSquared_round_trip,
      (fun _ _ heq => aitkenDeltaSquaredToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AitkenDeltaSquaredUp
