import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FanModulusBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FanModulusBoundaryUp : Type where
  | mk (F M W Q U R H C P N : BHist) : FanModulusBoundaryUp
  deriving DecidableEq

def fanModulusBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fanModulusBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fanModulusBoundaryEncodeBHist h

def fanModulusBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fanModulusBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fanModulusBoundaryDecodeBHist tail)

private theorem FanModulusBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fanModulusBoundaryFields : FanModulusBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FanModulusBoundaryUp.mk F M W Q U R H C P N =>
      [F, M, W, Q, U, R, H, C, P, N]

def fanModulusBoundaryToEventFlow : FanModulusBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map fanModulusBoundaryEncodeBHist (fanModulusBoundaryFields x)

def fanModulusBoundaryFromEventFlow
    (ef : EventFlow) : Option FanModulusBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | F :: restF =>
      match restF with
      | [] => none
      | M :: restM =>
          match restM with
          | [] => none
          | W :: restW =>
              match restW with
              | [] => none
              | Q :: restQ =>
                  match restQ with
                  | [] => none
                  | U :: restU =>
                      match restU with
                      | [] => none
                      | R :: restR =>
                          match restR with
                          | [] => none
                          | H :: restH =>
                              match restH with
                              | [] => none
                              | C :: restC =>
                                  match restC with
                                  | [] => none
                                  | P :: restP =>
                                      match restP with
                                      | [] => none
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (FanModulusBoundaryUp.mk
                                                  (fanModulusBoundaryDecodeBHist F)
                                                  (fanModulusBoundaryDecodeBHist M)
                                                  (fanModulusBoundaryDecodeBHist W)
                                                  (fanModulusBoundaryDecodeBHist Q)
                                                  (fanModulusBoundaryDecodeBHist U)
                                                  (fanModulusBoundaryDecodeBHist R)
                                                  (fanModulusBoundaryDecodeBHist H)
                                                  (fanModulusBoundaryDecodeBHist C)
                                                  (fanModulusBoundaryDecodeBHist P)
                                                  (fanModulusBoundaryDecodeBHist N))
                                          | _ :: _ => none

private theorem FanModulusBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FanModulusBoundaryUp,
      fanModulusBoundaryFromEventFlow (fanModulusBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M W Q U R H C P N =>
      change
        some
          (FanModulusBoundaryUp.mk
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist F))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist M))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist W))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist Q))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist U))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist R))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist H))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist C))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist P))
            (fanModulusBoundaryDecodeBHist (fanModulusBoundaryEncodeBHist N))) =
          some (FanModulusBoundaryUp.mk F M W Q U R H C P N)
      rw [FanModulusBoundaryTasteGate_single_carrier_alignment_decode F,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode M,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode W,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode Q,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode U,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode R,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode H,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode C,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode P,
        FanModulusBoundaryTasteGate_single_carrier_alignment_decode N]

private theorem FanModulusBoundaryTasteGate_single_carrier_alignment_injective
    {x y : FanModulusBoundaryUp} :
    fanModulusBoundaryToEventFlow x = fanModulusBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fanModulusBoundaryFromEventFlow (fanModulusBoundaryToEventFlow x) =
        fanModulusBoundaryFromEventFlow (fanModulusBoundaryToEventFlow y) :=
    congrArg fanModulusBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FanModulusBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FanModulusBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance fanModulusBoundaryBHistCarrier : BHistCarrier FanModulusBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fanModulusBoundaryToEventFlow
  fromEventFlow := fanModulusBoundaryFromEventFlow

instance fanModulusBoundaryChapterTasteGate : ChapterTasteGate FanModulusBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fanModulusBoundaryFromEventFlow (fanModulusBoundaryToEventFlow x) = some x
    exact FanModulusBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FanModulusBoundaryTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FanModulusBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fanModulusBoundaryChapterTasteGate

theorem FanModulusBoundaryTasteGate_single_carrier_alignment :
    (forall x : FanModulusBoundaryUp,
      fanModulusBoundaryFromEventFlow (fanModulusBoundaryToEventFlow x) = some x) ∧
      (forall x y : FanModulusBoundaryUp,
        fanModulusBoundaryToEventFlow x = fanModulusBoundaryToEventFlow y -> x = y) ∧
        fanModulusBoundaryFields
          (FanModulusBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FanModulusBoundaryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FanModulusBoundaryTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.FanModulusBoundaryUp
