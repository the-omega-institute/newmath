import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FareySequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FareySequenceUp : Type where
  | mk (B A M L T S D Q W R G E H C P N : BHist) : FareySequenceUp
  deriving DecidableEq

def fareySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fareySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fareySequenceEncodeBHist h

def fareySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fareySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fareySequenceDecodeBHist tail)

private theorem FareySequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, fareySequenceDecodeBHist (fareySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fareySequenceFields : FareySequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FareySequenceUp.mk B A M L T S D Q W R G E H C P N =>
      [B, A, M, L, T, S, D, Q, W, R, G, E, H, C, P, N]

def fareySequenceToEventFlow : FareySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map fareySequenceEncodeBHist (fareySequenceFields x)

def fareySequenceFromEventFlow (ef : EventFlow) : Option FareySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | B :: restB =>
      match restB with
      | [] => none
      | A :: restA =>
          match restA with
          | [] => none
          | M :: restM =>
              match restM with
              | [] => none
              | L :: restL =>
                  match restL with
                  | [] => none
                  | T :: restT =>
                      match restT with
                      | [] => none
                      | S :: restS =>
                          match restS with
                          | [] => none
                          | D :: restD =>
                              match restD with
                              | [] => none
                              | Q :: restQ =>
                                  match restQ with
                                  | [] => none
                                  | W :: restW =>
                                      match restW with
                                      | [] => none
                                      | R :: restR =>
                                          match restR with
                                          | [] => none
                                          | G :: restG =>
                                              match restG with
                                              | [] => none
                                              | E :: restE =>
                                                  match restE with
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
                                                                        (FareySequenceUp.mk
                                                                          (fareySequenceDecodeBHist B)
                                                                          (fareySequenceDecodeBHist A)
                                                                          (fareySequenceDecodeBHist M)
                                                                          (fareySequenceDecodeBHist L)
                                                                          (fareySequenceDecodeBHist T)
                                                                          (fareySequenceDecodeBHist S)
                                                                          (fareySequenceDecodeBHist D)
                                                                          (fareySequenceDecodeBHist Q)
                                                                          (fareySequenceDecodeBHist W)
                                                                          (fareySequenceDecodeBHist R)
                                                                          (fareySequenceDecodeBHist G)
                                                                          (fareySequenceDecodeBHist E)
                                                                          (fareySequenceDecodeBHist H)
                                                                          (fareySequenceDecodeBHist C)
                                                                          (fareySequenceDecodeBHist P)
                                                                          (fareySequenceDecodeBHist N))
                                                                  | _ :: _ => none

private theorem FareySequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FareySequenceUp,
      fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B A M L T S D Q W R G E H C P N =>
      change
        some
          (FareySequenceUp.mk
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist B))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist A))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist M))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist L))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist T))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist S))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist D))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist Q))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist W))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist R))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist G))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist E))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist H))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist C))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist P))
            (fareySequenceDecodeBHist (fareySequenceEncodeBHist N))) =
          some (FareySequenceUp.mk B A M L T S D Q W R G E H C P N)
      rw [FareySequenceTasteGate_single_carrier_alignment_decode B,
        FareySequenceTasteGate_single_carrier_alignment_decode A,
        FareySequenceTasteGate_single_carrier_alignment_decode M,
        FareySequenceTasteGate_single_carrier_alignment_decode L,
        FareySequenceTasteGate_single_carrier_alignment_decode T,
        FareySequenceTasteGate_single_carrier_alignment_decode S,
        FareySequenceTasteGate_single_carrier_alignment_decode D,
        FareySequenceTasteGate_single_carrier_alignment_decode Q,
        FareySequenceTasteGate_single_carrier_alignment_decode W,
        FareySequenceTasteGate_single_carrier_alignment_decode R,
        FareySequenceTasteGate_single_carrier_alignment_decode G,
        FareySequenceTasteGate_single_carrier_alignment_decode E,
        FareySequenceTasteGate_single_carrier_alignment_decode H,
        FareySequenceTasteGate_single_carrier_alignment_decode C,
        FareySequenceTasteGate_single_carrier_alignment_decode P,
        FareySequenceTasteGate_single_carrier_alignment_decode N]

private theorem FareySequenceTasteGate_single_carrier_alignment_injective
    {x y : FareySequenceUp} :
    fareySequenceToEventFlow x = fareySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fareySequenceFromEventFlow (fareySequenceToEventFlow x) =
        fareySequenceFromEventFlow (fareySequenceToEventFlow y) :=
    congrArg fareySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FareySequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FareySequenceTasteGate_single_carrier_alignment_round_trip y)))

instance fareySequenceBHistCarrier : BHistCarrier FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fareySequenceToEventFlow
  fromEventFlow := fareySequenceFromEventFlow

instance fareySequenceChapterTasteGate : ChapterTasteGate FareySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x
    exact FareySequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FareySequenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FareySequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fareySequenceChapterTasteGate

theorem FareySequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, fareySequenceDecodeBHist (fareySequenceEncodeBHist h) = h) ∧
      (∀ x : FareySequenceUp,
        fareySequenceFromEventFlow (fareySequenceToEventFlow x) = some x) ∧
        (∀ x y : FareySequenceUp,
          fareySequenceToEventFlow x = fareySequenceToEventFlow y → x = y) ∧
          fareySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨FareySequenceTasteGate_single_carrier_alignment_decode,
      FareySequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => FareySequenceTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.FareySequenceUp.TasteGate
