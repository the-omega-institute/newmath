import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardErrorEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PicardErrorEstimateUp : Type where
  | mk (X d T ratio I r M R E H C P N : BHist) : PicardErrorEstimateUp
  deriving DecidableEq

def picardErrorEstimateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardErrorEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardErrorEstimateEncodeBHist h

def picardErrorEstimateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardErrorEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardErrorEstimateDecodeBHist tail)

private theorem picardErrorEstimate_decode_encode :
    ∀ h : BHist, picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardErrorEstimateFields : PicardErrorEstimateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardErrorEstimateUp.mk X d T ratio I r M R E H C P N =>
      [X, d, T, ratio, I, r, M, R, E, H, C, P, N]

def picardErrorEstimateToEventFlow : PicardErrorEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (picardErrorEstimateFields x).map picardErrorEstimateEncodeBHist

def picardErrorEstimateFromEventFlow : EventFlow → Option PicardErrorEstimateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: restD =>
      match restD with
      | [] => none
      | d :: restT =>
          match restT with
          | [] => none
          | T :: restRatio =>
              match restRatio with
              | [] => none
              | ratio :: restI =>
                  match restI with
                  | [] => none
                  | I :: restR =>
                      match restR with
                      | [] => none
                      | r :: restM =>
                          match restM with
                          | [] => none
                          | M :: restReg =>
                              match restReg with
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
                                                            (PicardErrorEstimateUp.mk
                                                              (picardErrorEstimateDecodeBHist X)
                                                              (picardErrorEstimateDecodeBHist d)
                                                              (picardErrorEstimateDecodeBHist T)
                                                              (picardErrorEstimateDecodeBHist ratio)
                                                              (picardErrorEstimateDecodeBHist I)
                                                              (picardErrorEstimateDecodeBHist r)
                                                              (picardErrorEstimateDecodeBHist M)
                                                              (picardErrorEstimateDecodeBHist R)
                                                              (picardErrorEstimateDecodeBHist E)
                                                              (picardErrorEstimateDecodeBHist H)
                                                              (picardErrorEstimateDecodeBHist C)
                                                              (picardErrorEstimateDecodeBHist P)
                                                              (picardErrorEstimateDecodeBHist N))
                                                      | _ :: _ => none

private theorem picardErrorEstimate_round_trip :
    ∀ x : PicardErrorEstimateUp,
      picardErrorEstimateFromEventFlow (picardErrorEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d T ratio I r M R E H C P N =>
      change
        some
          (PicardErrorEstimateUp.mk
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist X))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist d))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist T))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist ratio))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist I))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist r))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist M))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist R))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist E))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist H))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist C))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist P))
            (picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist N))) =
          some (PicardErrorEstimateUp.mk X d T ratio I r M R E H C P N)
      rw [picardErrorEstimate_decode_encode X, picardErrorEstimate_decode_encode d,
        picardErrorEstimate_decode_encode T, picardErrorEstimate_decode_encode ratio,
        picardErrorEstimate_decode_encode I, picardErrorEstimate_decode_encode r,
        picardErrorEstimate_decode_encode M, picardErrorEstimate_decode_encode R,
        picardErrorEstimate_decode_encode E, picardErrorEstimate_decode_encode H,
        picardErrorEstimate_decode_encode C, picardErrorEstimate_decode_encode P,
        picardErrorEstimate_decode_encode N]

private theorem picardErrorEstimateToEventFlow_injective {x y : PicardErrorEstimateUp} :
    picardErrorEstimateToEventFlow x = picardErrorEstimateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardErrorEstimateFromEventFlow (picardErrorEstimateToEventFlow x) =
        picardErrorEstimateFromEventFlow (picardErrorEstimateToEventFlow y) :=
    congrArg picardErrorEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (picardErrorEstimate_round_trip x).symm
      (Eq.trans hread (picardErrorEstimate_round_trip y)))

instance picardErrorEstimateBHistCarrier : BHistCarrier PicardErrorEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardErrorEstimateToEventFlow
  fromEventFlow := picardErrorEstimateFromEventFlow

instance picardErrorEstimateChapterTasteGate : ChapterTasteGate PicardErrorEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change picardErrorEstimateFromEventFlow (picardErrorEstimateToEventFlow x) = some x
    exact picardErrorEstimate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (picardErrorEstimateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PicardErrorEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  picardErrorEstimateChapterTasteGate

theorem PicardErrorEstimateTasteGate_single_carrier_alignment :
    (∃ _gate : ChapterTasteGate PicardErrorEstimateUp,
        ∀ h : BHist, picardErrorEstimateDecodeBHist (picardErrorEstimateEncodeBHist h) = h) ∧
      picardErrorEstimateEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨picardErrorEstimateChapterTasteGate, picardErrorEstimate_decode_encode⟩, rfl⟩

end BEDC.Derived.PicardErrorEstimateUp
