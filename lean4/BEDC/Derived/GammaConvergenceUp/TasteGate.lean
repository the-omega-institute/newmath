import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GammaConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GammaConvergenceUp : Type where
  | mk (X K L F A R Q E H C P N : BHist) : GammaConvergenceUp
  deriving DecidableEq

def GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist h

def GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem gammaConvergence_decode_encode_bhist :
    forall h : BHist,
      GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
        (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow :
    GammaConvergenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GammaConvergenceUp.mk X K L F A R Q E H C P N =>
      [[BMark.b0],
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist X,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist K,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist L,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist F,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist A,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist R,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist Q,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist E,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist H,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist C,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist P,
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist N]

def GammaConvergenceTasteGate_single_carrier_alignment_fields :
    GammaConvergenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GammaConvergenceUp.mk X K L F A R Q E H C P N => [X, K, L, F, A, R, Q, E, H, C, P, N]

def GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option GammaConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: X :: K :: L :: F :: A :: R :: Q :: E :: H :: C :: P :: N :: [] =>
      some
        (GammaConvergenceUp.mk
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist X)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist K)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist L)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist F)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist A)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist R)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist Q)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist E)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist H)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist C)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist P)
          (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem gammaConvergence_round_trip :
    forall x : GammaConvergenceUp,
      GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow
        (GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K L F A R Q E H C P N =>
      change
        some
          (GammaConvergenceUp.mk
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist X))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist K))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist L))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist F))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist A))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist R))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist Q))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist E))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist H))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist C))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist P))
            (GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (GammaConvergenceUp.mk X K L F A R Q E H C P N)
      rw [gammaConvergence_decode_encode_bhist X,
        gammaConvergence_decode_encode_bhist K,
        gammaConvergence_decode_encode_bhist L,
        gammaConvergence_decode_encode_bhist F,
        gammaConvergence_decode_encode_bhist A,
        gammaConvergence_decode_encode_bhist R,
        gammaConvergence_decode_encode_bhist Q,
        gammaConvergence_decode_encode_bhist E,
        gammaConvergence_decode_encode_bhist H,
        gammaConvergence_decode_encode_bhist C,
        gammaConvergence_decode_encode_bhist P,
        gammaConvergence_decode_encode_bhist N]

private theorem gammaConvergence_toEventFlow_injective {x y : GammaConvergenceUp} :
    GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow x =
      GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow x) =
        GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (gammaConvergence_round_trip x).symm
      (Eq.trans hread (gammaConvergence_round_trip y)))

instance gammaConvergenceBHistCarrier : BHistCarrier GammaConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow

instance gammaConvergenceChapterTasteGate : ChapterTasteGate GammaConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      GammaConvergenceTasteGate_single_carrier_alignment_fromEventFlow
        (GammaConvergenceTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact gammaConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gammaConvergence_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate GammaConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gammaConvergenceChapterTasteGate

theorem GammaConvergenceTasteGate_single_carrier_alignment :
    (forall X K L F A R Q E H C P N : BHist,
      GammaConvergenceTasteGate_single_carrier_alignment_fields
          (GammaConvergenceUp.mk X K L F A R Q E H C P N) =
        [X, K, L, F, A, R, Q, E, H, C, P, N]) ∧
      (forall h : BHist,
        GammaConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        GammaConvergenceTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨(by intros; rfl), gammaConvergence_decode_encode_bhist, rfl⟩

end BEDC.Derived.GammaConvergenceUp
