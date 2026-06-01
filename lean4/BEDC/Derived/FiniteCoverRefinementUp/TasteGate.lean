import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCoverRefinementUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCoverRefinementUp : Type where
  | mk (K D F Q U W H C P N : BHist) : FiniteCoverRefinementUp
  deriving DecidableEq

def finiteCoverRefinementEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCoverRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCoverRefinementEncodeBHist h

def finiteCoverRefinementDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCoverRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCoverRefinementDecodeBHist tail)

private theorem FiniteCoverRefinementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCoverRefinementFields : FiniteCoverRefinementUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCoverRefinementUp.mk K D F Q U W H C P N => [K, D, F, Q, U, W, H, C, P, N]

def finiteCoverRefinementToEventFlow : FiniteCoverRefinementUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map finiteCoverRefinementEncodeBHist (finiteCoverRefinementFields x)

def finiteCoverRefinementFromEventFlow (ef : EventFlow) : Option FiniteCoverRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | K :: restK =>
      match restK with
      | [] => none
      | D :: restD =>
          match restD with
          | [] => none
          | F :: restF =>
              match restF with
              | [] => none
              | Q :: restQ =>
                  match restQ with
                  | [] => none
                  | U :: restU =>
                      match restU with
                      | [] => none
                      | W :: restW =>
                          match restW with
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
                                                (FiniteCoverRefinementUp.mk
                                                  (finiteCoverRefinementDecodeBHist K)
                                                  (finiteCoverRefinementDecodeBHist D)
                                                  (finiteCoverRefinementDecodeBHist F)
                                                  (finiteCoverRefinementDecodeBHist Q)
                                                  (finiteCoverRefinementDecodeBHist U)
                                                  (finiteCoverRefinementDecodeBHist W)
                                                  (finiteCoverRefinementDecodeBHist H)
                                                  (finiteCoverRefinementDecodeBHist C)
                                                  (finiteCoverRefinementDecodeBHist P)
                                                  (finiteCoverRefinementDecodeBHist N))
                                          | _ :: _ => none

private theorem FiniteCoverRefinementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteCoverRefinementUp,
      finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K D F Q U W H C P N =>
      change
        some
          (FiniteCoverRefinementUp.mk
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist K))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist D))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist F))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist Q))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist U))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist W))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist H))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist C))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist P))
            (finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist N))) =
          some (FiniteCoverRefinementUp.mk K D F Q U W H C P N)
      rw [FiniteCoverRefinementTasteGate_single_carrier_alignment_decode K,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode D,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode F,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode Q,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode U,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode W,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode H,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode C,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode P,
        FiniteCoverRefinementTasteGate_single_carrier_alignment_decode N]

private theorem FiniteCoverRefinementTasteGate_single_carrier_alignment_injective
    {x y : FiniteCoverRefinementUp} :
    finiteCoverRefinementToEventFlow x = finiteCoverRefinementToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) =
        finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow y) :=
    congrArg finiteCoverRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteCoverRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteCoverRefinementTasteGate_single_carrier_alignment_round_trip y)))

instance finiteCoverRefinementBHistCarrier : BHistCarrier FiniteCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCoverRefinementToEventFlow
  fromEventFlow := finiteCoverRefinementFromEventFlow

instance finiteCoverRefinementChapterTasteGate : ChapterTasteGate FiniteCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) = some x
    exact FiniteCoverRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteCoverRefinementTasteGate_single_carrier_alignment_injective heq)

theorem FiniteCoverRefinementTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteCoverRefinementUp) ∧
      Nonempty (ChapterTasteGate FiniteCoverRefinementUp) ∧
        (∀ h : BHist,
          finiteCoverRefinementDecodeBHist (finiteCoverRefinementEncodeBHist h) = h) ∧
          (∀ x : FiniteCoverRefinementUp,
            finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) =
              some x) ∧
            finiteCoverRefinementEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              finiteCoverRefinementEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro {
        toEventFlow := finiteCoverRefinementToEventFlow
        fromEventFlow := finiteCoverRefinementFromEventFlow
      },
      Nonempty.intro {
        round_trip := by
          intro x
          change finiteCoverRefinementFromEventFlow (finiteCoverRefinementToEventFlow x) = some x
          exact FiniteCoverRefinementTasteGate_single_carrier_alignment_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (FiniteCoverRefinementTasteGate_single_carrier_alignment_injective heq)
      },
      FiniteCoverRefinementTasteGate_single_carrier_alignment_decode,
      FiniteCoverRefinementTasteGate_single_carrier_alignment_round_trip,
      rfl,
      rfl⟩

end BEDC.Derived.FiniteCoverRefinementUp.TasteGate
