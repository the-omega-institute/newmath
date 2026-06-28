import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HilbertCurveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HilbertCurveUp : Type where
  | mk (A Q O F X Y B T C K N : BHist) : HilbertCurveUp
  deriving DecidableEq

def hilbertCurveEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hilbertCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hilbertCurveEncodeBHist h

def hilbertCurveDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hilbertCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hilbertCurveDecodeBHist tail)

private theorem HilbertCurveTasteGate_single_carrier_alignment_decode :
    forall h : BHist, hilbertCurveDecodeBHist (hilbertCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hilbertCurveToEventFlow :
    HilbertCurveUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HilbertCurveUp.mk A Q O F X Y B T C K N =>
      [hilbertCurveEncodeBHist A,
        hilbertCurveEncodeBHist Q,
        hilbertCurveEncodeBHist O,
        hilbertCurveEncodeBHist F,
        hilbertCurveEncodeBHist X,
        hilbertCurveEncodeBHist Y,
        hilbertCurveEncodeBHist B,
        hilbertCurveEncodeBHist T,
        hilbertCurveEncodeBHist C,
        hilbertCurveEncodeBHist K,
        hilbertCurveEncodeBHist N]

def hilbertCurveFromEventFlow :
    EventFlow -> Option HilbertCurveUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | X :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Y :: rest5 =>
                          match rest5 with
                          | [] => none
                          | B :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | K :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (HilbertCurveUp.mk
                                                      (hilbertCurveDecodeBHist A)
                                                      (hilbertCurveDecodeBHist Q)
                                                      (hilbertCurveDecodeBHist O)
                                                      (hilbertCurveDecodeBHist F)
                                                      (hilbertCurveDecodeBHist X)
                                                      (hilbertCurveDecodeBHist Y)
                                                      (hilbertCurveDecodeBHist B)
                                                      (hilbertCurveDecodeBHist T)
                                                      (hilbertCurveDecodeBHist C)
                                                      (hilbertCurveDecodeBHist K)
                                                      (hilbertCurveDecodeBHist N))
                                              | _ :: _ => none

private theorem HilbertCurveTasteGate_single_carrier_alignment_round_trip :
    forall x : HilbertCurveUp,
      hilbertCurveFromEventFlow
        (hilbertCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q O F X Y B T C K N =>
      change
        some
          (HilbertCurveUp.mk
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist A))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist Q))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist O))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist F))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist X))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist Y))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist B))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist T))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist C))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist K))
            (hilbertCurveDecodeBHist (hilbertCurveEncodeBHist N))) =
          some (HilbertCurveUp.mk A Q O F X Y B T C K N)
      rw [HilbertCurveTasteGate_single_carrier_alignment_decode A,
        HilbertCurveTasteGate_single_carrier_alignment_decode Q,
        HilbertCurveTasteGate_single_carrier_alignment_decode O,
        HilbertCurveTasteGate_single_carrier_alignment_decode F,
        HilbertCurveTasteGate_single_carrier_alignment_decode X,
        HilbertCurveTasteGate_single_carrier_alignment_decode Y,
        HilbertCurveTasteGate_single_carrier_alignment_decode B,
        HilbertCurveTasteGate_single_carrier_alignment_decode T,
        HilbertCurveTasteGate_single_carrier_alignment_decode C,
        HilbertCurveTasteGate_single_carrier_alignment_decode K,
        HilbertCurveTasteGate_single_carrier_alignment_decode N]

private theorem hilbertCurveToEventFlow_injective
    {x y : HilbertCurveUp} :
    hilbertCurveToEventFlow x =
        hilbertCurveToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hilbertCurveFromEventFlow
          (hilbertCurveToEventFlow x) =
        hilbertCurveFromEventFlow
          (hilbertCurveToEventFlow y) :=
    congrArg hilbertCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HilbertCurveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HilbertCurveTasteGate_single_carrier_alignment_round_trip y)))

instance hilbertCurveBHistCarrier : BHistCarrier HilbertCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hilbertCurveToEventFlow
  fromEventFlow := hilbertCurveFromEventFlow

instance hilbertCurveChapterTasteGate : ChapterTasteGate HilbertCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hilbertCurveFromEventFlow
        (hilbertCurveToEventFlow x) = some x
    exact HilbertCurveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hilbertCurveToEventFlow_injective heq)

theorem HilbertCurveTasteGate_single_carrier_alignment :
    (forall h : BHist, hilbertCurveDecodeBHist (hilbertCurveEncodeBHist h) = h) /\
      Nonempty (BHistCarrier HilbertCurveUp) /\
        Nonempty (ChapterTasteGate HilbertCurveUp) /\
          hilbertCurveEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HilbertCurveTasteGate_single_carrier_alignment_decode,
      ⟨hilbertCurveBHistCarrier⟩,
      ⟨hilbertCurveChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.HilbertCurveUp
