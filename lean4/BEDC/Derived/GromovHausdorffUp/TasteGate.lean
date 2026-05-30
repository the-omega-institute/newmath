import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GromovHausdorffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GromovHausdorffUp : Type where
  | mk (X Y KX KY R D H Q U T C P N : BHist) : GromovHausdorffUp

def gromovHausdorffEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gromovHausdorffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gromovHausdorffEncodeBHist h

def gromovHausdorffDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gromovHausdorffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gromovHausdorffDecodeBHist tail)

private theorem GromovHausdorffTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gromovHausdorffFields : GromovHausdorffUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GromovHausdorffUp.mk X Y KX KY R D H Q U T C P N => [X, Y, KX, KY, R, D, H, Q, U, T, C, P, N]

def gromovHausdorffToEventFlow : GromovHausdorffUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gromovHausdorffFields x).map gromovHausdorffEncodeBHist

def gromovHausdorffFromEventFlow : EventFlow -> Option GromovHausdorffUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | Y :: restY =>
          match restY with
          | KX :: restKX =>
              match restKX with
              | KY :: restKY =>
                  match restKY with
                  | R :: restR =>
                      match restR with
                      | D :: restD =>
                          match restD with
                          | H :: restH =>
                              match restH with
                              | Q :: restQ =>
                                  match restQ with
                                  | U :: restU =>
                                      match restU with
                                      | T :: restT =>
                                          match restT with
                                          | C :: restC =>
                                              match restC with
                                              | P :: restP =>
                                                  match restP with
                                                  | N :: restN =>
                                                      match restN with
                                                      | [] =>
                                                          some
                                                            (GromovHausdorffUp.mk
                                                              (gromovHausdorffDecodeBHist X)
                                                              (gromovHausdorffDecodeBHist Y)
                                                              (gromovHausdorffDecodeBHist KX)
                                                              (gromovHausdorffDecodeBHist KY)
                                                              (gromovHausdorffDecodeBHist R)
                                                              (gromovHausdorffDecodeBHist D)
                                                              (gromovHausdorffDecodeBHist H)
                                                              (gromovHausdorffDecodeBHist Q)
                                                              (gromovHausdorffDecodeBHist U)
                                                              (gromovHausdorffDecodeBHist T)
                                                              (gromovHausdorffDecodeBHist C)
                                                              (gromovHausdorffDecodeBHist P)
                                                              (gromovHausdorffDecodeBHist N))
                                                      | _ :: _ => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem GromovHausdorffTasteGate_single_carrier_alignment_round_trip :
    forall x : GromovHausdorffUp,
      gromovHausdorffFromEventFlow (gromovHausdorffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y KX KY R D H Q U T C P N =>
      change
        some
            (GromovHausdorffUp.mk
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist X))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist Y))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist KX))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist KY))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist R))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist D))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist H))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist Q))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist U))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist T))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist C))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist P))
              (gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist N))) =
          some (GromovHausdorffUp.mk X Y KX KY R D H Q U T C P N)
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode X]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode Y]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode KX]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode KY]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode R]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode D]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode H]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode Q]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode U]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode T]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode C]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode P]
      rw [GromovHausdorffTasteGate_single_carrier_alignment_decode_encode N]

private theorem GromovHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GromovHausdorffUp} :
    gromovHausdorffToEventFlow x = gromovHausdorffToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gromovHausdorffFromEventFlow (gromovHausdorffToEventFlow x) =
        gromovHausdorffFromEventFlow (gromovHausdorffToEventFlow y) :=
    congrArg gromovHausdorffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GromovHausdorffTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GromovHausdorffTasteGate_single_carrier_alignment_round_trip y)))

instance gromovHausdorffBHistCarrier : BHistCarrier GromovHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gromovHausdorffToEventFlow
  fromEventFlow := gromovHausdorffFromEventFlow

instance gromovHausdorffChapterTasteGate : ChapterTasteGate GromovHausdorffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gromovHausdorffFromEventFlow (gromovHausdorffToEventFlow x) = some x
    exact GromovHausdorffTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GromovHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GromovHausdorffTasteGate_single_carrier_alignment :
    (forall h : BHist, gromovHausdorffDecodeBHist (gromovHausdorffEncodeBHist h) = h) ∧
      (forall x : GromovHausdorffUp,
        gromovHausdorffFromEventFlow (gromovHausdorffToEventFlow x) = some x) ∧
      (forall x y : GromovHausdorffUp,
        gromovHausdorffToEventFlow x = gromovHausdorffToEventFlow y -> x = y) ∧
      gromovHausdorffEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact GromovHausdorffTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact GromovHausdorffTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact GromovHausdorffTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.GromovHausdorffUp
