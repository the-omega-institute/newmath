import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotContinuedFractionBridgeUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotContinuedFractionBridgeUp : Type where
  | mk (S A F Q V I W R E H C P N : BHist) : SternBrocotContinuedFractionBridgeUp
  deriving DecidableEq

def sternBrocotContinuedFractionBridgeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotContinuedFractionBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotContinuedFractionBridgeEncodeBHist h

def sternBrocotContinuedFractionBridgeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotContinuedFractionBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotContinuedFractionBridgeDecodeBHist tail)

private theorem SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      sternBrocotContinuedFractionBridgeDecodeBHist
        (sternBrocotContinuedFractionBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotContinuedFractionBridgeFields :
    SternBrocotContinuedFractionBridgeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotContinuedFractionBridgeUp.mk S A F Q V I W R E H C P N =>
      [S, A, F, Q, V, I, W, R, E, H, C, P, N]

def sternBrocotContinuedFractionBridgeToEventFlow :
    SternBrocotContinuedFractionBridgeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (sternBrocotContinuedFractionBridgeFields x).map
        sternBrocotContinuedFractionBridgeEncodeBHist

def sternBrocotContinuedFractionBridgeFromEventFlow :
    EventFlow -> Option SternBrocotContinuedFractionBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | A :: restA =>
          match restA with
          | F :: restF =>
              match restF with
              | Q :: restQ =>
                  match restQ with
                  | V :: restV =>
                      match restV with
                      | I :: restI =>
                          match restI with
                          | W :: restW =>
                              match restW with
                              | R :: restR =>
                                  match restR with
                                  | E :: restE =>
                                      match restE with
                                      | H :: restH =>
                                          match restH with
                                          | C :: restC =>
                                              match restC with
                                              | P :: restP =>
                                                  match restP with
                                                  | N :: rest =>
                                                      match rest with
                                                      | [] =>
                                                          some
                                                            (SternBrocotContinuedFractionBridgeUp.mk
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist S)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist A)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist F)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist Q)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist V)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist I)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist W)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist R)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist E)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist H)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist C)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist P)
                                                              (sternBrocotContinuedFractionBridgeDecodeBHist N))
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

private theorem sternBrocotContinuedFractionBridge_mk_congr
    {S S' A A' F F' Q Q' V V' I I' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hA : A' = A) (hF : F' = F) (hQ : Q' = Q)
    (hV : V' = V) (hI : I' = I) (hW : W' = W) (hR : R' = R)
    (hE : E' = E) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    SternBrocotContinuedFractionBridgeUp.mk S' A' F' Q' V' I' W' R' E' H' C' P' N' =
      SternBrocotContinuedFractionBridgeUp.mk S A F Q V I W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hA
  cases hF
  cases hQ
  cases hV
  cases hI
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_round_trip :
    forall x : SternBrocotContinuedFractionBridgeUp,
      sternBrocotContinuedFractionBridgeFromEventFlow
        (sternBrocotContinuedFractionBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A F Q V I W R E H C P N =>
      exact
        congrArg some
          (sternBrocotContinuedFractionBridge_mk_congr
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode S)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode A)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode F)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode Q)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode V)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode I)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode W)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode R)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode E)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode H)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode C)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode P)
            (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode N))

private theorem sternBrocotContinuedFractionBridgeToEventFlow_injective
    {x y : SternBrocotContinuedFractionBridgeUp} :
    sternBrocotContinuedFractionBridgeToEventFlow x =
        sternBrocotContinuedFractionBridgeToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow x) =
        sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow y) :=
    congrArg sternBrocotContinuedFractionBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_round_trip y)))

instance sternBrocotContinuedFractionBridgeBHistCarrier :
    BHistCarrier SternBrocotContinuedFractionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotContinuedFractionBridgeToEventFlow
  fromEventFlow := sternBrocotContinuedFractionBridgeFromEventFlow

instance sternBrocotContinuedFractionBridgeChapterTasteGate :
    ChapterTasteGate SternBrocotContinuedFractionBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow x) =
        some x
    exact SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sternBrocotContinuedFractionBridgeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SternBrocotContinuedFractionBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sternBrocotContinuedFractionBridgeChapterTasteGate

theorem SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment :
    (forall h : BHist,
      sternBrocotContinuedFractionBridgeDecodeBHist
        (sternBrocotContinuedFractionBridgeEncodeBHist h) = h) ∧
      (forall x : SternBrocotContinuedFractionBridgeUp,
        sternBrocotContinuedFractionBridgeFromEventFlow
          (sternBrocotContinuedFractionBridgeToEventFlow x) = some x) ∧
      (forall x y : SternBrocotContinuedFractionBridgeUp,
        sternBrocotContinuedFractionBridgeToEventFlow x =
            sternBrocotContinuedFractionBridgeToEventFlow y ->
          x = y) ∧
      sternBrocotContinuedFractionBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_decode
  constructor
  · exact SternBrocotContinuedFractionBridgeTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact sternBrocotContinuedFractionBridgeToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.SternBrocotContinuedFractionBridgeUp
