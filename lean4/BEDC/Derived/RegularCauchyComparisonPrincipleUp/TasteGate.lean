import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyComparisonPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyComparisonPrincipleUp : Type where
  | mk (X Y W D E T Q R H C K N : BHist) : RegularCauchyComparisonPrincipleUp
  deriving DecidableEq

def regularCauchyComparisonPrincipleEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyComparisonPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyComparisonPrincipleEncodeBHist h

def regularCauchyComparisonPrincipleDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyComparisonPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyComparisonPrincipleDecodeBHist tail)

private theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyComparisonPrincipleFields :
    RegularCauchyComparisonPrincipleUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyComparisonPrincipleUp.mk X Y W D E T Q R H C K N =>
      [X, Y, W, D, E, T, Q, R, H, C, K, N]

def regularCauchyComparisonPrincipleToEventFlow :
    RegularCauchyComparisonPrincipleUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyComparisonPrincipleFields x).map
        regularCauchyComparisonPrincipleEncodeBHist

def regularCauchyComparisonPrincipleFromEventFlow :
    EventFlow -> Option RegularCauchyComparisonPrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | Y :: restY =>
          match restY with
          | W :: restW =>
              match restW with
              | D :: restD =>
                  match restD with
                  | E :: restE =>
                      match restE with
                      | T :: restT =>
                          match restT with
                          | Q :: restQ =>
                              match restQ with
                              | R :: restR =>
                                  match restR with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | K :: restK =>
                                              match restK with
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (RegularCauchyComparisonPrincipleUp.mk
                                                          (regularCauchyComparisonPrincipleDecodeBHist X)
                                                          (regularCauchyComparisonPrincipleDecodeBHist Y)
                                                          (regularCauchyComparisonPrincipleDecodeBHist W)
                                                          (regularCauchyComparisonPrincipleDecodeBHist D)
                                                          (regularCauchyComparisonPrincipleDecodeBHist E)
                                                          (regularCauchyComparisonPrincipleDecodeBHist T)
                                                          (regularCauchyComparisonPrincipleDecodeBHist Q)
                                                          (regularCauchyComparisonPrincipleDecodeBHist R)
                                                          (regularCauchyComparisonPrincipleDecodeBHist H)
                                                          (regularCauchyComparisonPrincipleDecodeBHist C)
                                                          (regularCauchyComparisonPrincipleDecodeBHist K)
                                                          (regularCauchyComparisonPrincipleDecodeBHist N))
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

private theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_mk_congr
    {X X' Y Y' W W' D D' E E' T T' Q Q' R R' H H' C C' K K' N N' : BHist}
    (hX : X' = X) (hY : Y' = Y) (hW : W' = W) (hD : D' = D)
    (hE : E' = E) (hT : T' = T) (hQ : Q' = Q) (hR : R' = R)
    (hH : H' = H) (hC : C' = C) (hK : K' = K) (hN : N' = N) :
    RegularCauchyComparisonPrincipleUp.mk X' Y' W' D' E' T' Q' R' H' C' K' N' =
      RegularCauchyComparisonPrincipleUp.mk X Y W D E T Q R H C K N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hY
  cases hW
  cases hD
  cases hE
  cases hT
  cases hQ
  cases hR
  cases hH
  cases hC
  cases hK
  cases hN
  rfl

private theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyComparisonPrincipleUp,
      regularCauchyComparisonPrincipleFromEventFlow
        (regularCauchyComparisonPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D E T Q R H C K N =>
      exact
        congrArg some
          (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_mk_congr
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode X)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode Y)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode W)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode D)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode E)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode T)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode Q)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode R)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode H)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode C)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode K)
            (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode N))

private theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyComparisonPrincipleUp} :
    regularCauchyComparisonPrincipleToEventFlow x =
        regularCauchyComparisonPrincipleToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyComparisonPrincipleFromEventFlow
          (regularCauchyComparisonPrincipleToEventFlow x) =
        regularCauchyComparisonPrincipleFromEventFlow
          (regularCauchyComparisonPrincipleToEventFlow y) :=
    congrArg regularCauchyComparisonPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyComparisonPrincipleBHistCarrier :
    BHistCarrier RegularCauchyComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyComparisonPrincipleToEventFlow
  fromEventFlow := regularCauchyComparisonPrincipleFromEventFlow

instance regularCauchyComparisonPrincipleChapterTasteGate :
    ChapterTasteGate RegularCauchyComparisonPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyComparisonPrincipleFromEventFlow
        (regularCauchyComparisonPrincipleToEventFlow x) = some x
    exact RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyComparisonPrincipleDecodeBHist
        (regularCauchyComparisonPrincipleEncodeBHist h) = h) ∧
      (forall x : RegularCauchyComparisonPrincipleUp,
        regularCauchyComparisonPrincipleFromEventFlow
          (regularCauchyComparisonPrincipleToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyComparisonPrincipleUp,
          regularCauchyComparisonPrincipleToEventFlow x =
              regularCauchyComparisonPrincipleToEventFlow y ->
            x = y) ∧
          regularCauchyComparisonPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          RegularCauchyComparisonPrincipleTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.RegularCauchyComparisonPrincipleUp
