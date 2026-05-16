import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyLimitWitnessLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyLimitWitnessLedgerUp : Type where
  | mk (D T S W G R H C P N A : BHist) : CauchyLimitWitnessLedgerUp
  deriving DecidableEq

def cauchyLimitWitnessLedgerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyLimitWitnessLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyLimitWitnessLedgerEncodeBHist h

def cauchyLimitWitnessLedgerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyLimitWitnessLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyLimitWitnessLedgerDecodeBHist tail)

private theorem cauchyLimitWitnessLedgerDecode_encode_bhist :
    ∀ h : BHist,
      cauchyLimitWitnessLedgerDecodeBHist
        (cauchyLimitWitnessLedgerEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyLimitWitnessLedgerFields :
    CauchyLimitWitnessLedgerUp → List BHist
  | CauchyLimitWitnessLedgerUp.mk D T S W G R H C P N A =>
      [D, T, S, W, G, R, H, C, P, N, A]

def cauchyLimitWitnessLedgerToEventFlow :
    CauchyLimitWitnessLedgerUp → EventFlow
  | CauchyLimitWitnessLedgerUp.mk D T S W G R H C P N A =>
      [cauchyLimitWitnessLedgerEncodeBHist D,
        cauchyLimitWitnessLedgerEncodeBHist T,
        cauchyLimitWitnessLedgerEncodeBHist S,
        cauchyLimitWitnessLedgerEncodeBHist W,
        cauchyLimitWitnessLedgerEncodeBHist G,
        cauchyLimitWitnessLedgerEncodeBHist R,
        cauchyLimitWitnessLedgerEncodeBHist H,
        cauchyLimitWitnessLedgerEncodeBHist C,
        cauchyLimitWitnessLedgerEncodeBHist P,
        cauchyLimitWitnessLedgerEncodeBHist N,
        cauchyLimitWitnessLedgerEncodeBHist A]

def cauchyLimitWitnessLedgerFromEventFlow :
    EventFlow → Option CauchyLimitWitnessLedgerUp
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | G :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | A :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyLimitWitnessLedgerUp.mk
                                                      (cauchyLimitWitnessLedgerDecodeBHist D)
                                                      (cauchyLimitWitnessLedgerDecodeBHist T)
                                                      (cauchyLimitWitnessLedgerDecodeBHist S)
                                                      (cauchyLimitWitnessLedgerDecodeBHist W)
                                                      (cauchyLimitWitnessLedgerDecodeBHist G)
                                                      (cauchyLimitWitnessLedgerDecodeBHist R)
                                                      (cauchyLimitWitnessLedgerDecodeBHist H)
                                                      (cauchyLimitWitnessLedgerDecodeBHist C)
                                                      (cauchyLimitWitnessLedgerDecodeBHist P)
                                                      (cauchyLimitWitnessLedgerDecodeBHist N)
                                                      (cauchyLimitWitnessLedgerDecodeBHist A))
                                              | _ :: _ => none

private theorem cauchyLimitWitnessLedger_mk_congr
    {D D' T T' S S' W W' G G' R R' H H' C C' P P' N N' A A' : BHist}
    (hD : D' = D)
    (hT : T' = T)
    (hS : S' = S)
    (hW : W' = W)
    (hG : G' = G)
    (hR : R' = R)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N)
    (hA : A' = A) :
    CauchyLimitWitnessLedgerUp.mk D' T' S' W' G' R' H' C' P' N' A' =
      CauchyLimitWitnessLedgerUp.mk D T S W G R H C P N A := by
  cases hD
  cases hT
  cases hS
  cases hW
  cases hG
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  cases hA
  rfl

private theorem cauchyLimitWitnessLedger_round_trip :
    ∀ x : CauchyLimitWitnessLedgerUp,
      cauchyLimitWitnessLedgerFromEventFlow
        (cauchyLimitWitnessLedgerToEventFlow x) = some x := by
  intro x
  cases x with
  | mk D T S W G R H C P N A =>
      change
        some
          (CauchyLimitWitnessLedgerUp.mk
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist D))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist T))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist S))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist W))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist G))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist R))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist H))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist C))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist P))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist N))
            (cauchyLimitWitnessLedgerDecodeBHist
              (cauchyLimitWitnessLedgerEncodeBHist A))) =
          some (CauchyLimitWitnessLedgerUp.mk D T S W G R H C P N A)
      exact
        congrArg some
          (cauchyLimitWitnessLedger_mk_congr
            (cauchyLimitWitnessLedgerDecode_encode_bhist D)
            (cauchyLimitWitnessLedgerDecode_encode_bhist T)
            (cauchyLimitWitnessLedgerDecode_encode_bhist S)
            (cauchyLimitWitnessLedgerDecode_encode_bhist W)
            (cauchyLimitWitnessLedgerDecode_encode_bhist G)
            (cauchyLimitWitnessLedgerDecode_encode_bhist R)
            (cauchyLimitWitnessLedgerDecode_encode_bhist H)
            (cauchyLimitWitnessLedgerDecode_encode_bhist C)
            (cauchyLimitWitnessLedgerDecode_encode_bhist P)
            (cauchyLimitWitnessLedgerDecode_encode_bhist N)
            (cauchyLimitWitnessLedgerDecode_encode_bhist A))

private theorem cauchyLimitWitnessLedgerToEventFlow_injective
    {x y : CauchyLimitWitnessLedgerUp} :
    cauchyLimitWitnessLedgerToEventFlow x =
      cauchyLimitWitnessLedgerToEventFlow y → x = y := by
  intro heq
  have hread :
      cauchyLimitWitnessLedgerFromEventFlow
          (cauchyLimitWitnessLedgerToEventFlow x) =
        cauchyLimitWitnessLedgerFromEventFlow
          (cauchyLimitWitnessLedgerToEventFlow y) :=
    congrArg cauchyLimitWitnessLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyLimitWitnessLedger_round_trip x).symm
      (Eq.trans hread (cauchyLimitWitnessLedger_round_trip y)))

private theorem cauchyLimitWitnessLedger_fields_faithful :
    ∀ x y : CauchyLimitWitnessLedgerUp,
      cauchyLimitWitnessLedgerFields x =
        cauchyLimitWitnessLedgerFields y → x = y := by
  intro x y hfields
  cases x with
  | mk D T S W G R H C P N A =>
      cases y with
      | mk D' T' S' W' G' R' H' C' P' N' A' =>
          injection hfields with hD htail0
          injection htail0 with hT htail1
          injection htail1 with hS htail2
          injection htail2 with hW htail3
          injection htail3 with hG htail4
          injection htail4 with hR htail5
          injection htail5 with hH htail6
          injection htail6 with hC htail7
          injection htail7 with hP htail8
          injection htail8 with hN htail9
          injection htail9 with hA _hNil
          cases hD
          cases hT
          cases hS
          cases hW
          cases hG
          cases hR
          cases hH
          cases hC
          cases hP
          cases hN
          cases hA
          rfl

instance cauchyLimitWitnessLedgerBHistCarrier :
    BHistCarrier CauchyLimitWitnessLedgerUp where
  toEventFlow := cauchyLimitWitnessLedgerToEventFlow
  fromEventFlow := cauchyLimitWitnessLedgerFromEventFlow

instance cauchyLimitWitnessLedgerChapterTasteGate :
    ChapterTasteGate CauchyLimitWitnessLedgerUp where
  round_trip := cauchyLimitWitnessLedger_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyLimitWitnessLedgerToEventFlow_injective heq)

instance cauchyLimitWitnessLedgerFieldFaithful :
    FieldFaithful CauchyLimitWitnessLedgerUp where
  fields := cauchyLimitWitnessLedgerFields
  field_faithful := cauchyLimitWitnessLedger_fields_faithful

instance cauchyLimitWitnessLedgerNontrivial :
    Nontrivial CauchyLimitWitnessLedgerUp where
  witness_pair :=
    ⟨CauchyLimitWitnessLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyLimitWitnessLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyLimitWitnessLedgerUp :=
  cauchyLimitWitnessLedgerChapterTasteGate

theorem CauchyLimitWitnessLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyLimitWitnessLedgerDecodeBHist
        (cauchyLimitWitnessLedgerEncodeBHist h) = h) ∧
      (∀ x : CauchyLimitWitnessLedgerUp,
        cauchyLimitWitnessLedgerFromEventFlow
          (cauchyLimitWitnessLedgerToEventFlow x) = some x) ∧
        (∀ x y : CauchyLimitWitnessLedgerUp,
          cauchyLimitWitnessLedgerToEventFlow x =
            cauchyLimitWitnessLedgerToEventFlow y → x = y) ∧
            cauchyLimitWitnessLedgerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            cauchyLimitWitnessLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
              cauchyLimitWitnessLedgerDecodeBHist ([] : RawEvent) = BHist.Empty := by
  exact
    ⟨cauchyLimitWitnessLedgerDecode_encode_bhist,
      cauchyLimitWitnessLedger_round_trip,
      @cauchyLimitWitnessLedgerToEventFlow_injective,
      rfl,
      rfl,
      rfl⟩

end BEDC.Derived.CauchyLimitWitnessLedgerUp
