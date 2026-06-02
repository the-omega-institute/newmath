import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChurchRosserUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChurchRosserUp : Type where
  | mk : (T L S NF P D C O H Q G M : BHist) → ChurchRosserUp
  deriving DecidableEq

def churchRosserEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: churchRosserEncodeBHist h
  | BHist.e1 h => BMark.b1 :: churchRosserEncodeBHist h

def churchRosserDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (churchRosserDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (churchRosserDecodeBHist tail)

private theorem churchRosserDecode_encode_bhist :
    ∀ h : BHist, churchRosserDecodeBHist (churchRosserEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem churchRosser_mk_congr
    {T T' L L' S S' NF NF' P P' D D' C C' O O' H H' Q Q' G G' M M' : BHist}
    (hT : T' = T)
    (hL : L' = L)
    (hS : S' = S)
    (hNF : NF' = NF)
    (hP : P' = P)
    (hD : D' = D)
    (hC : C' = C)
    (hO : O' = O)
    (hH : H' = H)
    (hQ : Q' = Q)
    (hG : G' = G)
    (hM : M' = M) :
    ChurchRosserUp.mk T' L' S' NF' P' D' C' O' H' Q' G' M' =
      ChurchRosserUp.mk T L S NF P D C O H Q G M := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hL
  cases hS
  cases hNF
  cases hP
  cases hD
  cases hC
  cases hO
  cases hH
  cases hQ
  cases hG
  cases hM
  rfl

def churchRosserToEventFlow : ChurchRosserUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChurchRosserUp.mk T L S NF P D C O H Q G M =>
      [churchRosserEncodeBHist T,
        churchRosserEncodeBHist L,
        churchRosserEncodeBHist S,
        churchRosserEncodeBHist NF,
        churchRosserEncodeBHist P,
        churchRosserEncodeBHist D,
        churchRosserEncodeBHist C,
        churchRosserEncodeBHist O,
        churchRosserEncodeBHist H,
        churchRosserEncodeBHist Q,
        churchRosserEncodeBHist G,
        churchRosserEncodeBHist M]

def churchRosserFromEventFlow : EventFlow → Option ChurchRosserUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest =>
      match rest with
      | [] => none
      | L :: rest =>
          match rest with
          | [] => none
          | S :: rest =>
              match rest with
              | [] => none
              | NF :: rest =>
                  match rest with
                  | [] => none
                  | P :: rest =>
                      match rest with
                      | [] => none
                      | D :: rest =>
                          match rest with
                          | [] => none
                          | C :: rest =>
                              match rest with
                              | [] => none
                              | O :: rest =>
                                  match rest with
                                  | [] => none
                                  | H :: rest =>
                                      match rest with
                                      | [] => none
                                      | Q :: rest =>
                                          match rest with
                                          | [] => none
                                          | G :: rest =>
                                              match rest with
                                              | [] => none
                                              | M :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (ChurchRosserUp.mk
                                                          (churchRosserDecodeBHist T)
                                                          (churchRosserDecodeBHist L)
                                                          (churchRosserDecodeBHist S)
                                                          (churchRosserDecodeBHist NF)
                                                          (churchRosserDecodeBHist P)
                                                          (churchRosserDecodeBHist D)
                                                          (churchRosserDecodeBHist C)
                                                          (churchRosserDecodeBHist O)
                                                          (churchRosserDecodeBHist H)
                                                          (churchRosserDecodeBHist Q)
                                                          (churchRosserDecodeBHist G)
                                                          (churchRosserDecodeBHist M))
                                                  | _ :: _ => none

def churchRosserFields : ChurchRosserUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChurchRosserUp.mk T L S NF P D C O H Q G M =>
      [T, L, S, NF, P, D, C, O, H, Q, G, M]

private theorem churchRosser_round_trip :
    ∀ x : ChurchRosserUp,
      churchRosserFromEventFlow (churchRosserToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T L S NF P D C O H Q G M =>
      exact
        congrArg some
          (churchRosser_mk_congr
            (churchRosserDecode_encode_bhist T)
            (churchRosserDecode_encode_bhist L)
            (churchRosserDecode_encode_bhist S)
            (churchRosserDecode_encode_bhist NF)
            (churchRosserDecode_encode_bhist P)
            (churchRosserDecode_encode_bhist D)
            (churchRosserDecode_encode_bhist C)
            (churchRosserDecode_encode_bhist O)
            (churchRosserDecode_encode_bhist H)
            (churchRosserDecode_encode_bhist Q)
            (churchRosserDecode_encode_bhist G)
            (churchRosserDecode_encode_bhist M))

private theorem churchRosserToEventFlow_injective {x y : ChurchRosserUp} :
    churchRosserToEventFlow x = churchRosserToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      churchRosserFromEventFlow (churchRosserToEventFlow x) =
        churchRosserFromEventFlow (churchRosserToEventFlow y) :=
    congrArg churchRosserFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (churchRosser_round_trip x).symm
      (Eq.trans hread (churchRosser_round_trip y)))

private theorem churchRosserFields_faithful :
    ∀ x y : ChurchRosserUp, churchRosserFields x = churchRosserFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T1 L1 S1 NF1 P1 D1 C1 O1 H1 Q1 G1 M1 =>
      cases y with
      | mk T2 L2 S2 NF2 P2 D2 C2 O2 H2 Q2 G2 M2 =>
          cases h
          rfl

instance churchRosserBHistCarrier : BHistCarrier ChurchRosserUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := churchRosserToEventFlow
  fromEventFlow := churchRosserFromEventFlow

instance churchRosserChapterTasteGate : ChapterTasteGate ChurchRosserUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change churchRosserFromEventFlow (churchRosserToEventFlow x) = some x
    exact churchRosser_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (churchRosserToEventFlow_injective heq)

instance churchRosserFieldFaithful : FieldFaithful ChurchRosserUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := churchRosserFields
  field_faithful := churchRosserFields_faithful

instance churchRosserNontrivial : Nontrivial ChurchRosserUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChurchRosserUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ChurchRosserUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ChurchRosserUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem ChurchRosserTasteGate_single_carrier_alignment :
    (∀ h : BHist, churchRosserDecodeBHist (churchRosserEncodeBHist h) = h) ∧
      (∀ x : ChurchRosserUp,
        churchRosserFromEventFlow (churchRosserToEventFlow x) = some x) ∧
        (∀ x y : ChurchRosserUp,
          churchRosserToEventFlow x = churchRosserToEventFlow y → x = y) ∧
          churchRosserEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact churchRosserDecode_encode_bhist h
  · constructor
    · intro x
      exact churchRosser_round_trip x
    · constructor
      · intro x y heq
        exact churchRosserToEventFlow_injective heq
      · rfl

end BEDC.Derived.ChurchRosserUp
