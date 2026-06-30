import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KoopmanOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KoopmanOperatorUp : Type where
  | mk (X T F O W R E A H C P N : BHist) : KoopmanOperatorUp
  deriving DecidableEq

def koopmanOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: koopmanOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: koopmanOperatorEncodeBHist h

def koopmanOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (koopmanOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (koopmanOperatorDecodeBHist tail)

private theorem KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist, koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def koopmanOperatorFields : KoopmanOperatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KoopmanOperatorUp.mk X T F O W R E A H C P N => [X, T, F, O, W, R, E, A, H, C, P, N]

def koopmanOperatorToEventFlow : KoopmanOperatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (koopmanOperatorFields x).map koopmanOperatorEncodeBHist

def koopmanOperatorFromEventFlow : EventFlow → Option KoopmanOperatorUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | T :: restT =>
          match restT with
          | F :: restF =>
              match restF with
              | O :: restO =>
                  match restO with
                  | W :: restW =>
                      match restW with
                      | R :: restR =>
                          match restR with
                          | E :: restE =>
                              match restE with
                              | A :: restA =>
                                  match restA with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (KoopmanOperatorUp.mk
                                                          (koopmanOperatorDecodeBHist X)
                                                          (koopmanOperatorDecodeBHist T)
                                                          (koopmanOperatorDecodeBHist F)
                                                          (koopmanOperatorDecodeBHist O)
                                                          (koopmanOperatorDecodeBHist W)
                                                          (koopmanOperatorDecodeBHist R)
                                                          (koopmanOperatorDecodeBHist E)
                                                          (koopmanOperatorDecodeBHist A)
                                                          (koopmanOperatorDecodeBHist H)
                                                          (koopmanOperatorDecodeBHist C)
                                                          (koopmanOperatorDecodeBHist P)
                                                          (koopmanOperatorDecodeBHist N))
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

private theorem KoopmanOperatorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KoopmanOperatorUp,
      koopmanOperatorFromEventFlow (koopmanOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T F O W R E A H C P N =>
      change
        some
          (KoopmanOperatorUp.mk
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist X))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist T))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist F))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist O))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist W))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist R))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist E))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist A))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist H))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist C))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist P))
            (koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist N))) =
          some (KoopmanOperatorUp.mk X T F O W R E A H C P N)
      rw [KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist X,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist T,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist F,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist O,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist W,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist R,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist E,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist A,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist H,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist C,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist P,
        KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist N]

private theorem koopmanOperatorToEventFlow_injective {x y : KoopmanOperatorUp} :
    koopmanOperatorToEventFlow x = koopmanOperatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      koopmanOperatorFromEventFlow (koopmanOperatorToEventFlow x) =
        koopmanOperatorFromEventFlow (koopmanOperatorToEventFlow y) :=
    congrArg koopmanOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KoopmanOperatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KoopmanOperatorTasteGate_single_carrier_alignment_round_trip y)))

theorem KoopmanOperatorTasteGate_single_carrier_alignment_field_faithful :
    forall x y : KoopmanOperatorUp, koopmanOperatorFields x = koopmanOperatorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X T F O W R E A H C P N =>
      cases y with
      | mk X' T' F' O' W' R' E' A' H' C' P' N' =>
          cases hfields
          rfl

instance koopmanOperatorBHistCarrier : BHistCarrier KoopmanOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := koopmanOperatorToEventFlow
  fromEventFlow := koopmanOperatorFromEventFlow

instance koopmanOperatorChapterTasteGate : ChapterTasteGate KoopmanOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (KoopmanOperatorTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (koopmanOperatorToEventFlow_injective heq)

instance koopmanOperatorFieldFaithful : FieldFaithful KoopmanOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := koopmanOperatorFields
  field_faithful := KoopmanOperatorTasteGate_single_carrier_alignment_field_faithful

instance koopmanOperatorNontrivial : BEDC.Meta.TasteGate.Nontrivial KoopmanOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KoopmanOperatorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KoopmanOperatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KoopmanOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  koopmanOperatorChapterTasteGate

theorem KoopmanOperatorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KoopmanOperatorUp) ∧
      Nonempty (FieldFaithful KoopmanOperatorUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial KoopmanOperatorUp) ∧
      (∀ h : BHist, koopmanOperatorDecodeBHist (koopmanOperatorEncodeBHist h) = h) ∧
      koopmanOperatorDecodeBHist [BMark.b0] = BHist.e0 BHist.Empty ∧
      ∀ x : KoopmanOperatorUp,
        koopmanOperatorFromEventFlow (koopmanOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨koopmanOperatorChapterTasteGate⟩
  constructor
  · exact ⟨koopmanOperatorFieldFaithful⟩
  constructor
  · exact ⟨koopmanOperatorNontrivial⟩
  constructor
  · exact KoopmanOperatorTasteGate_single_carrier_alignment_decode_encode_bhist
  constructor
  · rfl
  · exact KoopmanOperatorTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.KoopmanOperatorUp
