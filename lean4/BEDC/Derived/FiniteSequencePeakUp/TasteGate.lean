import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSequencePeakUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSequencePeakUp : Type where
  | mk (L O D W R E H C G N : BHist) : FiniteSequencePeakUp
  deriving DecidableEq

def finiteSequencePeakEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSequencePeakEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSequencePeakEncodeBHist h

def finiteSequencePeakDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSequencePeakDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSequencePeakDecodeBHist tail)

private theorem finiteSequencePeakDecode_encode_bhist :
    ∀ h : BHist, finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSequencePeakFields : FiniteSequencePeakUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSequencePeakUp.mk L O D W R E H C G N => [L, O, D, W, R, E, H, C, G, N]

def finiteSequencePeakToEventFlow : FiniteSequencePeakUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteSequencePeakFields x).map finiteSequencePeakEncodeBHist

def finiteSequencePeakFromEventFlow : EventFlow → Option FiniteSequencePeakUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restO =>
      match restO with
      | [] => none
      | O :: restD =>
          match restD with
          | [] => none
          | D :: restW =>
              match restW with
              | [] => none
              | W :: restR =>
                  match restR with
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
                              | C :: restG =>
                                  match restG with
                                  | [] => none
                                  | G :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (FiniteSequencePeakUp.mk
                                                  (finiteSequencePeakDecodeBHist L)
                                                  (finiteSequencePeakDecodeBHist O)
                                                  (finiteSequencePeakDecodeBHist D)
                                                  (finiteSequencePeakDecodeBHist W)
                                                  (finiteSequencePeakDecodeBHist R)
                                                  (finiteSequencePeakDecodeBHist E)
                                                  (finiteSequencePeakDecodeBHist H)
                                                  (finiteSequencePeakDecodeBHist C)
                                                  (finiteSequencePeakDecodeBHist G)
                                                  (finiteSequencePeakDecodeBHist N))
                                          | _ :: _ => none

private theorem finiteSequencePeak_round_trip :
    ∀ x : FiniteSequencePeakUp,
      finiteSequencePeakFromEventFlow (finiteSequencePeakToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L O D W R E H C G N =>
      change
        some
          (FiniteSequencePeakUp.mk
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist L))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist O))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist D))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist W))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist R))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist E))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist H))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist C))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist G))
            (finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist N))) =
          some (FiniteSequencePeakUp.mk L O D W R E H C G N)
      rw [finiteSequencePeakDecode_encode_bhist L, finiteSequencePeakDecode_encode_bhist O,
        finiteSequencePeakDecode_encode_bhist D, finiteSequencePeakDecode_encode_bhist W,
        finiteSequencePeakDecode_encode_bhist R, finiteSequencePeakDecode_encode_bhist E,
        finiteSequencePeakDecode_encode_bhist H, finiteSequencePeakDecode_encode_bhist C,
        finiteSequencePeakDecode_encode_bhist G, finiteSequencePeakDecode_encode_bhist N]

private theorem finiteSequencePeakToEventFlow_injective {x y : FiniteSequencePeakUp} :
    finiteSequencePeakToEventFlow x = finiteSequencePeakToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSequencePeakFromEventFlow (finiteSequencePeakToEventFlow x) =
        finiteSequencePeakFromEventFlow (finiteSequencePeakToEventFlow y) :=
    congrArg finiteSequencePeakFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteSequencePeak_round_trip x).symm
      (Eq.trans hread (finiteSequencePeak_round_trip y)))

private theorem finiteSequencePeak_fields_faithful :
    ∀ x y : FiniteSequencePeakUp,
      finiteSequencePeakFields x = finiteSequencePeakFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 O1 D1 W1 R1 E1 H1 C1 G1 N1 =>
      cases y with
      | mk L2 O2 D2 W2 R2 E2 H2 C2 G2 N2 =>
          cases hfields
          rfl

instance finiteSequencePeakBHistCarrier : BHistCarrier FiniteSequencePeakUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSequencePeakToEventFlow
  fromEventFlow := finiteSequencePeakFromEventFlow

instance finiteSequencePeakChapterTasteGate : ChapterTasteGate FiniteSequencePeakUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSequencePeakFromEventFlow (finiteSequencePeakToEventFlow x) = some x
    exact finiteSequencePeak_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteSequencePeakToEventFlow_injective heq)

instance finiteSequencePeakFieldFaithful : FieldFaithful FiniteSequencePeakUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteSequencePeakFields
  field_faithful := finiteSequencePeak_fields_faithful

instance finiteSequencePeakNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteSequencePeakUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteSequencePeakUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteSequencePeakUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteSequencePeakTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteSequencePeakDecodeBHist (finiteSequencePeakEncodeBHist h) = h) ∧
      (∀ x : FiniteSequencePeakUp,
        finiteSequencePeakFromEventFlow (finiteSequencePeakToEventFlow x) = some x) ∧
        (∀ x y : FiniteSequencePeakUp,
          finiteSequencePeakToEventFlow x = finiteSequencePeakToEventFlow y → x = y) ∧
          finiteSequencePeakEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteSequencePeakDecode_encode_bhist, finiteSequencePeak_round_trip,
      (fun _ _ heq => finiteSequencePeakToEventFlow_injective heq), rfl⟩

end BEDC.Derived.FiniteSequencePeakUp.TasteGate
