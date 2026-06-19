import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindEtaCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindEtaCompletionUp : Type where
  | mk (S R D Q L A H C P N : BHist) : DedekindEtaCompletionUp
  deriving DecidableEq

def dedekindEtaCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindEtaCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindEtaCompletionEncodeBHist h

def dedekindEtaCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindEtaCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindEtaCompletionDecodeBHist tail)

private theorem DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindEtaCompletionFields : DedekindEtaCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindEtaCompletionUp.mk S R D Q L A H C P N =>
      [S, R, D, Q, L, A, H, C, P, N]

def dedekindEtaCompletionToEventFlow : DedekindEtaCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dedekindEtaCompletionFields x).map dedekindEtaCompletionEncodeBHist

def dedekindEtaCompletionFromEventFlow :
    EventFlow → Option DedekindEtaCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | R :: restR =>
          match restR with
          | D :: restD =>
              match restD with
              | Q :: restQ =>
                  match restQ with
                  | L :: restL =>
                      match restL with
                      | A :: restA =>
                          match restA with
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
                                                (DedekindEtaCompletionUp.mk
                                                  (dedekindEtaCompletionDecodeBHist S)
                                                  (dedekindEtaCompletionDecodeBHist R)
                                                  (dedekindEtaCompletionDecodeBHist D)
                                                  (dedekindEtaCompletionDecodeBHist Q)
                                                  (dedekindEtaCompletionDecodeBHist L)
                                                  (dedekindEtaCompletionDecodeBHist A)
                                                  (dedekindEtaCompletionDecodeBHist H)
                                                  (dedekindEtaCompletionDecodeBHist C)
                                                  (dedekindEtaCompletionDecodeBHist P)
                                                  (dedekindEtaCompletionDecodeBHist N))
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

private theorem DedekindEtaCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DedekindEtaCompletionUp,
      dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D Q L A H C P N =>
      change
        some
          (DedekindEtaCompletionUp.mk
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist S))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist R))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist D))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist Q))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist L))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist A))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist H))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist C))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist P))
            (dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist N))) =
          some (DedekindEtaCompletionUp.mk S R D Q L A H C P N)
      rw [DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode S,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode R,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode D,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode L,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode A,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode H,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode C,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode P,
        DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem DedekindEtaCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DedekindEtaCompletionUp} :
    dedekindEtaCompletionToEventFlow x = dedekindEtaCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) =
        dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow y) :=
    congrArg dedekindEtaCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DedekindEtaCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DedekindEtaCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance dedekindEtaCompletionBHistCarrier :
    BHistCarrier DedekindEtaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindEtaCompletionToEventFlow
  fromEventFlow := dedekindEtaCompletionFromEventFlow

instance dedekindEtaCompletionChapterTasteGate :
    ChapterTasteGate DedekindEtaCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) = some x
    exact DedekindEtaCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DedekindEtaCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DedekindEtaCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindEtaCompletionChapterTasteGate

theorem DedekindEtaCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dedekindEtaCompletionDecodeBHist (dedekindEtaCompletionEncodeBHist h) = h) ∧
      (∀ x : DedekindEtaCompletionUp,
        dedekindEtaCompletionFromEventFlow (dedekindEtaCompletionToEventFlow x) =
          some x) ∧
      (∀ x y : DedekindEtaCompletionUp,
        dedekindEtaCompletionToEventFlow x = dedekindEtaCompletionToEventFlow y →
          x = y) ∧
      dedekindEtaCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DedekindEtaCompletionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact DedekindEtaCompletionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact DedekindEtaCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.DedekindEtaCompletionUp
