import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DNAFourPhaseAlphabetBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DNAFourPhaseAlphabetBridgeUp : Type where
  | mk (B Q A E H C P N : BHist) : DNAFourPhaseAlphabetBridgeUp
  deriving DecidableEq

def dnaFourPhaseAlphabetBridgeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dnaFourPhaseAlphabetBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dnaFourPhaseAlphabetBridgeEncodeBHist h

def dnaFourPhaseAlphabetBridgeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dnaFourPhaseAlphabetBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dnaFourPhaseAlphabetBridgeDecodeBHist tail)

private theorem dnaFourPhaseAlphabetBridge_decode_encode_bhist :
    forall h : BHist,
      dnaFourPhaseAlphabetBridgeDecodeBHist
          (dnaFourPhaseAlphabetBridgeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dnaFourPhaseAlphabetBridgeFields :
    DNAFourPhaseAlphabetBridgeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DNAFourPhaseAlphabetBridgeUp.mk B Q A E H C P N => [B, Q, A, E, H, C, P, N]

def dnaFourPhaseAlphabetBridgeToEventFlow :
    DNAFourPhaseAlphabetBridgeUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dnaFourPhaseAlphabetBridgeFields x).map dnaFourPhaseAlphabetBridgeEncodeBHist

private def dnaFourPhaseAlphabetBridgeEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dnaFourPhaseAlphabetBridgeEventAt index rest

def dnaFourPhaseAlphabetBridgeFromEventFlow :
    EventFlow -> Option DNAFourPhaseAlphabetBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DNAFourPhaseAlphabetBridgeUp.mk
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 0 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 1 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 2 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 3 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 4 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 5 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 6 ef))
          (dnaFourPhaseAlphabetBridgeDecodeBHist
            (dnaFourPhaseAlphabetBridgeEventAt 7 ef)))

private theorem dnaFourPhaseAlphabetBridge_round_trip :
    forall x : DNAFourPhaseAlphabetBridgeUp,
      dnaFourPhaseAlphabetBridgeFromEventFlow
          (dnaFourPhaseAlphabetBridgeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Q A E H C P N =>
      change
        some
          (DNAFourPhaseAlphabetBridgeUp.mk
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist B))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist Q))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist A))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist E))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist H))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist C))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist P))
            (dnaFourPhaseAlphabetBridgeDecodeBHist
              (dnaFourPhaseAlphabetBridgeEncodeBHist N))) =
          some (DNAFourPhaseAlphabetBridgeUp.mk B Q A E H C P N)
      rw [dnaFourPhaseAlphabetBridge_decode_encode_bhist B,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist Q,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist A,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist E,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist H,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist C,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist P,
        dnaFourPhaseAlphabetBridge_decode_encode_bhist N]

private theorem dnaFourPhaseAlphabetBridgeToEventFlow_injective
    {x y : DNAFourPhaseAlphabetBridgeUp} :
    dnaFourPhaseAlphabetBridgeToEventFlow x =
        dnaFourPhaseAlphabetBridgeToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk B1 Q1 A1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 Q2 A2 E2 H2 C2 P2 N2 =>
          change
            [dnaFourPhaseAlphabetBridgeEncodeBHist B1,
              dnaFourPhaseAlphabetBridgeEncodeBHist Q1,
              dnaFourPhaseAlphabetBridgeEncodeBHist A1,
              dnaFourPhaseAlphabetBridgeEncodeBHist E1,
              dnaFourPhaseAlphabetBridgeEncodeBHist H1,
              dnaFourPhaseAlphabetBridgeEncodeBHist C1,
              dnaFourPhaseAlphabetBridgeEncodeBHist P1,
              dnaFourPhaseAlphabetBridgeEncodeBHist N1] =
            [dnaFourPhaseAlphabetBridgeEncodeBHist B2,
              dnaFourPhaseAlphabetBridgeEncodeBHist Q2,
              dnaFourPhaseAlphabetBridgeEncodeBHist A2,
              dnaFourPhaseAlphabetBridgeEncodeBHist E2,
              dnaFourPhaseAlphabetBridgeEncodeBHist H2,
              dnaFourPhaseAlphabetBridgeEncodeBHist C2,
              dnaFourPhaseAlphabetBridgeEncodeBHist P2,
              dnaFourPhaseAlphabetBridgeEncodeBHist N2] at heq
          injection heq with hB tail0
          injection tail0 with hQ tail1
          injection tail1 with hA tail2
          injection tail2 with hE tail3
          injection tail3 with hH tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          have hB' : B1 = B2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist B1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hB)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist B2))
          have hQ' : Q1 = Q2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist Q1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hQ)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist Q2))
          have hA' : A1 = A2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist A1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hA)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist A2))
          have hE' : E1 = E2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist E1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hE)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist E2))
          have hH' : H1 = H2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist H1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hH)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist H2))
          have hC' : C1 = C2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist C1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hC)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist C2))
          have hP' : P1 = P2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist P1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hP)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist P2))
          have hN' : N1 = N2 :=
            Eq.trans (dnaFourPhaseAlphabetBridge_decode_encode_bhist N1).symm
              (Eq.trans (congrArg dnaFourPhaseAlphabetBridgeDecodeBHist hN)
                (dnaFourPhaseAlphabetBridge_decode_encode_bhist N2))
          cases hB'
          cases hQ'
          cases hA'
          cases hE'
          cases hH'
          cases hC'
          cases hP'
          cases hN'
          rfl

private theorem dnaFourPhaseAlphabetBridge_field_faithful :
    forall x y : DNAFourPhaseAlphabetBridgeUp,
      dnaFourPhaseAlphabetBridgeFields x = dnaFourPhaseAlphabetBridgeFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 Q1 A1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 Q2 A2 E2 H2 C2 P2 N2 =>
          injection hfields with hB tail0
          injection tail0 with hQ tail1
          injection tail1 with hA tail2
          injection tail2 with hE tail3
          injection tail3 with hH tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hB
          subst hQ
          subst hA
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance dnaFourPhaseAlphabetBridgeBHistCarrier :
    BHistCarrier DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dnaFourPhaseAlphabetBridgeToEventFlow
  fromEventFlow := dnaFourPhaseAlphabetBridgeFromEventFlow

instance dnaFourPhaseAlphabetBridgeChapterTasteGate :
    ChapterTasteGate DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dnaFourPhaseAlphabetBridgeFromEventFlow
          (dnaFourPhaseAlphabetBridgeToEventFlow x) =
        some x
    exact dnaFourPhaseAlphabetBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dnaFourPhaseAlphabetBridgeToEventFlow_injective heq)

instance dnaFourPhaseAlphabetBridgeFieldFaithful :
    FieldFaithful DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dnaFourPhaseAlphabetBridgeFields
  field_faithful := dnaFourPhaseAlphabetBridge_field_faithful

instance dnaFourPhaseAlphabetBridgeNontrivial :
    Nontrivial DNAFourPhaseAlphabetBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DNAFourPhaseAlphabetBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DNAFourPhaseAlphabetBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DNAFourPhaseAlphabetBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dnaFourPhaseAlphabetBridgeChapterTasteGate

theorem DNAFourPhaseAlphabetBridgeTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dnaFourPhaseAlphabetBridgeDecodeBHist
          (dnaFourPhaseAlphabetBridgeEncodeBHist h) =
        h) ∧
      (forall x : DNAFourPhaseAlphabetBridgeUp,
        dnaFourPhaseAlphabetBridgeFromEventFlow
            (dnaFourPhaseAlphabetBridgeToEventFlow x) =
          some x) ∧
      (forall x y : DNAFourPhaseAlphabetBridgeUp,
        dnaFourPhaseAlphabetBridgeToEventFlow x =
            dnaFourPhaseAlphabetBridgeToEventFlow y ->
          x = y) ∧
      dnaFourPhaseAlphabetBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact dnaFourPhaseAlphabetBridge_decode_encode_bhist
  constructor
  · exact dnaFourPhaseAlphabetBridge_round_trip
  constructor
  · intro x y heq
    exact dnaFourPhaseAlphabetBridgeToEventFlow_injective heq
  · rfl

end BEDC.Derived.DNAFourPhaseAlphabetBridgeUp
