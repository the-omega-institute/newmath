import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OnticResidueLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OnticResidueLedgerUp : Type where
  | mk (O M S A C R H T P N : BHist) : OnticResidueLedgerUp
  deriving DecidableEq

def onticResidueLedgerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: onticResidueLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: onticResidueLedgerEncodeBHist h

def onticResidueLedgerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (onticResidueLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (onticResidueLedgerDecodeBHist tail)

private theorem onticResidueLedgerDecode_encode_bhist :
    forall h : BHist, onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def onticResidueLedgerFields : OnticResidueLedgerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OnticResidueLedgerUp.mk O M S A C R H T P N => [O, M, S, A, C, R, H, T, P, N]

def onticResidueLedgerToEventFlow : OnticResidueLedgerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (onticResidueLedgerFields x).map onticResidueLedgerEncodeBHist

def onticResidueLedgerFromEventFlow : EventFlow -> Option OnticResidueLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | O :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | C :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (OnticResidueLedgerUp.mk
                                                  (onticResidueLedgerDecodeBHist O)
                                                  (onticResidueLedgerDecodeBHist M)
                                                  (onticResidueLedgerDecodeBHist S)
                                                  (onticResidueLedgerDecodeBHist A)
                                                  (onticResidueLedgerDecodeBHist C)
                                                  (onticResidueLedgerDecodeBHist R)
                                                  (onticResidueLedgerDecodeBHist H)
                                                  (onticResidueLedgerDecodeBHist T)
                                                  (onticResidueLedgerDecodeBHist P)
                                                  (onticResidueLedgerDecodeBHist N))
                                          | _ :: _ => none

private theorem onticResidueLedger_round_trip :
    forall x : OnticResidueLedgerUp,
      onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O M S A C R H T P N =>
      change
        some
          (OnticResidueLedgerUp.mk
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist O))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist M))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist S))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist A))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist C))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist R))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist H))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist T))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist P))
            (onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist N))) =
          some (OnticResidueLedgerUp.mk O M S A C R H T P N)
      rw [onticResidueLedgerDecode_encode_bhist O, onticResidueLedgerDecode_encode_bhist M,
        onticResidueLedgerDecode_encode_bhist S, onticResidueLedgerDecode_encode_bhist A,
        onticResidueLedgerDecode_encode_bhist C, onticResidueLedgerDecode_encode_bhist R,
        onticResidueLedgerDecode_encode_bhist H, onticResidueLedgerDecode_encode_bhist T,
        onticResidueLedgerDecode_encode_bhist P, onticResidueLedgerDecode_encode_bhist N]

private theorem onticResidueLedgerToEventFlow_injective
    {x y : OnticResidueLedgerUp} :
    onticResidueLedgerToEventFlow x = onticResidueLedgerToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) =
        onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow y) :=
    congrArg onticResidueLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (onticResidueLedger_round_trip x).symm
      (Eq.trans hread (onticResidueLedger_round_trip y)))

private theorem onticResidueLedger_fields_faithful :
    forall x y : OnticResidueLedgerUp,
      onticResidueLedgerFields x = onticResidueLedgerFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 M1 S1 A1 C1 R1 H1 T1 P1 N1 =>
      cases y with
      | mk O2 M2 S2 A2 C2 R2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance onticResidueLedgerBHistCarrier : BHistCarrier OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := onticResidueLedgerToEventFlow
  fromEventFlow := onticResidueLedgerFromEventFlow

instance onticResidueLedgerChapterTasteGate :
    ChapterTasteGate OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change onticResidueLedgerFromEventFlow (onticResidueLedgerToEventFlow x) = some x
    exact onticResidueLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (onticResidueLedgerToEventFlow_injective heq)

instance onticResidueLedgerFieldFaithful : FieldFaithful OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := onticResidueLedgerFields
  field_faithful := onticResidueLedger_fields_faithful

instance onticResidueLedgerNontrivial : Nontrivial OnticResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OnticResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  onticResidueLedgerChapterTasteGate

theorem OnticResidueLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist, onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist h) = h) ∧
      (forall x : OnticResidueLedgerUp,
        onticResidueLedgerToEventFlow x =
          List.map onticResidueLedgerEncodeBHist (onticResidueLedgerFields x)) ∧
        (forall x y : OnticResidueLedgerUp,
          onticResidueLedgerFields x = onticResidueLedgerFields y -> x = y) ∧
          (exists x y : OnticResidueLedgerUp, x ≠ y) ∧
            onticResidueLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
              onticResidueLedgerToEventFlow
                  (OnticResidueLedgerUp.mk BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty) =
                [onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist (BHist.e0 BHist.Empty),
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact onticResidueLedgerDecode_encode_bhist
  · constructor
    · intro x
      rfl
    · constructor
      · exact onticResidueLedger_fields_faithful
      · constructor
        · exact
            ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              by
                intro h
                cases h⟩
        · constructor
          · rfl
          · rfl

theorem OnticResidueLedgerObserverAccess_row_nonescape
    {O M S A C R H T P N : BHist}
    (visibleA : A ≠ BHist.Empty) :
    onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
      onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S BHist.Empty C R H T P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  injection hfields with _ htail
  injection htail with _ htail
  injection htail with _ htail
  injection htail with hA _
  exact visibleA hA

namespace TasteGate

theorem OnticResidueLedgerSignatureResidue_row_nonescape
    {O M S A C R H T P N : BHist}
    (hR : R = BHist.e0 BHist.Empty) :
    onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
      onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C BHist.Empty H T P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  injection hfields with _ tail1
  injection tail1 with _ tail2
  injection tail2 with _ tail3
  injection tail3 with _ tail4
  injection tail4 with _ tail5
  injection tail5 with hResidue _
  cases hR
  exact BHist.noConfusion hResidue

theorem OnticResidueLedgerScoped_consumer_surface
    {O M S A C R H T P N : BHist}
    (visibleO : O ≠ BHist.Empty)
    (visibleM : M ≠ BHist.Empty)
    (visibleA : A ≠ BHist.Empty)
    (hR : R = BHist.e0 BHist.Empty) :
    onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) =
        [O, M, S, A, C, R, H, T, P, N] ∧
      onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
        onticResidueLedgerFields (OnticResidueLedgerUp.mk BHist.Empty M S A C R H T P N) ∧
        onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
          onticResidueLedgerFields (OnticResidueLedgerUp.mk O BHist.Empty S A C R H T P N) ∧
          onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
            onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S BHist.Empty C R H T P N) ∧
            onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
              onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C BHist.Empty H T P N) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · rfl
  · constructor
    · intro hfields
      injection hfields with hO _
      exact visibleO hO
    · constructor
      · intro hfields
        injection hfields with _ tail1
        injection tail1 with hM _
        exact visibleM hM
      · constructor
        · exact OnticResidueLedgerObserverAccess_row_nonescape visibleA
        · exact OnticResidueLedgerSignatureResidue_row_nonescape hR

theorem OnticResidueLedgerBridgeExport_structural_rows_nonescape
    {O M S A C R H T P N : BHist}
    (visibleT : T ≠ BHist.Empty)
    (visibleP : P ≠ BHist.Empty)
    (visibleN : N ≠ BHist.Empty) :
    onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) =
        [O, M, S, A, C, R, H, T, P, N] ∧
      onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
        onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H BHist.Empty P N) ∧
        onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
          onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T BHist.Empty N) ∧
          onticResidueLedgerFields (OnticResidueLedgerUp.mk O M S A C R H T P N) ≠
            onticResidueLedgerFields
              (OnticResidueLedgerUp.mk O M S A C R H T P BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · rfl
  · constructor
    · intro hfields
      injection hfields with _ tail1
      injection tail1 with _ tail2
      injection tail2 with _ tail3
      injection tail3 with _ tail4
      injection tail4 with _ tail5
      injection tail5 with _ tail6
      injection tail6 with _ tail7
      injection tail7 with hT _
      exact visibleT hT
    · constructor
      · intro hfields
        injection hfields with _ tail1
        injection tail1 with _ tail2
        injection tail2 with _ tail3
        injection tail3 with _ tail4
        injection tail4 with _ tail5
        injection tail5 with _ tail6
        injection tail6 with _ tail7
        injection tail7 with _ tail8
        injection tail8 with hP _
        exact visibleP hP
      · intro hfields
        injection hfields with _ tail1
        injection tail1 with _ tail2
        injection tail2 with _ tail3
        injection tail3 with _ tail4
        injection tail4 with _ tail5
        injection tail5 with _ tail6
        injection tail6 with _ tail7
        injection tail7 with _ tail8
        injection tail8 with _ tail9
        injection tail9 with hN _
        exact visibleN hN

end TasteGate

namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem OnticResidueLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      onticResidueLedgerDecodeBHist (onticResidueLedgerEncodeBHist h) = h) ∧
      (forall x : OnticResidueLedgerUp,
        onticResidueLedgerToEventFlow x =
          List.map onticResidueLedgerEncodeBHist (onticResidueLedgerFields x)) ∧
        (forall x y : OnticResidueLedgerUp,
          onticResidueLedgerFields x = onticResidueLedgerFields y -> x = y) ∧
          (exists x y : OnticResidueLedgerUp, x ≠ y) ∧
            onticResidueLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
              onticResidueLedgerToEventFlow
                  (OnticResidueLedgerUp.mk BHist.Empty (BHist.e0 BHist.Empty) BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty) =
                [onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist (BHist.e0 BHist.Empty),
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty,
                  onticResidueLedgerEncodeBHist BHist.Empty] := by
  constructor
  · exact onticResidueLedgerDecode_encode_bhist
  · constructor
    · intro x
      rfl
    · constructor
      · exact onticResidueLedger_fields_faithful
      · constructor
        · exact
            ⟨OnticResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              OnticResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              by
                intro h
                cases h⟩
        · constructor
          · rfl
          · rfl

def taste_gate : ChapterTasteGate OnticResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.OnticResidueLedgerUp.taste_gate

end TasteGate

end BEDC.Derived.OnticResidueLedgerUp
