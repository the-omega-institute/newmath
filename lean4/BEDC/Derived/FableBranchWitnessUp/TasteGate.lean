import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FableBranchWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FableBranchWitnessUp : Type where
  | mk :
      (h m r e a transport route provenance name : BHist) →
        FableBranchWitnessUp
  deriving DecidableEq

def fableBranchWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fableBranchWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fableBranchWitnessEncodeBHist h

def fableBranchWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fableBranchWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fableBranchWitnessDecodeBHist tail)

private theorem fableBranchWitnessDecode_encode_bhist :
    ∀ h : BHist,
      fableBranchWitnessDecodeBHist
        (fableBranchWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fableBranchWitnessToEventFlow :
    FableBranchWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FableBranchWitnessUp.mk h m r e a transport route provenance name =>
      [[BMark.b0],
        fableBranchWitnessEncodeBHist h,
        [BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist m,
        [BMark.b1, BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist a,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fableBranchWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        fableBranchWitnessEncodeBHist name]

def fableBranchWitnessFromEventFlow :
    EventFlow → Option FableBranchWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | h :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | m :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | r :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | e :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | a :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (FableBranchWitnessUp.mk
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    h)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    m)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    r)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    e)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    a)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    transport)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    route)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    provenance)
                                                                                  (fableBranchWitnessDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem fableBranchWitness_round_trip :
    ∀ x : FableBranchWitnessUp,
      fableBranchWitnessFromEventFlow
        (fableBranchWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk h m r e a transport route provenance name =>
      change
        some
          (FableBranchWitnessUp.mk
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist h))
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist m))
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist r))
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist e))
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist a))
            (fableBranchWitnessDecodeBHist
              (fableBranchWitnessEncodeBHist transport))
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist route))
            (fableBranchWitnessDecodeBHist
              (fableBranchWitnessEncodeBHist provenance))
            (fableBranchWitnessDecodeBHist (fableBranchWitnessEncodeBHist name))) =
          some (FableBranchWitnessUp.mk h m r e a transport route provenance name)
      rw [fableBranchWitnessDecode_encode_bhist h,
        fableBranchWitnessDecode_encode_bhist m,
        fableBranchWitnessDecode_encode_bhist r,
        fableBranchWitnessDecode_encode_bhist e,
        fableBranchWitnessDecode_encode_bhist a,
        fableBranchWitnessDecode_encode_bhist transport,
        fableBranchWitnessDecode_encode_bhist route,
        fableBranchWitnessDecode_encode_bhist provenance,
        fableBranchWitnessDecode_encode_bhist name]

private theorem fableBranchWitnessToEventFlow_injective
    {x y : FableBranchWitnessUp} :
    fableBranchWitnessToEventFlow x =
      fableBranchWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fableBranchWitnessFromEventFlow (fableBranchWitnessToEventFlow x) =
        fableBranchWitnessFromEventFlow (fableBranchWitnessToEventFlow y) :=
    congrArg fableBranchWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fableBranchWitness_round_trip x).symm
      (Eq.trans hread (fableBranchWitness_round_trip y)))

def fableBranchWitnessFields : FableBranchWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FableBranchWitnessUp.mk h m r e a transport route provenance name =>
      [h, m, r, e, a, transport, route, provenance, name]

private theorem fableBranchWitness_field_faithful :
    ∀ x y : FableBranchWitnessUp, fableBranchWitnessFields x = fableBranchWitnessFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk h1 m1 r1 e1 a1 transport1 route1 provenance1 name1 =>
      cases y with
      | mk h2 m2 r2 e2 a2 transport2 route2 provenance2 name2 =>
          cases hfields
          rfl

instance fableBranchWitnessBHistCarrier :
    BHistCarrier FableBranchWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fableBranchWitnessToEventFlow
  fromEventFlow := fableBranchWitnessFromEventFlow

instance fableBranchWitnessChapterTasteGate :
    ChapterTasteGate FableBranchWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      fableBranchWitnessFromEventFlow
        (fableBranchWitnessToEventFlow x) = some x
    exact fableBranchWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fableBranchWitnessToEventFlow_injective heq)

instance fableBranchWitnessFieldFaithful : FieldFaithful FableBranchWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fableBranchWitnessFields
  field_faithful := fableBranchWitness_field_faithful

instance fableBranchWitnessNontrivial : Nontrivial FableBranchWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FableBranchWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FableBranchWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FableBranchWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, fableBranchWitnessDecodeBHist
      (fableBranchWitnessEncodeBHist h) = h) ∧
      (∀ x : FableBranchWitnessUp,
        fableBranchWitnessFromEventFlow
          (fableBranchWitnessToEventFlow x) = some x) ∧
        (∀ x y : FableBranchWitnessUp,
          fableBranchWitnessToEventFlow x =
            fableBranchWitnessToEventFlow y → x = y) ∧
          fableBranchWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fableBranchWitnessDecode_encode_bhist
  · constructor
    · exact fableBranchWitness_round_trip
    · constructor
      · intro x y heq
        exact fableBranchWitnessToEventFlow_injective heq
      · rfl

def FableBranchWitnessPacket (h m r e a transport route provenance name branchRead : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  UnaryHistory h ∧ UnaryHistory m ∧ UnaryHistory r ∧ UnaryHistory e ∧ UnaryHistory a ∧
    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ Cont h m r ∧ Cont r e a ∧ Cont a transport route ∧
        Cont route provenance branchRead

theorem FableBranchWitnessNameCertObligations
    {h m r e a transport route provenance name branchRead : BHist} :
    FableBranchWitnessPacket h m r e a transport route provenance name branchRead →
      SemanticNameCert
        (fun row : BHist =>
          FableBranchWitnessPacket h m r e a transport route provenance name branchRead ∧
            hsame row name)
        (fun row : BHist =>
          FableBranchWitnessPacket h m r e a transport route provenance name branchRead ∧
            hsame row name)
        (fun row : BHist =>
          FableBranchWitnessPacket h m r e a transport route provenance name branchRead ∧
            hsame row name)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro name (And.intro packet (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row col same
        exact hsame_symm same
      equiv_trans := by
        intro row col out sameRow sameCol
        exact hsame_trans sameRow sameCol
      carrier_respects_equiv := by
        intro row col same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.FableBranchWitnessUp
