import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RoleSeparationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoleSeparationLedgerUp : Type where
  | mk (K F A G S O H C P N : BHist) : RoleSeparationLedgerUp
  deriving DecidableEq

def roleSeparationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roleSeparationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roleSeparationLedgerEncodeBHist h

def roleSeparationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roleSeparationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roleSeparationLedgerDecodeBHist tail)

private theorem roleSeparationLedgerDecodeEncodeBHist :
    ∀ h : BHist, roleSeparationLedgerDecodeBHist (roleSeparationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def roleSeparationLedgerFields : RoleSeparationLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoleSeparationLedgerUp.mk K F A G S O H C P N => [K, F, A, G, S, O, H, C, P, N]

def roleSeparationLedgerToEventFlow : RoleSeparationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RoleSeparationLedgerUp.mk K F A G S O H C P N =>
      [[BMark.b0], roleSeparationLedgerEncodeBHist K,
        [BMark.b1], roleSeparationLedgerEncodeBHist F,
        [BMark.b0, BMark.b0], roleSeparationLedgerEncodeBHist A,
        [BMark.b0, BMark.b1], roleSeparationLedgerEncodeBHist G,
        [BMark.b1, BMark.b0], roleSeparationLedgerEncodeBHist S,
        [BMark.b1, BMark.b1], roleSeparationLedgerEncodeBHist O,
        [BMark.b0, BMark.b0, BMark.b0], roleSeparationLedgerEncodeBHist H,
        [BMark.b0, BMark.b0, BMark.b1], roleSeparationLedgerEncodeBHist C,
        [BMark.b0, BMark.b1, BMark.b0], roleSeparationLedgerEncodeBHist P,
        [BMark.b0, BMark.b1, BMark.b1], roleSeparationLedgerEncodeBHist N]

private def roleSeparationLedgerDecodePacket
    (K F A G S O H C P N : RawEvent) : RoleSeparationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RoleSeparationLedgerUp.mk
    (roleSeparationLedgerDecodeBHist K)
    (roleSeparationLedgerDecodeBHist F)
    (roleSeparationLedgerDecodeBHist A)
    (roleSeparationLedgerDecodeBHist G)
    (roleSeparationLedgerDecodeBHist S)
    (roleSeparationLedgerDecodeBHist O)
    (roleSeparationLedgerDecodeBHist H)
    (roleSeparationLedgerDecodeBHist C)
    (roleSeparationLedgerDecodeBHist P)
    (roleSeparationLedgerDecodeBHist N)

def roleSeparationLedgerFromEventFlow : EventFlow → Option RoleSeparationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagK :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | _tagF :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tagA :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tagG :: rest6 =>
                              match rest6 with
                              | [] => none
                              | G :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tagS :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | S :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tagO :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | O :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tagH :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tagC :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tagP :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tagN :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (roleSeparationLedgerDecodePacket
                                                                                          K F A G S O H C P N)
                                                                                  | _ :: _ =>
                                                                                      none

private theorem roleSeparationLedger_round_trip :
    ∀ x : RoleSeparationLedgerUp,
      roleSeparationLedgerFromEventFlow (roleSeparationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F A G S O H C P N =>
      change
        some
          (roleSeparationLedgerDecodePacket
            (roleSeparationLedgerEncodeBHist K)
            (roleSeparationLedgerEncodeBHist F)
            (roleSeparationLedgerEncodeBHist A)
            (roleSeparationLedgerEncodeBHist G)
            (roleSeparationLedgerEncodeBHist S)
            (roleSeparationLedgerEncodeBHist O)
            (roleSeparationLedgerEncodeBHist H)
            (roleSeparationLedgerEncodeBHist C)
            (roleSeparationLedgerEncodeBHist P)
            (roleSeparationLedgerEncodeBHist N)) =
          some (RoleSeparationLedgerUp.mk K F A G S O H C P N)
      unfold roleSeparationLedgerDecodePacket
      rw [roleSeparationLedgerDecodeEncodeBHist K,
        roleSeparationLedgerDecodeEncodeBHist F,
        roleSeparationLedgerDecodeEncodeBHist A,
        roleSeparationLedgerDecodeEncodeBHist G,
        roleSeparationLedgerDecodeEncodeBHist S,
        roleSeparationLedgerDecodeEncodeBHist O,
        roleSeparationLedgerDecodeEncodeBHist H,
        roleSeparationLedgerDecodeEncodeBHist C,
        roleSeparationLedgerDecodeEncodeBHist P,
        roleSeparationLedgerDecodeEncodeBHist N]

private theorem roleSeparationLedgerToEventFlow_injective {x y : RoleSeparationLedgerUp} :
    roleSeparationLedgerToEventFlow x = roleSeparationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roleSeparationLedgerFromEventFlow (roleSeparationLedgerToEventFlow x) =
        roleSeparationLedgerFromEventFlow (roleSeparationLedgerToEventFlow y) :=
    congrArg roleSeparationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (roleSeparationLedger_round_trip x).symm
      (Eq.trans hread (roleSeparationLedger_round_trip y)))

instance roleSeparationLedgerBHistCarrier : BHistCarrier RoleSeparationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roleSeparationLedgerToEventFlow
  fromEventFlow := roleSeparationLedgerFromEventFlow

instance roleSeparationLedgerChapterTasteGate : ChapterTasteGate RoleSeparationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roleSeparationLedgerFromEventFlow (roleSeparationLedgerToEventFlow x) = some x
    exact roleSeparationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (roleSeparationLedgerToEventFlow_injective heq)

instance roleSeparationLedgerFieldFaithful : FieldFaithful RoleSeparationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := roleSeparationLedgerFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk K F A G S O H C P N =>
        cases y with
        | mk K' F' A' G' S' O' H' C' P' N' =>
            cases hfields
            rfl

instance roleSeparationLedgerNontrivial : Nontrivial RoleSeparationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RoleSeparationLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RoleSeparationLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RoleSeparationLedgerTasteGate_single_carrier_alignment :
    ∀ x : RoleSeparationLedgerUp,
      ∃ K F A G S O H C P N : BHist,
        x = RoleSeparationLedgerUp.mk K F A G S O H C P N ∧
          roleSeparationLedgerFields x = [K, F, A, G, S, O, H, C, P, N] ∧
            roleSeparationLedgerFromEventFlow (roleSeparationLedgerToEventFlow x) = some x ∧
              roleSeparationLedgerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
                roleSeparationLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F A G S O H C P N =>
      exact
        ⟨K, F, A, G, S, O, H, C, P, N, rfl, rfl, roleSeparationLedger_round_trip _,
          rfl, rfl⟩

def roleSeparationLedgerTasteGate :
    (fun _ : BHist => ChapterTasteGate RoleSeparationLedgerUp) BHist.Empty :=
  -- BEDC touchpoint anchor: BHist BMark
  roleSeparationLedgerChapterTasteGate

end BEDC.Derived.RoleSeparationLedgerUp
