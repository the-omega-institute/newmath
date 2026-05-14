import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SocketUseLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SocketUseLedgerUp : Type where
  | mk : (A S Q V R H C P N : BHist) → SocketUseLedgerUp
  deriving DecidableEq

def socketUseLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: socketUseLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: socketUseLedgerEncodeBHist h

def socketUseLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (socketUseLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (socketUseLedgerDecodeBHist tail)

private theorem socketUseLedgerDecode_encode_bhist :
    ∀ h : BHist, socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def socketUseLedgerFields : SocketUseLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SocketUseLedgerUp.mk A S Q V R H C P N => [A, S, Q, V, R, H, C, P, N]

def socketUseLedgerToEventFlow : SocketUseLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (socketUseLedgerFields x).map socketUseLedgerEncodeBHist

def socketUseLedgerFromEventFlow : EventFlow → Option SocketUseLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | V :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (SocketUseLedgerUp.mk
                                              (socketUseLedgerDecodeBHist A)
                                              (socketUseLedgerDecodeBHist S)
                                              (socketUseLedgerDecodeBHist Q)
                                              (socketUseLedgerDecodeBHist V)
                                              (socketUseLedgerDecodeBHist R)
                                              (socketUseLedgerDecodeBHist H)
                                              (socketUseLedgerDecodeBHist C)
                                              (socketUseLedgerDecodeBHist P)
                                              (socketUseLedgerDecodeBHist N))
                                      | _ :: _ => none

private theorem socketUseLedger_round_trip :
    ∀ x : SocketUseLedgerUp,
      socketUseLedgerFromEventFlow (socketUseLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S Q V R H C P N =>
      change
        some
          (SocketUseLedgerUp.mk
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist A))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist S))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist Q))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist V))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist R))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist H))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist C))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist P))
            (socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist N))) =
          some (SocketUseLedgerUp.mk A S Q V R H C P N)
      rw [socketUseLedgerDecode_encode_bhist A, socketUseLedgerDecode_encode_bhist S,
        socketUseLedgerDecode_encode_bhist Q, socketUseLedgerDecode_encode_bhist V,
        socketUseLedgerDecode_encode_bhist R, socketUseLedgerDecode_encode_bhist H,
        socketUseLedgerDecode_encode_bhist C, socketUseLedgerDecode_encode_bhist P,
        socketUseLedgerDecode_encode_bhist N]

private theorem socketUseLedgerToEventFlow_injective {x y : SocketUseLedgerUp} :
    socketUseLedgerToEventFlow x = socketUseLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      socketUseLedgerFromEventFlow (socketUseLedgerToEventFlow x) =
        socketUseLedgerFromEventFlow (socketUseLedgerToEventFlow y) :=
    congrArg socketUseLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (socketUseLedger_round_trip x).symm
      (Eq.trans hread (socketUseLedger_round_trip y)))

instance socketUseLedgerBHistCarrier : BHistCarrier SocketUseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := socketUseLedgerToEventFlow
  fromEventFlow := socketUseLedgerFromEventFlow

instance socketUseLedgerChapterTasteGate : ChapterTasteGate SocketUseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change socketUseLedgerFromEventFlow (socketUseLedgerToEventFlow x) = some x
    exact socketUseLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (socketUseLedgerToEventFlow_injective heq)

instance socketUseLedgerFieldFaithful : FieldFaithful SocketUseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := socketUseLedgerFields
  field_faithful := by
    intro x y h
    cases x with
    | mk A₁ S₁ Q₁ V₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ S₂ Q₂ V₂ R₂ H₂ C₂ P₂ N₂ =>
            injection h with hA hRest₁
            injection hRest₁ with hS hRest₂
            injection hRest₂ with hQ hRest₃
            injection hRest₃ with hV hRest₄
            injection hRest₄ with hR hRest₅
            injection hRest₅ with hH hRest₆
            injection hRest₆ with hC hRest₇
            injection hRest₇ with hP hRest₈
            injection hRest₈ with hN _
            subst hA
            subst hS
            subst hQ
            subst hV
            subst hR
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance socketUseLedgerNontrivial : Nontrivial SocketUseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SocketUseLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SocketUseLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SocketUseLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, socketUseLedgerDecodeBHist (socketUseLedgerEncodeBHist h) = h) ∧
      (∀ x : SocketUseLedgerUp,
        socketUseLedgerFromEventFlow (socketUseLedgerToEventFlow x) = some x) ∧
        (∀ x y : SocketUseLedgerUp,
          socketUseLedgerToEventFlow x = socketUseLedgerToEventFlow y → x = y) ∧
          socketUseLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨socketUseLedgerDecode_encode_bhist, socketUseLedger_round_trip,
      fun _x _y => socketUseLedgerToEventFlow_injective, rfl⟩

end BEDC.Derived.SocketUseLedgerUp
