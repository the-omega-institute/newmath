import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalMeetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalMeetUp : Type where
  | mk (T M E W Q H C P N : BHist) : RegularCauchyDiagonalMeetUp
  deriving DecidableEq

def regularCauchyDiagonalMeetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalMeetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalMeetEncodeBHist h

def regularCauchyDiagonalMeetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalMeetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalMeetDecodeBHist tail)

private theorem regularCauchyDiagonalMeetDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyDiagonalMeetDecodeBHist
          (regularCauchyDiagonalMeetEncodeBHist h) =
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

def regularCauchyDiagonalMeetFields : RegularCauchyDiagonalMeetUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyDiagonalMeetUp.mk T M E W Q H C P N =>
      [T, M, E, W, Q, H, C, P, N]

def regularCauchyDiagonalMeetToEventFlow :
    RegularCauchyDiagonalMeetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyDiagonalMeetUp.mk T M E W Q H C P N =>
      [regularCauchyDiagonalMeetEncodeBHist T,
        regularCauchyDiagonalMeetEncodeBHist M,
        regularCauchyDiagonalMeetEncodeBHist E,
        regularCauchyDiagonalMeetEncodeBHist W,
        regularCauchyDiagonalMeetEncodeBHist Q,
        regularCauchyDiagonalMeetEncodeBHist H,
        regularCauchyDiagonalMeetEncodeBHist C,
        regularCauchyDiagonalMeetEncodeBHist P,
        regularCauchyDiagonalMeetEncodeBHist N]

def regularCauchyDiagonalMeetFromEventFlow :
    EventFlow → Option RegularCauchyDiagonalMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | T :: M :: E :: W :: Q :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyDiagonalMeetUp.mk
          (regularCauchyDiagonalMeetDecodeBHist T)
          (regularCauchyDiagonalMeetDecodeBHist M)
          (regularCauchyDiagonalMeetDecodeBHist E)
          (regularCauchyDiagonalMeetDecodeBHist W)
          (regularCauchyDiagonalMeetDecodeBHist Q)
          (regularCauchyDiagonalMeetDecodeBHist H)
          (regularCauchyDiagonalMeetDecodeBHist C)
          (regularCauchyDiagonalMeetDecodeBHist P)
          (regularCauchyDiagonalMeetDecodeBHist N))
  | _ => none

private theorem regularCauchyDiagonalMeet_round_trip :
    ∀ x : RegularCauchyDiagonalMeetUp,
      regularCauchyDiagonalMeetFromEventFlow
          (regularCauchyDiagonalMeetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T M E W Q H C P N =>
      simp only [regularCauchyDiagonalMeetToEventFlow,
        regularCauchyDiagonalMeetFromEventFlow,
        regularCauchyDiagonalMeetDecode_encode_bhist]

private theorem regularCauchyDiagonalMeetToEventFlow_injective
    {x y : RegularCauchyDiagonalMeetUp} :
    regularCauchyDiagonalMeetToEventFlow x =
        regularCauchyDiagonalMeetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyDiagonalMeetFromEventFlow
            (regularCauchyDiagonalMeetToEventFlow x) :=
        (regularCauchyDiagonalMeet_round_trip x).symm
      _ =
          regularCauchyDiagonalMeetFromEventFlow
            (regularCauchyDiagonalMeetToEventFlow y) :=
        congrArg regularCauchyDiagonalMeetFromEventFlow hxy
      _ = some y := regularCauchyDiagonalMeet_round_trip y
  exact Option.some.inj optionEq

private theorem regularCauchyDiagonalMeet_field_faithful :
    ∀ x y : RegularCauchyDiagonalMeetUp,
      regularCauchyDiagonalMeetFields x = regularCauchyDiagonalMeetFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T1 M1 E1 W1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 M2 E2 W2 Q2 H2 C2 P2 N2 =>
          cases h
          rfl

instance regularCauchyDiagonalMeetBHistCarrier :
    BHistCarrier RegularCauchyDiagonalMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalMeetToEventFlow
  fromEventFlow := regularCauchyDiagonalMeetFromEventFlow

instance regularCauchyDiagonalMeetChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalMeetFromEventFlow
          (regularCauchyDiagonalMeetToEventFlow x) =
        some x
    exact regularCauchyDiagonalMeet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalMeetToEventFlow_injective heq)

instance regularCauchyDiagonalMeetFieldFaithful :
    FieldFaithful RegularCauchyDiagonalMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyDiagonalMeetFields
  field_faithful := regularCauchyDiagonalMeet_field_faithful

instance regularCauchyDiagonalMeetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyDiagonalMeetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyDiagonalMeetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyDiagonalMeetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyDiagonalMeetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDiagonalMeetChapterTasteGate

theorem RegularCauchyDiagonalMeetNameCertObligations
    (x : RegularCauchyDiagonalMeetUp) :
    ∃ T M E W Q H C P N : BHist,
      x = RegularCauchyDiagonalMeetUp.mk T M E W Q H C P N ∧
        SemanticNameCert
          (fun row : BHist => hsame row N)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row E ∨ hsame row W ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist => hsame row N)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk T M E W Q H C P N =>
      exact
        ⟨T, M, E, W, Q, H, C, P, N, rfl,
          {
            core := {
              carrier_inhabited := Exists.intro N (hsame_refl N)
              equiv_refl := by
                intro row _source
                exact hsame_refl row
              equiv_symm := by
                intro _row _other sameRows
                exact hsame_symm sameRows
              equiv_trans := by
                intro _row _middle _other sameLeft sameRight
                exact hsame_trans sameLeft sameRight
              carrier_respects_equiv := by
                intro _row _other sameRows sourceRow
                exact hsame_trans (hsame_symm sameRows) sourceRow
            }
            pattern_sound := by
              intro _row sourceRow
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr sourceRow)))))))
            ledger_sound := by
              intro _row sourceRow
              exact sourceRow
          }⟩

end BEDC.Derived.RegularCauchyDiagonalMeetUp
