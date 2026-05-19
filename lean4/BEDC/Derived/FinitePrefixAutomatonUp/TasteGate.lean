import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixAutomatonUp : Type where
  | mk (Q q0 A T W R E H C P N : BHist) : FinitePrefixAutomatonUp
  deriving DecidableEq

def finitePrefixAutomatonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixAutomatonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixAutomatonEncodeBHist h

def finitePrefixAutomatonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixAutomatonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixAutomatonDecodeBHist tail)

private theorem finitePrefixAutomatonDecode_encode_bhist :
    ∀ h : BHist, finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finitePrefixAutomatonToEventFlow : FinitePrefixAutomatonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N =>
      [[BMark.b0],
        finitePrefixAutomatonEncodeBHist Q,
        [BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist q0,
        [BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finitePrefixAutomatonEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finitePrefixAutomatonEncodeBHist N]

def finitePrefixAutomatonFromEventFlow : EventFlow → Option FinitePrefixAutomatonUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tagQ :: Q :: _tagQ0 :: q0 :: _tagA :: A :: _tagT :: T :: _tagW :: W ::
      _tagR :: R :: _tagE :: E :: _tagH :: H :: _tagC :: C :: _tagP :: P ::
      _tagN :: N :: [] =>
      some
        (FinitePrefixAutomatonUp.mk
          (finitePrefixAutomatonDecodeBHist Q)
          (finitePrefixAutomatonDecodeBHist q0)
          (finitePrefixAutomatonDecodeBHist A)
          (finitePrefixAutomatonDecodeBHist T)
          (finitePrefixAutomatonDecodeBHist W)
          (finitePrefixAutomatonDecodeBHist R)
          (finitePrefixAutomatonDecodeBHist E)
          (finitePrefixAutomatonDecodeBHist H)
          (finitePrefixAutomatonDecodeBHist C)
          (finitePrefixAutomatonDecodeBHist P)
          (finitePrefixAutomatonDecodeBHist N))
  | _ => none

private theorem finitePrefixAutomaton_round_trip :
    ∀ x : FinitePrefixAutomatonUp,
      finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q q0 A T W R E H C P N =>
      change
        some
          (FinitePrefixAutomatonUp.mk
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist Q))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist q0))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist A))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist T))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist W))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist R))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist E))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist H))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist C))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist P))
            (finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist N))) =
          some (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)
      rw [finitePrefixAutomatonDecode_encode_bhist Q, finitePrefixAutomatonDecode_encode_bhist q0,
        finitePrefixAutomatonDecode_encode_bhist A, finitePrefixAutomatonDecode_encode_bhist T,
        finitePrefixAutomatonDecode_encode_bhist W, finitePrefixAutomatonDecode_encode_bhist R,
        finitePrefixAutomatonDecode_encode_bhist E, finitePrefixAutomatonDecode_encode_bhist H,
        finitePrefixAutomatonDecode_encode_bhist C, finitePrefixAutomatonDecode_encode_bhist P,
        finitePrefixAutomatonDecode_encode_bhist N]

private theorem finitePrefixAutomatonToEventFlow_injective
    {x y : FinitePrefixAutomatonUp} :
    finitePrefixAutomatonToEventFlow x = finitePrefixAutomatonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow x) =
        finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow y) :=
    congrArg finitePrefixAutomatonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finitePrefixAutomaton_round_trip x).symm
      (Eq.trans hread (finitePrefixAutomaton_round_trip y)))

private def finitePrefixAutomatonFields : FinitePrefixAutomatonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N => [Q, q0, A, T, W, R, E, H, C, P, N]

private theorem finitePrefixAutomaton_fields_faithful :
    ∀ x y : FinitePrefixAutomatonUp,
      finitePrefixAutomatonFields x = finitePrefixAutomatonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 q01 A1 T1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 q02 A2 T2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finitePrefixAutomatonBHistCarrier : BHistCarrier FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixAutomatonToEventFlow
  fromEventFlow := finitePrefixAutomatonFromEventFlow

instance finitePrefixAutomatonChapterTasteGate : ChapterTasteGate FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finitePrefixAutomatonFromEventFlow (finitePrefixAutomatonToEventFlow x) = some x
    exact finitePrefixAutomaton_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finitePrefixAutomatonToEventFlow_injective heq)

instance finitePrefixAutomatonFieldFaithful : FieldFaithful FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finitePrefixAutomatonFields
  field_faithful := finitePrefixAutomaton_fields_faithful

instance finitePrefixAutomatonNontrivial : Nontrivial FinitePrefixAutomatonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePrefixAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FinitePrefixAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FinitePrefixAutomatonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finitePrefixAutomatonDecodeBHist (finitePrefixAutomatonEncodeBHist h) = h) ∧
      (∀ x y : FinitePrefixAutomatonUp,
        finitePrefixAutomatonFields x = finitePrefixAutomatonFields y → x = y) ∧
      finitePrefixAutomatonEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      finitePrefixAutomatonEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ x y : FinitePrefixAutomatonUp,
        x = y → finitePrefixAutomatonToEventFlow x = finitePrefixAutomatonToEventFlow y) ∧
      (∃ x y : FinitePrefixAutomatonUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact finitePrefixAutomatonDecode_encode_bhist
  constructor
  · exact finitePrefixAutomaton_fields_faithful
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro x y hxy
    cases hxy
    rfl
  · exact
      ⟨FinitePrefixAutomatonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        FinitePrefixAutomatonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩

end BEDC.Derived.FinitePrefixAutomatonUp
