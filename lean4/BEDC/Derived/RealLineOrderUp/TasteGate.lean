import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLineOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLineOrderUp : Type where
  | mk (dyadicTolerance streamWindow regularReadback locatedComparison apartness realSeal
      transport replay provenance name : BHist) : RealLineOrderUp
  deriving DecidableEq

def realLineOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLineOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLineOrderEncodeBHist h

def realLineOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLineOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLineOrderDecodeBHist tail)

private theorem realLineOrder_decode_encode_bhist :
    ∀ h : BHist, realLineOrderDecodeBHist (realLineOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLineOrderFields : RealLineOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLineOrderUp.mk dyadicTolerance streamWindow regularReadback locatedComparison
      apartness realSeal transport replay provenance name =>
      [dyadicTolerance, streamWindow, regularReadback, locatedComparison, apartness, realSeal,
        transport, replay, provenance, name]

def realLineOrderToEventFlow : RealLineOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realLineOrderFields x).map realLineOrderEncodeBHist

def realLineOrderFromEventFlow : EventFlow → Option RealLineOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | dyadicTolerance :: streamWindow :: regularReadback :: locatedComparison :: apartness ::
      realSeal :: transport :: replay :: provenance :: name :: [] =>
      some
        (RealLineOrderUp.mk
          (realLineOrderDecodeBHist dyadicTolerance)
          (realLineOrderDecodeBHist streamWindow)
          (realLineOrderDecodeBHist regularReadback)
          (realLineOrderDecodeBHist locatedComparison)
          (realLineOrderDecodeBHist apartness)
          (realLineOrderDecodeBHist realSeal)
          (realLineOrderDecodeBHist transport)
          (realLineOrderDecodeBHist replay)
          (realLineOrderDecodeBHist provenance)
          (realLineOrderDecodeBHist name))
  | _ => none

private theorem realLineOrder_round_trip :
    ∀ x : RealLineOrderUp,
      realLineOrderFromEventFlow (realLineOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadicTolerance streamWindow regularReadback locatedComparison apartness realSeal
      transport replay provenance name =>
      simp only [realLineOrderToEventFlow, realLineOrderFields, realLineOrderFromEventFlow,
        List.map_cons, List.map_nil, realLineOrder_decode_encode_bhist]

private theorem realLineOrderToEventFlow_injective {x y : RealLineOrderUp} :
    realLineOrderToEventFlow x = realLineOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLineOrderFromEventFlow (realLineOrderToEventFlow x) =
        realLineOrderFromEventFlow (realLineOrderToEventFlow y) :=
    congrArg realLineOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLineOrder_round_trip x).symm
      (Eq.trans hread (realLineOrder_round_trip y)))

private theorem realLineOrder_field_faithful :
    ∀ x y : RealLineOrderUp, realLineOrderFields x = realLineOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk dyadicTolerance₁ streamWindow₁ regularReadback₁ locatedComparison₁ apartness₁ realSeal₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk dyadicTolerance₂ streamWindow₂ regularReadback₂ locatedComparison₂ apartness₂
          realSeal₂ transport₂ replay₂ provenance₂ name₂ =>
          injection hfields with hDyadic tail0
          injection tail0 with hStream tail1
          injection tail1 with hRegular tail2
          injection tail2 with hLocated tail3
          injection tail3 with hApartness tail4
          injection tail4 with hSeal tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hName _
          subst hDyadic
          subst hStream
          subst hRegular
          subst hLocated
          subst hApartness
          subst hSeal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hName
          rfl

instance realLineOrderBHistCarrier : BHistCarrier RealLineOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLineOrderToEventFlow
  fromEventFlow := realLineOrderFromEventFlow

instance realLineOrderChapterTasteGate : ChapterTasteGate RealLineOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLineOrderFromEventFlow (realLineOrderToEventFlow x) = some x
    exact realLineOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLineOrderToEventFlow_injective heq)

instance realLineOrderFieldFaithful : FieldFaithful RealLineOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realLineOrderFields
  field_faithful := realLineOrder_field_faithful

instance realLineOrderNontrivial : Nontrivial RealLineOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealLineOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealLineOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealLineOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLineOrderChapterTasteGate

theorem RealLineOrderNameCertObligations (x : RealLineOrderUp) :
    SemanticNameCert
      (fun row : BHist => row ∈ realLineOrderFields x)
      (fun row : BHist => row ∈ realLineOrderFields x)
      (fun row : BHist => row ∈ realLineOrderFields x)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases x with
  | mk dyadicTolerance streamWindow regularReadback locatedComparison apartness realSeal
      transport replay provenance name =>
      exact
        {
          core := {
            carrier_inhabited := Exists.intro dyadicTolerance (List.Mem.head _)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro _row _row' same
              exact hsame_symm same
            equiv_trans := by
              intro _row _row' _row'' sameLeft sameRight
              exact hsame_trans sameLeft sameRight
            carrier_respects_equiv := by
              intro _row _row' same source
              cases same
              exact source
          }
          pattern_sound := by
            intro _row source
            exact source
          ledger_sound := by
            intro _row source
            exact source
        }

end BEDC.Derived.RealLineOrderUp
