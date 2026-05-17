import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TraditionRegistryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TraditionRegistryUp : Type where
  | mk :
      (tradition site preserved rejected transport replay provenance localName : BHist) →
      TraditionRegistryUp
  deriving DecidableEq

def traditionRegistryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: traditionRegistryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: traditionRegistryEncodeBHist h

def traditionRegistryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (traditionRegistryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (traditionRegistryDecodeBHist tail)

private theorem traditionRegistryDecodeEncodeBHist :
    ∀ h : BHist, traditionRegistryDecodeBHist (traditionRegistryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def traditionRegistryFields : TraditionRegistryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionRegistryUp.mk tradition site preserved rejected transport replay provenance
      localName =>
      [tradition, site, preserved, rejected, transport, replay, provenance, localName]

def traditionRegistryToEventFlow : TraditionRegistryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (traditionRegistryFields x).map traditionRegistryEncodeBHist

def traditionRegistryFromEventFlow : EventFlow → Option TraditionRegistryUp
  -- BEDC touchpoint anchor: BHist BMark
  | tradition :: site :: preserved :: rejected :: transport :: replay :: provenance ::
      localName :: [] =>
      some
        (TraditionRegistryUp.mk
          (traditionRegistryDecodeBHist tradition)
          (traditionRegistryDecodeBHist site)
          (traditionRegistryDecodeBHist preserved)
          (traditionRegistryDecodeBHist rejected)
          (traditionRegistryDecodeBHist transport)
          (traditionRegistryDecodeBHist replay)
          (traditionRegistryDecodeBHist provenance)
          (traditionRegistryDecodeBHist localName))
  | _ => none

private theorem traditionRegistry_round_trip :
    ∀ x : TraditionRegistryUp,
      traditionRegistryFromEventFlow (traditionRegistryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tradition site preserved rejected transport replay provenance localName =>
      change
        some
          (TraditionRegistryUp.mk
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist tradition))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist site))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist preserved))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist rejected))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist transport))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist replay))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist provenance))
            (traditionRegistryDecodeBHist (traditionRegistryEncodeBHist localName))) =
          some
            (TraditionRegistryUp.mk tradition site preserved rejected transport replay
              provenance localName)
      rw [traditionRegistryDecodeEncodeBHist tradition,
        traditionRegistryDecodeEncodeBHist site,
        traditionRegistryDecodeEncodeBHist preserved,
        traditionRegistryDecodeEncodeBHist rejected,
        traditionRegistryDecodeEncodeBHist transport,
        traditionRegistryDecodeEncodeBHist replay,
        traditionRegistryDecodeEncodeBHist provenance,
        traditionRegistryDecodeEncodeBHist localName]

private theorem traditionRegistryToEventFlow_injective {x y : TraditionRegistryUp} :
    traditionRegistryToEventFlow x = traditionRegistryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      traditionRegistryFromEventFlow (traditionRegistryToEventFlow x) =
        traditionRegistryFromEventFlow (traditionRegistryToEventFlow y) :=
    congrArg traditionRegistryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (traditionRegistry_round_trip x).symm
      (Eq.trans hread (traditionRegistry_round_trip y)))

private theorem traditionRegistry_field_faithful :
    ∀ x y : TraditionRegistryUp, traditionRegistryFields x = traditionRegistryFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tradition₁ site₁ preserved₁ rejected₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk tradition₂ site₂ preserved₂ rejected₂ transport₂ replay₂ provenance₂ localName₂ =>
          injection hfields with htradition tail0
          injection tail0 with hsite tail1
          injection tail1 with hpreserved tail2
          injection tail2 with hrejected tail3
          injection tail3 with htransport tail4
          injection tail4 with hreplay tail5
          injection tail5 with hprovenance tail6
          injection tail6 with hlocalName _
          subst htradition
          subst hsite
          subst hpreserved
          subst hrejected
          subst htransport
          subst hreplay
          subst hprovenance
          subst hlocalName
          rfl

instance traditionRegistryBHistCarrier : BHistCarrier TraditionRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := traditionRegistryToEventFlow
  fromEventFlow := traditionRegistryFromEventFlow

instance traditionRegistryChapterTasteGate : ChapterTasteGate TraditionRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change traditionRegistryFromEventFlow (traditionRegistryToEventFlow x) = some x
    exact traditionRegistry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (traditionRegistryToEventFlow_injective heq)

instance traditionRegistryFieldFaithful : FieldFaithful TraditionRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := traditionRegistryFields
  field_faithful := traditionRegistry_field_faithful

instance traditionRegistryNontrivial : Nontrivial TraditionRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TraditionRegistryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TraditionRegistryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TraditionRegistryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  traditionRegistryChapterTasteGate

end BEDC.Derived.TraditionRegistryUp
