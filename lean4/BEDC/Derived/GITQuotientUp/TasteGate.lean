import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GITQuotientUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GITQuotientUp : Type where
  | mk (S A P G I Q O H C L N : BHist) : GITQuotientUp
  deriving DecidableEq

def gitQuotientEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gitQuotientEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gitQuotientEncodeBHist h

def gitQuotientDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gitQuotientDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gitQuotientDecodeBHist tail)

private theorem gitQuotientDecode_encode_bhist :
    ∀ h : BHist, gitQuotientDecodeBHist (gitQuotientEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gitQuotientFields : GITQuotientUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GITQuotientUp.mk S A P G I Q O H C L N => [S, A, P, G, I, Q, O, H, C, L, N]

def gitQuotientToEventFlow : GITQuotientUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gitQuotientFields x).map gitQuotientEncodeBHist

private def gitQuotientEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => gitQuotientEventAtDefault index rest

def gitQuotientFromEventFlow (ef : EventFlow) : Option GITQuotientUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GITQuotientUp.mk
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 0 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 1 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 2 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 3 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 4 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 5 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 6 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 7 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 8 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 9 ef))
      (gitQuotientDecodeBHist (gitQuotientEventAtDefault 10 ef)))

private theorem GITQuotientTasteGate_single_carrier_alignment_round_trip
    (x : GITQuotientUp) :
    gitQuotientFromEventFlow (gitQuotientToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S A P G I Q O H C L N =>
      change
        some
          (GITQuotientUp.mk
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist S))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist A))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist P))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist G))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist I))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist Q))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist O))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist H))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist C))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist L))
            (gitQuotientDecodeBHist (gitQuotientEncodeBHist N))) =
          some (GITQuotientUp.mk S A P G I Q O H C L N)
      rw [gitQuotientDecode_encode_bhist S,
        gitQuotientDecode_encode_bhist A,
        gitQuotientDecode_encode_bhist P,
        gitQuotientDecode_encode_bhist G,
        gitQuotientDecode_encode_bhist I,
        gitQuotientDecode_encode_bhist Q,
        gitQuotientDecode_encode_bhist O,
        gitQuotientDecode_encode_bhist H,
        gitQuotientDecode_encode_bhist C,
        gitQuotientDecode_encode_bhist L,
        gitQuotientDecode_encode_bhist N]

private theorem gitQuotientToEventFlow_injective {x y : GITQuotientUp} :
    gitQuotientToEventFlow x = gitQuotientToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gitQuotientFromEventFlow (gitQuotientToEventFlow x) =
        gitQuotientFromEventFlow (gitQuotientToEventFlow y) :=
    congrArg gitQuotientFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GITQuotientTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GITQuotientTasteGate_single_carrier_alignment_round_trip y)))

instance gitQuotientBHistCarrier : BHistCarrier GITQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gitQuotientToEventFlow
  fromEventFlow := gitQuotientFromEventFlow

instance gitQuotientChapterTasteGate : ChapterTasteGate GITQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gitQuotientFromEventFlow (gitQuotientToEventFlow x) = some x
    exact GITQuotientTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (gitQuotientToEventFlow_injective heq)

theorem GITQuotientTasteGate_single_carrier_alignment :
    ChapterTasteGate GITQuotientUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact gitQuotientChapterTasteGate

end BEDC.Derived.GITQuotientUp
