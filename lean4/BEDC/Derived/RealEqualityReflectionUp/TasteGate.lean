import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealEqualityReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealEqualityReflectionUp : Type where
  | mk (Q E R S D H C P0 N : BHist) : RealEqualityReflectionUp
  deriving DecidableEq

def realEqualityReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realEqualityReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realEqualityReflectionEncodeBHist h

def realEqualityReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realEqualityReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realEqualityReflectionDecodeBHist tail)

private theorem realEqualityReflectionDecodeEncode :
    ∀ h : BHist, realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realEqualityReflectionToEventFlow : RealEqualityReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealEqualityReflectionUp.mk Q E R S D H C P0 N =>
      [[BMark.b0],
        realEqualityReflectionEncodeBHist Q,
        [BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realEqualityReflectionEncodeBHist P0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realEqualityReflectionEncodeBHist N]

private def realEqualityReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realEqualityReflectionEventAtDefault index rest

def realEqualityReflectionFromEventFlow
    (ef : EventFlow) : Option RealEqualityReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealEqualityReflectionUp.mk
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 1 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 3 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 5 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 7 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 9 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 11 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 13 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 15 ef))
      (realEqualityReflectionDecodeBHist (realEqualityReflectionEventAtDefault 17 ef)))

private theorem realEqualityReflectionRoundTrip :
    ∀ x : RealEqualityReflectionUp,
      realEqualityReflectionFromEventFlow (realEqualityReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q E R S D H C P0 N =>
      change
        some
          (RealEqualityReflectionUp.mk
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist Q))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist E))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist R))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist S))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist D))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist H))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist C))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist P0))
            (realEqualityReflectionDecodeBHist (realEqualityReflectionEncodeBHist N))) =
          some (RealEqualityReflectionUp.mk Q E R S D H C P0 N)
      rw [realEqualityReflectionDecodeEncode Q, realEqualityReflectionDecodeEncode E,
        realEqualityReflectionDecodeEncode R, realEqualityReflectionDecodeEncode S,
        realEqualityReflectionDecodeEncode D, realEqualityReflectionDecodeEncode H,
        realEqualityReflectionDecodeEncode C, realEqualityReflectionDecodeEncode P0,
        realEqualityReflectionDecodeEncode N]

private theorem realEqualityReflectionToEventFlow_injective
    {x y : RealEqualityReflectionUp} :
    realEqualityReflectionToEventFlow x = realEqualityReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realEqualityReflectionFromEventFlow (realEqualityReflectionToEventFlow x) =
        realEqualityReflectionFromEventFlow (realEqualityReflectionToEventFlow y) :=
    congrArg realEqualityReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (realEqualityReflectionRoundTrip x).symm
      (Eq.trans hread (realEqualityReflectionRoundTrip y)))

instance realEqualityReflectionBHistCarrier : BHistCarrier RealEqualityReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realEqualityReflectionToEventFlow
  fromEventFlow := realEqualityReflectionFromEventFlow

instance realEqualityReflectionChapterTasteGate :
    ChapterTasteGate RealEqualityReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realEqualityReflectionFromEventFlow (realEqualityReflectionToEventFlow x) = some x
    exact realEqualityReflectionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realEqualityReflectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealEqualityReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realEqualityReflectionChapterTasteGate

theorem RealEqualityReflectionNameCertObligationSurface (P : RealEqualityReflectionUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ Q E R S D H C P0 N : BHist,
          P = RealEqualityReflectionUp.mk Q E R S D H C P0 N ∧ hsame row H)
      (fun row : BHist =>
        ∃ Q E R S D H C P0 N : BHist,
          P = RealEqualityReflectionUp.mk Q E R S D H C P0 N ∧ hsame row H)
      (fun row : BHist =>
        ∃ Q E R S D H C P0 N : BHist,
          P = RealEqualityReflectionUp.mk Q E R S D H C P0 N ∧ hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases P with
  | mk Q E R S D H C P0 N =>
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact ⟨H, Q, E, R, S, D, H, C, P0, N, And.intro rfl (hsame_refl H)⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' same₁ same₂
        exact hsame_trans same₁ same₂
      · intro row row' same source
        cases source with
        | intro Q0 source =>
            cases source with
            | intro E0 source =>
                cases source with
                | intro R0 source =>
                    cases source with
                    | intro S0 source =>
                        cases source with
                        | intro D0 source =>
                            cases source with
                            | intro H0 source =>
                                cases source with
                                | intro C0 source =>
                                    cases source with
                                    | intro P1 source =>
                                        cases source with
                                        | intro N0 source =>
                                            cases source.left
                                            exact
                                              ⟨Q, E, R, S, D, H, C, P0, N, rfl,
                                                hsame_trans (hsame_symm same) source.right⟩
      · intro row source
        exact source
      · intro row source
        exact source

end BEDC.Derived.RealEqualityReflectionUp
