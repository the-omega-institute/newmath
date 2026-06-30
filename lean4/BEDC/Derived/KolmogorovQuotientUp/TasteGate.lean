import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KolmogorovQuotientUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KolmogorovQuotientUp : Type where
  | mk (T O E R S H C P N : BHist) : KolmogorovQuotientUp
  deriving DecidableEq

def kolmogorovQuotientEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kolmogorovQuotientEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kolmogorovQuotientEncodeBHist h

def kolmogorovQuotientDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kolmogorovQuotientDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kolmogorovQuotientDecodeBHist tail)

private theorem kolmogorovQuotientDecodeEncode :
    ∀ h : BHist, kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kolmogorovQuotientToEventFlow : KolmogorovQuotientUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KolmogorovQuotientUp.mk T O E R S H C P N =>
      [[BMark.b0],
        kolmogorovQuotientEncodeBHist T,
        [BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kolmogorovQuotientEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kolmogorovQuotientEncodeBHist N]

private def kolmogorovQuotientEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kolmogorovQuotientEventAtDefault index rest

def kolmogorovQuotientFromEventFlow (ef : EventFlow) : Option KolmogorovQuotientUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KolmogorovQuotientUp.mk
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 1 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 3 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 5 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 7 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 9 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 11 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 13 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 15 ef))
      (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEventAtDefault 17 ef)))

private theorem kolmogorovQuotientRoundTrip :
    ∀ x : KolmogorovQuotientUp,
      kolmogorovQuotientFromEventFlow (kolmogorovQuotientToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T O E R S H C P N =>
      change
        some
          (KolmogorovQuotientUp.mk
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist T))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist O))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist E))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist R))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist S))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist H))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist C))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist P))
            (kolmogorovQuotientDecodeBHist (kolmogorovQuotientEncodeBHist N))) =
          some (KolmogorovQuotientUp.mk T O E R S H C P N)
      rw [kolmogorovQuotientDecodeEncode T, kolmogorovQuotientDecodeEncode O,
        kolmogorovQuotientDecodeEncode E, kolmogorovQuotientDecodeEncode R,
        kolmogorovQuotientDecodeEncode S, kolmogorovQuotientDecodeEncode H,
        kolmogorovQuotientDecodeEncode C, kolmogorovQuotientDecodeEncode P,
        kolmogorovQuotientDecodeEncode N]

private theorem kolmogorovQuotientToEventFlow_injective {x y : KolmogorovQuotientUp} :
    kolmogorovQuotientToEventFlow x = kolmogorovQuotientToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kolmogorovQuotientFromEventFlow (kolmogorovQuotientToEventFlow x) =
        kolmogorovQuotientFromEventFlow (kolmogorovQuotientToEventFlow y) :=
    congrArg kolmogorovQuotientFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (kolmogorovQuotientRoundTrip x).symm
      (Eq.trans hread (kolmogorovQuotientRoundTrip y)))

instance kolmogorovQuotientBHistCarrier : BHistCarrier KolmogorovQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kolmogorovQuotientToEventFlow
  fromEventFlow := kolmogorovQuotientFromEventFlow

instance kolmogorovQuotientChapterTasteGate : ChapterTasteGate KolmogorovQuotientUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kolmogorovQuotientFromEventFlow (kolmogorovQuotientToEventFlow x) = some x
    exact kolmogorovQuotientRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kolmogorovQuotientToEventFlow_injective heq)

def taste_gate : ChapterTasteGate KolmogorovQuotientUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kolmogorovQuotientChapterTasteGate

theorem KolmogorovQuotientNameCertObligations (K : KolmogorovQuotientUp) :
    SemanticNameCert
      (fun row : BHist =>
        ∃ T O E R S H C P N : BHist,
          K = KolmogorovQuotientUp.mk T O E R S H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ T O E R S H C P N : BHist,
          K = KolmogorovQuotientUp.mk T O E R S H C P N ∧ hsame row H)
      (fun row : BHist =>
        ∃ T O E R S H C P N : BHist,
          K = KolmogorovQuotientUp.mk T O E R S H C P N ∧ hsame row H)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases K with
  | mk T O E R S H C P N =>
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact ⟨H, T, O, E, R, S, H, C, P, N, And.intro rfl (hsame_refl H)⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' same₁ same₂
        exact hsame_trans same₁ same₂
      · intro row row' same source
        cases source with
        | intro T0 source =>
            cases source with
            | intro O0 source =>
                cases source with
                | intro E0 source =>
                    cases source with
                    | intro R0 source =>
                        cases source with
                        | intro S0 source =>
                            cases source with
                            | intro H0 source =>
                                cases source with
                                | intro C0 source =>
                                    cases source with
                                    | intro P0 source =>
                                        cases source with
                                        | intro N0 source =>
                                            cases source.left
                                            exact
                                              ⟨T, O, E, R, S, H, C, P, N, rfl,
                                                hsame_trans (hsame_symm same) source.right⟩
      · intro row source
        exact source
      · intro row source
        exact source

end BEDC.Derived.KolmogorovQuotientUp
