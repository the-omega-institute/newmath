import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyInterleavingModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyInterleavingModulusUp : Type where
  | mk (A B SA SB Q M R E H C P N : BHist) : BishopCauchyInterleavingModulusUp
  deriving DecidableEq

def bishopCauchyInterleavingModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyInterleavingModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyInterleavingModulusEncodeBHist h

def bishopCauchyInterleavingModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyInterleavingModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyInterleavingModulusDecodeBHist tail)

private theorem bishopCauchyInterleavingModulusDecode_encode :
    ∀ h : BHist,
      bishopCauchyInterleavingModulusDecodeBHist
          (bishopCauchyInterleavingModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyInterleavingModulusFields :
    BishopCauchyInterleavingModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyInterleavingModulusUp.mk A B SA SB Q M R E H C P N =>
      [A, B, SA, SB, Q, M, R, E, H, C, P, N]

def bishopCauchyInterleavingModulusToEventFlow :
    BishopCauchyInterleavingModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyInterleavingModulusFields x).map
    bishopCauchyInterleavingModulusEncodeBHist

private def bishopCauchyInterleavingModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyInterleavingModulusRawAt index rest

def bishopCauchyInterleavingModulusFromEventFlow
    (flow : EventFlow) : Option BishopCauchyInterleavingModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyInterleavingModulusUp.mk
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 0 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 1 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 2 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 3 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 4 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 5 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 6 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 7 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 8 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 9 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 10 flow))
      (bishopCauchyInterleavingModulusDecodeBHist
        (bishopCauchyInterleavingModulusRawAt 11 flow)))

private theorem bishopCauchyInterleavingModulus_round_trip
    (x : BishopCauchyInterleavingModulusUp) :
    bishopCauchyInterleavingModulusFromEventFlow
        (bishopCauchyInterleavingModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B SA SB Q M R E H C P N =>
      change
        some
          (BishopCauchyInterleavingModulusUp.mk
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist A))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist B))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist SA))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist SB))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist Q))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist M))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist R))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist E))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist H))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist C))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist P))
            (bishopCauchyInterleavingModulusDecodeBHist
              (bishopCauchyInterleavingModulusEncodeBHist N))) =
          some (BishopCauchyInterleavingModulusUp.mk A B SA SB Q M R E H C P N)
      rw [bishopCauchyInterleavingModulusDecode_encode A,
        bishopCauchyInterleavingModulusDecode_encode B,
        bishopCauchyInterleavingModulusDecode_encode SA,
        bishopCauchyInterleavingModulusDecode_encode SB,
        bishopCauchyInterleavingModulusDecode_encode Q,
        bishopCauchyInterleavingModulusDecode_encode M,
        bishopCauchyInterleavingModulusDecode_encode R,
        bishopCauchyInterleavingModulusDecode_encode E,
        bishopCauchyInterleavingModulusDecode_encode H,
        bishopCauchyInterleavingModulusDecode_encode C,
        bishopCauchyInterleavingModulusDecode_encode P,
        bishopCauchyInterleavingModulusDecode_encode N]

private theorem bishopCauchyInterleavingModulusToEventFlow_injective
    {x y : BishopCauchyInterleavingModulusUp} :
    bishopCauchyInterleavingModulusToEventFlow x =
      bishopCauchyInterleavingModulusToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyInterleavingModulusFromEventFlow
          (bishopCauchyInterleavingModulusToEventFlow x) =
        bishopCauchyInterleavingModulusFromEventFlow
          (bishopCauchyInterleavingModulusToEventFlow y) :=
    congrArg bishopCauchyInterleavingModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCauchyInterleavingModulus_round_trip x).symm
      (Eq.trans hread (bishopCauchyInterleavingModulus_round_trip y)))

instance bishopCauchyInterleavingModulusBHistCarrier :
    BHistCarrier BishopCauchyInterleavingModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyInterleavingModulusToEventFlow
  fromEventFlow := bishopCauchyInterleavingModulusFromEventFlow

instance bishopCauchyInterleavingModulusChapterTasteGate :
    ChapterTasteGate BishopCauchyInterleavingModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyInterleavingModulusFromEventFlow
          (bishopCauchyInterleavingModulusToEventFlow x) =
        some x
    exact bishopCauchyInterleavingModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyInterleavingModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCauchyInterleavingModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyInterleavingModulusChapterTasteGate

def BishopCauchyInterleavingModulusCarrier [AskSetup] [PackageSetup]
    (A B SA SB Q M R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory SA ∧ UnaryHistory SB ∧
    UnaryHistory Q ∧ UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont A SA Q ∧ Cont B SB Q ∧ Cont Q M R ∧ Cont R E N ∧ PkgSig bundle P pkg

theorem BishopCauchyInterleavingModulusCarrier_namecert_obligations [AskSetup]
    [PackageSetup] {A B SA SB Q M R E H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCauchyInterleavingModulusCarrier A B SA SB Q M R E H C P N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BishopCauchyInterleavingModulusCarrier A B SA SB Q M R E H C P N bundle pkg ∧
            hsame row N)
        (fun row : BHist =>
          BishopCauchyInterleavingModulusCarrier A B SA SB Q M R E H C P N bundle pkg ∧
            hsame row N)
        (fun row : BHist =>
          BishopCauchyInterleavingModulusCarrier A B SA SB Q M R E H C P N bundle pkg ∧
            hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert NameCert BMark
  intro carrier
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact ⟨N, carrier, hsame_refl N⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows source
    exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
  · intro _row source
    exact source
  · intro _row source
    exact source

end BEDC.Derived.BishopCauchyInterleavingModulusUp
