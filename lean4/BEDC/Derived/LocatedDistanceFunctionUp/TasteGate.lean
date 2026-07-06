import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedDistanceFunctionUp

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

inductive LocatedDistanceFunctionUp : Type where
  | mk (X A D F R O H C P N : BHist) : LocatedDistanceFunctionUp
  deriving DecidableEq

def locatedDistanceFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedDistanceFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedDistanceFunctionEncodeBHist h

def locatedDistanceFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedDistanceFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedDistanceFunctionDecodeBHist tail)

private theorem locatedDistanceFunctionDecode_encode :
    ∀ h : BHist, locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedDistanceFunctionFields : LocatedDistanceFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedDistanceFunctionUp.mk X A D F R O H C P N => [X, A, D, F, R, O, H, C, P, N]

def locatedDistanceFunctionToEventFlow : LocatedDistanceFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedDistanceFunctionFields x).map locatedDistanceFunctionEncodeBHist

private def locatedDistanceFunctionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedDistanceFunctionRawAt index rest

def locatedDistanceFunctionFromEventFlow (flow : EventFlow) :
    Option LocatedDistanceFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedDistanceFunctionUp.mk
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 0 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 1 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 2 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 3 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 4 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 5 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 6 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 7 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 8 flow))
      (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionRawAt 9 flow)))

private theorem locatedDistanceFunction_round_trip (x : LocatedDistanceFunctionUp) :
    locatedDistanceFunctionFromEventFlow (locatedDistanceFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X A D F R O H C P N =>
      change
        some
          (LocatedDistanceFunctionUp.mk
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist X))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist A))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist D))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist F))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist R))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist O))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist H))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist C))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist P))
            (locatedDistanceFunctionDecodeBHist (locatedDistanceFunctionEncodeBHist N))) =
          some (LocatedDistanceFunctionUp.mk X A D F R O H C P N)
      rw [locatedDistanceFunctionDecode_encode X, locatedDistanceFunctionDecode_encode A,
        locatedDistanceFunctionDecode_encode D, locatedDistanceFunctionDecode_encode F,
        locatedDistanceFunctionDecode_encode R, locatedDistanceFunctionDecode_encode O,
        locatedDistanceFunctionDecode_encode H, locatedDistanceFunctionDecode_encode C,
        locatedDistanceFunctionDecode_encode P, locatedDistanceFunctionDecode_encode N]

private theorem locatedDistanceFunctionToEventFlow_injective {x y : LocatedDistanceFunctionUp} :
    locatedDistanceFunctionToEventFlow x = locatedDistanceFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedDistanceFunctionFromEventFlow (locatedDistanceFunctionToEventFlow x) =
        locatedDistanceFunctionFromEventFlow (locatedDistanceFunctionToEventFlow y) :=
    congrArg locatedDistanceFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedDistanceFunction_round_trip x).symm
      (Eq.trans hread (locatedDistanceFunction_round_trip y)))

instance locatedDistanceFunctionBHistCarrier : BHistCarrier LocatedDistanceFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedDistanceFunctionToEventFlow
  fromEventFlow := locatedDistanceFunctionFromEventFlow

instance locatedDistanceFunctionChapterTasteGate : ChapterTasteGate LocatedDistanceFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedDistanceFunctionFromEventFlow (locatedDistanceFunctionToEventFlow x) = some x
    exact locatedDistanceFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedDistanceFunctionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedDistanceFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedDistanceFunctionChapterTasteGate

def LocatedDistanceFunctionCarrier [AskSetup] [PackageSetup]
    (X A D F R O H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory D ∧ UnaryHistory F ∧
    UnaryHistory R ∧ UnaryHistory O ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X A D ∧ Cont D F R ∧
        Cont R O N ∧ Cont H C P ∧ PkgSig bundle P pkg

theorem LocatedDistanceFunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X A D F R O H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedDistanceFunctionCarrier X A D F R O H C P N bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          LocatedDistanceFunctionCarrier X A D F R O H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          LocatedDistanceFunctionCarrier X A D F R O H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          LocatedDistanceFunctionCarrier X A D F R O H C P N bundle pkg ∧ hsame row N)
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

end BEDC.Derived.LocatedDistanceFunctionUp
