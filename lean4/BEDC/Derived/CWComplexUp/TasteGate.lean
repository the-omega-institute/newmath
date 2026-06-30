import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CWComplexUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CWComplexUp : Type where
  | mk (T K E A B C H R P N : BHist) : CWComplexUp
  deriving DecidableEq

def cwComplexEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cwComplexEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cwComplexEncodeBHist h

def cwComplexDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cwComplexDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cwComplexDecodeBHist tail)

private theorem CWComplexCarrier_namecert_obligations_decode_encode :
    forall h : BHist, cwComplexDecodeBHist (cwComplexEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cwComplexFields : CWComplexUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CWComplexUp.mk T K E A B C H R P N => [T, K, E, A, B, C, H, R, P, N]

def cwComplexToEventFlow : CWComplexUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cwComplexFields x).map cwComplexEncodeBHist

private def CWComplexCarrier_namecert_obligations_eventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => CWComplexCarrier_namecert_obligations_eventAt index rest

def cwComplexFromEventFlow (ef : EventFlow) : Option CWComplexUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CWComplexUp.mk
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 0 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 1 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 2 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 3 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 4 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 5 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 6 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 7 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 8 ef))
      (cwComplexDecodeBHist (CWComplexCarrier_namecert_obligations_eventAt 9 ef)))

private theorem CWComplexCarrier_namecert_obligations_round_trip (x : CWComplexUp) :
    cwComplexFromEventFlow (cwComplexToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T K E A B C H R P N =>
      change
        some
          (CWComplexUp.mk
            (cwComplexDecodeBHist (cwComplexEncodeBHist T))
            (cwComplexDecodeBHist (cwComplexEncodeBHist K))
            (cwComplexDecodeBHist (cwComplexEncodeBHist E))
            (cwComplexDecodeBHist (cwComplexEncodeBHist A))
            (cwComplexDecodeBHist (cwComplexEncodeBHist B))
            (cwComplexDecodeBHist (cwComplexEncodeBHist C))
            (cwComplexDecodeBHist (cwComplexEncodeBHist H))
            (cwComplexDecodeBHist (cwComplexEncodeBHist R))
            (cwComplexDecodeBHist (cwComplexEncodeBHist P))
            (cwComplexDecodeBHist (cwComplexEncodeBHist N))) =
          some (CWComplexUp.mk T K E A B C H R P N)
      rw [CWComplexCarrier_namecert_obligations_decode_encode T,
        CWComplexCarrier_namecert_obligations_decode_encode K,
        CWComplexCarrier_namecert_obligations_decode_encode E,
        CWComplexCarrier_namecert_obligations_decode_encode A,
        CWComplexCarrier_namecert_obligations_decode_encode B,
        CWComplexCarrier_namecert_obligations_decode_encode C,
        CWComplexCarrier_namecert_obligations_decode_encode H,
        CWComplexCarrier_namecert_obligations_decode_encode R,
        CWComplexCarrier_namecert_obligations_decode_encode P,
        CWComplexCarrier_namecert_obligations_decode_encode N]

private theorem CWComplexCarrier_namecert_obligations_toEventFlow_injective
    {x y : CWComplexUp} :
    cwComplexToEventFlow x = cwComplexToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cwComplexFromEventFlow (cwComplexToEventFlow x) =
        cwComplexFromEventFlow (cwComplexToEventFlow y) :=
    congrArg cwComplexFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CWComplexCarrier_namecert_obligations_round_trip x).symm
      (Eq.trans hread (CWComplexCarrier_namecert_obligations_round_trip y)))

instance cwComplexBHistCarrier : BHistCarrier CWComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cwComplexToEventFlow
  fromEventFlow := cwComplexFromEventFlow

instance cwComplexChapterTasteGate : ChapterTasteGate CWComplexUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cwComplexFromEventFlow (cwComplexToEventFlow x) = some x
    exact CWComplexCarrier_namecert_obligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CWComplexCarrier_namecert_obligations_toEventFlow_injective heq)

def CWComplexCarrier [AskSetup] [PackageSetup]
    (T K E A B C H R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory A ∧
    UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory H ∧ UnaryHistory R ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont T K E ∧ Cont E A B ∧
        PkgSig bundle P pkg

theorem CWComplexCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T K E A B C H R P N boundaryRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    CWComplexCarrier T K E A B C H R P N bundle pkg ->
      Cont A B boundaryRead ->
        PkgSig bundle boundaryRead pkg ->
          UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory A ∧
            UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory H ∧ UnaryHistory R ∧
              UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory boundaryRead ∧
                Cont T K E ∧ Cont E A B ∧ Cont A B boundaryRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier boundaryRoute boundaryPkg
  obtain ⟨tUnary, kUnary, eUnary, aUnary, bUnary, cUnary, hUnary, rUnary, pUnary,
    nUnary, topologyCellRoute, attachingBoundaryRoute, provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed aUnary bUnary boundaryRoute
  exact
    ⟨tUnary, kUnary, eUnary, aUnary, bUnary, cUnary, hUnary, rUnary, pUnary, nUnary,
      boundaryUnary, topologyCellRoute, attachingBoundaryRoute, boundaryRoute, provenancePkg,
      boundaryPkg⟩

end BEDC.Derived.CWComplexUp
