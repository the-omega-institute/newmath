import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineBorelIntervalUp

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

inductive HeineBorelIntervalUp : Type where
  | mk (A B K M Z F T S R E Q C P N : BHist) : HeineBorelIntervalUp
  deriving DecidableEq

def heineBorelIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineBorelIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineBorelIntervalEncodeBHist h

def heineBorelIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineBorelIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineBorelIntervalDecodeBHist tail)

theorem HeineBorelIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def heineBorelIntervalFields : HeineBorelIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N =>
      [A, B, K, M, Z, F, T, S, R, E, Q, C, P, N]

def heineBorelIntervalToEventFlow : HeineBorelIntervalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (heineBorelIntervalFields x).map heineBorelIntervalEncodeBHist

def heineBorelIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => heineBorelIntervalEventAtDefault index rest

def heineBorelIntervalFromEventFlow (eventFlow : EventFlow) : Option HeineBorelIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HeineBorelIntervalUp.mk
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 0 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 1 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 2 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 3 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 4 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 5 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 6 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 7 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 8 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 9 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 10 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 11 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 12 eventFlow))
      (heineBorelIntervalDecodeBHist (heineBorelIntervalEventAtDefault 13 eventFlow)))

theorem HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HeineBorelIntervalUp,
      heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B K M Z F T S R E Q C P N =>
      change
        some
          (HeineBorelIntervalUp.mk
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist A))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist B))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist K))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist M))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist Z))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist F))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist T))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist S))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist R))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist E))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist Q))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist C))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist P))
            (heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist N))) =
          some (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
      rw [HeineBorelIntervalTasteGate_single_carrier_alignment_decode A,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode B,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode K,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode M,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode Z,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode F,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode T,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode S,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode R,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode E,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode Q,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode C,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode P,
        HeineBorelIntervalTasteGate_single_carrier_alignment_decode N]

theorem HeineBorelIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HeineBorelIntervalUp} :
    heineBorelIntervalToEventFlow x = heineBorelIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow x) =
        heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow y) :=
    congrArg heineBorelIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance heineBorelIntervalBHistCarrier : BHistCarrier HeineBorelIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineBorelIntervalToEventFlow
  fromEventFlow := heineBorelIntervalFromEventFlow

instance heineBorelIntervalChapterTasteGate : ChapterTasteGate HeineBorelIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change heineBorelIntervalFromEventFlow (heineBorelIntervalToEventFlow x) = some x
    exact HeineBorelIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HeineBorelIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HeineBorelIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  heineBorelIntervalChapterTasteGate

theorem HeineBorelIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, heineBorelIntervalDecodeBHist (heineBorelIntervalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HeineBorelIntervalUp) ∧
        Nonempty (ChapterTasteGate HeineBorelIntervalUp) ∧
          heineBorelIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HeineBorelIntervalTasteGate_single_carrier_alignment_decode,
      ⟨heineBorelIntervalBHistCarrier⟩,
      ⟨heineBorelIntervalChapterTasteGate⟩,
      rfl⟩

def HeineBorelIntervalCoverageRoute [AskSetup] [PackageSetup]
    (x : HeineBorelIntervalUp) (net mesh coverageRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  match x with
  | HeineBorelIntervalUp.mk _A _B K M Z F _T _S _R _E Q C P N =>
      UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory Z ∧ UnaryHistory F ∧
        UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          Cont K M net ∧ Cont net mesh coverageRead ∧ Cont Z F coverageRead ∧
            Cont C P N ∧ hsame mesh M ∧ PkgSig bundle coverageRead pkg

theorem HeineBorelIntervalNetCoverage [AskSetup] [PackageSetup]
    (x : HeineBorelIntervalUp) {net mesh coverageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute x net mesh coverageRead bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row net ∨ hsame row mesh ∨ hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont net mesh coverageRead ∧ PkgSig bundle coverageRead pkg)
          hsame ∧
        UnaryHistory coverageRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro route
  cases x with
  | mk A B K M Z F T S R E Q C P N =>
      obtain ⟨kUnary, mUnary, zUnary, fUnary, _qUnary, _cUnary, _pUnary, _nUnary,
        netRoute, requestedRoute, _finiteCoverageRoute, _replayRoute, meshSame, coveragePkg⟩ :=
        route
      have netUnary : UnaryHistory net :=
        unary_cont_closed kUnary mUnary netRoute
      have meshUnary : UnaryHistory mesh :=
        unary_transport_symm mUnary meshSame
      have coverageUnary : UnaryHistory coverageRead :=
        unary_cont_closed netUnary meshUnary requestedRoute
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row net ∨ hsame row mesh ∨ hsame row coverageRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont net mesh coverageRead ∧ PkgSig bundle coverageRead pkg)
              hsame := {
        core := {
          carrier_inhabited := Exists.intro coverageRead
            ⟨hsame_refl coverageRead, coverageUnary⟩
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
            intro _row _other sameRows source
            exact
              ⟨hsame_trans (hsame_symm sameRows) source.left,
                unary_transport source.right sameRows⟩
        }
        pattern_sound := by
          intro _row source
          exact Or.inr <| Or.inr source.left
        ledger_sound := by
          intro _row source
          exact ⟨source.right, requestedRoute, coveragePkg⟩
      }
      exact ⟨cert, coverageUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
