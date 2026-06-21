import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealStepFunctionUp

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

inductive RealStepFunctionUp : Type where
  | mk (I T V S R G H C P N : BHist) : RealStepFunctionUp
  deriving DecidableEq

def realStepFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realStepFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realStepFunctionEncodeBHist h

def realStepFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realStepFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realStepFunctionDecodeBHist tail)

private theorem realStepFunction_decode_encode :
    ∀ h : BHist, realStepFunctionDecodeBHist (realStepFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realStepFunctionFields : RealStepFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealStepFunctionUp.mk I T V S R G H C P N => [I, T, V, S, R, G, H, C, P, N]

def realStepFunctionToEventFlow : RealStepFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realStepFunctionFields x).map realStepFunctionEncodeBHist

private def realStepFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realStepFunctionEventAtDefault index rest

def realStepFunctionFromEventFlow (ef : EventFlow) : Option RealStepFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealStepFunctionUp.mk
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 0 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 1 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 2 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 3 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 4 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 5 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 6 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 7 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 8 ef))
      (realStepFunctionDecodeBHist (realStepFunctionEventAtDefault 9 ef)))

private theorem realStepFunction_round_trip :
    ∀ x : RealStepFunctionUp,
      realStepFunctionFromEventFlow (realStepFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T V S R G H C P N =>
      change
        some
          (RealStepFunctionUp.mk
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist I))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist T))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist V))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist S))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist R))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist G))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist H))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist C))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist P))
            (realStepFunctionDecodeBHist (realStepFunctionEncodeBHist N))) =
          some (RealStepFunctionUp.mk I T V S R G H C P N)
      rw [realStepFunction_decode_encode I, realStepFunction_decode_encode T,
        realStepFunction_decode_encode V, realStepFunction_decode_encode S,
        realStepFunction_decode_encode R, realStepFunction_decode_encode G,
        realStepFunction_decode_encode H, realStepFunction_decode_encode C,
        realStepFunction_decode_encode P, realStepFunction_decode_encode N]

private theorem realStepFunction_toEventFlow_injective {x y : RealStepFunctionUp} :
    realStepFunctionToEventFlow x = realStepFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realStepFunctionFromEventFlow (realStepFunctionToEventFlow x) =
        realStepFunctionFromEventFlow (realStepFunctionToEventFlow y) :=
    congrArg realStepFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realStepFunction_round_trip x).symm
      (Eq.trans hread (realStepFunction_round_trip y)))

instance realStepFunctionBHistCarrier : BHistCarrier RealStepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realStepFunctionToEventFlow
  fromEventFlow := realStepFunctionFromEventFlow

instance realStepFunctionChapterTasteGate : ChapterTasteGate RealStepFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realStepFunctionFromEventFlow (realStepFunctionToEventFlow x) = some x
    exact realStepFunction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realStepFunction_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealStepFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realStepFunctionChapterTasteGate

def RealStepFunctionCarrier [AskSetup] [PackageSetup]
    (I T V S R G H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory I ∧ UnaryHistory T ∧ UnaryHistory V ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem RealStepFunctionNamecertObligations [AskSetup] [PackageSetup]
    {I T V S R G H C P N intervalRead partitionRead valueRead sumRead integrableRead
      regulatedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealStepFunctionCarrier I T V S R G H C P N bundle pkg ->
      Cont I T intervalRead ->
        Cont intervalRead V partitionRead ->
          Cont partitionRead S valueRead ->
            Cont valueRead R sumRead ->
              Cont sumRead G regulatedRead ->
                Cont regulatedRead N namedRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row I ∨ hsame row T ∨ hsame row V ∨ hsame row S ∨
                          hsame row R ∨ hsame row G ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont I T intervalRead ∧
                          Cont intervalRead V partitionRead ∧
                            Cont partitionRead S valueRead ∧
                              Cont valueRead R sumRead ∧
                                Cont sumRead G regulatedRead ∧
                                  Cont regulatedRead N namedRead ∧ PkgSig bundle P pkg)
                      hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier intervalRoute partitionRoute valueRoute sumRoute regulatedRoute namedRoute
  obtain ⟨iUnary, tUnary, vUnary, sUnary, rUnary, gUnary, _hUnary, _cUnary, _pUnary,
    nUnary, provenancePkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed iUnary tUnary intervalRoute
  have partitionUnary : UnaryHistory partitionRead :=
    unary_cont_closed intervalUnary vUnary partitionRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed partitionUnary sUnary valueRoute
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed valueUnary rUnary sumRoute
  have regulatedUnary : UnaryHistory regulatedRead :=
    unary_cont_closed sumUnary gUnary regulatedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed regulatedUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row T ∨ hsame row V ∨ hsame row S ∨ hsame row R ∨
              hsame row G ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I T intervalRead ∧ Cont intervalRead V partitionRead ∧
              Cont partitionRead S valueRead ∧ Cont valueRead R sumRead ∧
                Cont sumRead G regulatedRead ∧ Cont regulatedRead N namedRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, intervalRoute, partitionRoute, valueRoute, sumRoute, regulatedRoute,
          namedRoute, provenancePkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.RealStepFunctionUp
