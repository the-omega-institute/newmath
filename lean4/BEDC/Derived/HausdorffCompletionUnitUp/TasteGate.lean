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

namespace BEDC.Derived.HausdorffCompletionUnitUp

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

inductive HausdorffCompletionUnitUp : Type where
  | mk (M S J W R E H C P N : BHist) : HausdorffCompletionUnitUp
  deriving DecidableEq

def hausdorffCompletionUnitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionUnitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionUnitEncodeBHist h

def hausdorffCompletionUnitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionUnitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionUnitDecodeBHist tail)

private theorem hausdorffCompletionUnit_decode_encode :
    ∀ h : BHist,
      hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffCompletionUnitFields : HausdorffCompletionUnitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionUnitUp.mk M S J W R E H C P N => [M, S, J, W, R, E, H, C, P, N]

def hausdorffCompletionUnitToEventFlow : HausdorffCompletionUnitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffCompletionUnitFields x).map hausdorffCompletionUnitEncodeBHist

private def hausdorffCompletionUnitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffCompletionUnitEventAt index rest

def hausdorffCompletionUnitFromEventFlow : EventFlow → Option HausdorffCompletionUnitUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (HausdorffCompletionUnitUp.mk
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 0 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 1 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 2 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 3 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 4 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 5 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 6 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 7 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 8 ef))
          (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 9 ef)))

private theorem hausdorffCompletionUnit_round_trip (x : HausdorffCompletionUnitUp) :
    hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S J W R E H C P N =>
      change
        some
            (HausdorffCompletionUnitUp.mk
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist M))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist S))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist J))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist W))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist R))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist E))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist H))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist C))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist P))
              (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist N))) =
          some (HausdorffCompletionUnitUp.mk M S J W R E H C P N)
      rw [hausdorffCompletionUnit_decode_encode M, hausdorffCompletionUnit_decode_encode S,
        hausdorffCompletionUnit_decode_encode J, hausdorffCompletionUnit_decode_encode W,
        hausdorffCompletionUnit_decode_encode R, hausdorffCompletionUnit_decode_encode E,
        hausdorffCompletionUnit_decode_encode H, hausdorffCompletionUnit_decode_encode C,
        hausdorffCompletionUnit_decode_encode P, hausdorffCompletionUnit_decode_encode N]

private theorem hausdorffCompletionUnitToEventFlow_injective
    {x y : HausdorffCompletionUnitUp} :
    hausdorffCompletionUnitToEventFlow x = hausdorffCompletionUnitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) =
        hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow y) :=
    congrArg hausdorffCompletionUnitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hausdorffCompletionUnit_round_trip x).symm
      (Eq.trans hread (hausdorffCompletionUnit_round_trip y)))

instance hausdorffCompletionUnitBHistCarrier : BHistCarrier HausdorffCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionUnitToEventFlow
  fromEventFlow := hausdorffCompletionUnitFromEventFlow

instance hausdorffCompletionUnitChapterTasteGate :
    ChapterTasteGate HausdorffCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := hausdorffCompletionUnit_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (hausdorffCompletionUnitToEventFlow_injective heq)

def HausdorffCompletionUnitCarrier [AskSetup] [PackageSetup]
    (M S J W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory J ∧ UnaryHistory W ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont M S J ∧ PkgSig bundle P pkg

theorem HausdorffCompletionUnitNamecertObligations [AskSetup] [PackageSetup]
    {M S J W R E H C P N unitRead readbackRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionUnitCarrier M S J W R E H C P N bundle pkg →
      Cont J W unitRead →
        Cont unitRead R readbackRead →
          Cont readbackRead E sealRead →
            Cont sealRead N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row S ∨ hsame row J ∨ hsame row W ∨
                          hsame row R ∨ hsame row E ∨ hsame row N ∨
                            hsame row unitRead ∨ hsame row readbackRead ∨
                              hsame row sealRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M S J ∧ Cont J W unitRead ∧
                          Cont unitRead R readbackRead ∧ Cont readbackRead E sealRead ∧
                            Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory unitRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: HausdorffCompletionUnitCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier unitRoute readbackRoute sealRoute namedRoute namedPkg
  obtain ⟨mUnary, sUnary, jUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary,
    nUnary, sourceRoute, _provenancePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed jUnary wUnary unitRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed unitUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row S ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row N ∨ hsame row unitRead ∨ hsame row readbackRead ∨
                hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M S J ∧ Cont J W unitRead ∧
              Cont unitRead R readbackRead ∧ Cont readbackRead E sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, unitRoute, readbackRoute, sealRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, unitUnary, readbackUnary, sealUnary, namedUnary⟩

end BEDC.Derived.HausdorffCompletionUnitUp
