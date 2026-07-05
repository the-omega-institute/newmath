import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyRateCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyRateCompletionUp : Type where
  | mk (S M D R E B H C P N : BHist) : BishopCauchyRateCompletionUp
  deriving DecidableEq

def bishopCauchyRateCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyRateCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyRateCompletionEncodeBHist h

def bishopCauchyRateCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyRateCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyRateCompletionDecodeBHist tail)

private theorem BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode :
    ∀ h : BHist,
      bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyRateCompletionFields : BishopCauchyRateCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyRateCompletionUp.mk S M D R E B H C P N => [S, M, D, R, E, B, H, C, P, N]

def bishopCauchyRateCompletionToEventFlow : BishopCauchyRateCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCauchyRateCompletionFields x).map bishopCauchyRateCompletionEncodeBHist

private def bishopCauchyRateCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyRateCompletionEventAt index rest

def bishopCauchyRateCompletionFromEventFlow
    (ef : EventFlow) : Option BishopCauchyRateCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyRateCompletionUp.mk
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 0 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 1 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 2 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 3 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 4 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 5 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 6 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 7 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 8 ef))
      (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEventAt 9 ef)))

private theorem BishopCauchyRateCompletionCarrier_namecert_obligations_round_trip
    (x : BishopCauchyRateCompletionUp) :
    bishopCauchyRateCompletionFromEventFlow (bishopCauchyRateCompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M D R E B H C P N =>
      change
        some
          (BishopCauchyRateCompletionUp.mk
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist S))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist M))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist D))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist R))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist E))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist B))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist H))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist C))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist P))
            (bishopCauchyRateCompletionDecodeBHist (bishopCauchyRateCompletionEncodeBHist N))) =
          some (BishopCauchyRateCompletionUp.mk S M D R E B H C P N)
      rw [BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode S,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode M,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode D,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode R,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode E,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode B,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode H,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode C,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode P,
        BishopCauchyRateCompletionCarrier_namecert_obligations_decode_encode N]

private theorem BishopCauchyRateCompletionCarrier_namecert_obligations_injective
    {x y : BishopCauchyRateCompletionUp} :
    bishopCauchyRateCompletionToEventFlow x = bishopCauchyRateCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyRateCompletionFromEventFlow (bishopCauchyRateCompletionToEventFlow x) =
        bishopCauchyRateCompletionFromEventFlow (bishopCauchyRateCompletionToEventFlow y) :=
    congrArg bishopCauchyRateCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCauchyRateCompletionCarrier_namecert_obligations_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyRateCompletionCarrier_namecert_obligations_round_trip y)))

instance bishopCauchyRateCompletionBHistCarrier :
    BHistCarrier BishopCauchyRateCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyRateCompletionToEventFlow
  fromEventFlow := bishopCauchyRateCompletionFromEventFlow

instance bishopCauchyRateCompletionChapterTasteGate :
    ChapterTasteGate BishopCauchyRateCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchyRateCompletionFromEventFlow
        (bishopCauchyRateCompletionToEventFlow x) = some x
    exact BishopCauchyRateCompletionCarrier_namecert_obligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCauchyRateCompletionCarrier_namecert_obligations_injective heq)

theorem BishopCauchyRateCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S M D R E B H C P N rateRead toleranceRead regularRead completionRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    bishopCauchyRateCompletionFields
        (BishopCauchyRateCompletionUp.mk S M D R E B H C P N) =
        [S, M, D, R, E, B, H, C, P, N] →
      Cont S M rateRead →
        Cont rateRead D toleranceRead →
          Cont toleranceRead R regularRead →
            Cont regularRead B completionRead →
              Cont completionRead E sealRead →
                Cont sealRead N namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row M ∨ hsame row D ∨ hsame row R ∨
                            hsame row E ∨ hsame row B ∨ hsame row namedRead)
                        (fun _row : BHist =>
                          Cont S M rateRead ∧ Cont rateRead D toleranceRead ∧
                            Cont toleranceRead R regularRead ∧
                              Cont regularRead B completionRead ∧
                                Cont completionRead E sealRead ∧
                                  Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
                        hsame ∧
                      hsame namedRead
                        (append (append (append (append (append (append S M) D) R) B) E) N) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields routeRate routeTolerance routeRegular routeCompletion routeSeal routeNamed
    namedPkg
  have rateEq : rateRead = append S M := routeRate
  have toleranceEq : toleranceRead = append (append S M) D :=
    routeTolerance.trans (congrArg (fun row => append row D) rateEq)
  have regularEq : regularRead = append (append (append S M) D) R :=
    routeRegular.trans (congrArg (fun row => append row R) toleranceEq)
  have completionEq : completionRead = append (append (append (append S M) D) R) B :=
    routeCompletion.trans (congrArg (fun row => append row B) regularEq)
  have sealEq : sealRead = append (append (append (append (append S M) D) R) B) E :=
    routeSeal.trans (congrArg (fun row => append row E) completionEq)
  have namedEq :
      hsame namedRead (append (append (append (append (append (append S M) D) R) B) E) N) :=
    routeNamed.trans (congrArg (fun row => append row N) sealEq)
  have sourceWitness : hsame namedRead namedRead := hsame_refl namedRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row B ∨ hsame row namedRead)
          (fun _row : BHist =>
            Cont S M rateRead ∧ Cont rateRead D toleranceRead ∧
              Cont toleranceRead R regularRead ∧ Cont regularRead B completionRead ∧
                Cont completionRead E sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceWitness
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source)))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨routeRate, routeTolerance, routeRegular, routeCompletion, routeSeal, routeNamed,
          namedPkg⟩
  }
  exact ⟨cert, namedEq⟩

end BEDC.Derived.BishopCauchyRateCompletionUp
