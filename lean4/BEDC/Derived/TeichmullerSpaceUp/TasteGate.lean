import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TeichmullerSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TeichmullerSpaceUp : Type where
  | mk (S M J G D E H C P N : BHist) : TeichmullerSpaceUp
  deriving DecidableEq

def teichmullerSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: teichmullerSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: teichmullerSpaceEncodeBHist h

def teichmullerSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (teichmullerSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (teichmullerSpaceDecodeBHist tail)

private theorem TeichmullerSpaceCarrier_namecert_obligations_decode_encode :
    ∀ h : BHist, teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def teichmullerSpaceFields : TeichmullerSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TeichmullerSpaceUp.mk S M J G D E H C P N => [S, M, J, G, D, E, H, C, P, N]

def teichmullerSpaceToEventFlow : TeichmullerSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (teichmullerSpaceFields x).map teichmullerSpaceEncodeBHist

private def teichmullerSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => teichmullerSpaceEventAt index rest

def teichmullerSpaceFromEventFlow (ef : EventFlow) : Option TeichmullerSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TeichmullerSpaceUp.mk
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 0 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 1 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 2 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 3 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 4 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 5 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 6 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 7 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 8 ef))
      (teichmullerSpaceDecodeBHist (teichmullerSpaceEventAt 9 ef)))

private theorem TeichmullerSpaceCarrier_namecert_obligations_round_trip
    (x : TeichmullerSpaceUp) :
    teichmullerSpaceFromEventFlow (teichmullerSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M J G D E H C P N =>
      change
        some
          (TeichmullerSpaceUp.mk
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist S))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist M))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist J))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist G))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist D))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist E))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist H))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist C))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist P))
            (teichmullerSpaceDecodeBHist (teichmullerSpaceEncodeBHist N))) =
          some (TeichmullerSpaceUp.mk S M J G D E H C P N)
      rw [TeichmullerSpaceCarrier_namecert_obligations_decode_encode S,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode M,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode J,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode G,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode D,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode E,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode H,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode C,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode P,
        TeichmullerSpaceCarrier_namecert_obligations_decode_encode N]

private theorem TeichmullerSpaceCarrier_namecert_obligations_injective
    {x y : TeichmullerSpaceUp} :
    teichmullerSpaceToEventFlow x = teichmullerSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      teichmullerSpaceFromEventFlow (teichmullerSpaceToEventFlow x) =
        teichmullerSpaceFromEventFlow (teichmullerSpaceToEventFlow y) :=
    congrArg teichmullerSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TeichmullerSpaceCarrier_namecert_obligations_round_trip x).symm
      (Eq.trans hread (TeichmullerSpaceCarrier_namecert_obligations_round_trip y)))

instance teichmullerSpaceBHistCarrier : BHistCarrier TeichmullerSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := teichmullerSpaceToEventFlow
  fromEventFlow := teichmullerSpaceFromEventFlow

instance teichmullerSpaceChapterTasteGate : ChapterTasteGate TeichmullerSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change teichmullerSpaceFromEventFlow (teichmullerSpaceToEventFlow x) = some x
    exact TeichmullerSpaceCarrier_namecert_obligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TeichmullerSpaceCarrier_namecert_obligations_injective heq)

theorem TeichmullerSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S M J G D E H C P N markedRead complexRead metricRead deformationRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    teichmullerSpaceFields (TeichmullerSpaceUp.mk S M J G D E H C P N) =
        [S, M, J, G, D, E, H, C, P, N] →
      Cont S M markedRead →
        Cont markedRead J complexRead →
          Cont complexRead G metricRead →
            Cont metricRead D deformationRead →
              Cont deformationRead N namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row M ∨ hsame row J ∨ hsame row G ∨
                          hsame row D ∨ hsame row E ∨ hsame row namedRead)
                      (fun _row : BHist =>
                        Cont S M markedRead ∧ Cont markedRead J complexRead ∧
                          Cont complexRead G metricRead ∧ Cont metricRead D deformationRead ∧
                            Cont deformationRead N namedRead ∧ PkgSig bundle namedRead pkg)
                      hsame ∧
                    hsame namedRead
                      (append (append (append (append (append S M) J) G) D) N) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields routeMarked routeComplex routeMetric routeDeformation routeNamed namedPkg
  have markedEq : markedRead = append S M := routeMarked
  have complexEq : complexRead = append (append S M) J :=
    routeComplex.trans (congrArg (fun row => append row J) markedEq)
  have metricEq : metricRead = append (append (append S M) J) G :=
    routeMetric.trans (congrArg (fun row => append row G) complexEq)
  have deformationEq : deformationRead = append (append (append (append S M) J) G) D :=
    routeDeformation.trans (congrArg (fun row => append row D) metricEq)
  have namedEq : hsame namedRead (append (append (append (append (append S M) J) G) D) N) :=
    routeNamed.trans (congrArg (fun row => append row N) deformationEq)
  have sourceWitness : hsame namedRead namedRead := hsame_refl namedRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row J ∨ hsame row G ∨ hsame row D ∨
              hsame row E ∨ hsame row namedRead)
          (fun _row : BHist =>
            Cont S M markedRead ∧ Cont markedRead J complexRead ∧
              Cont complexRead G metricRead ∧ Cont metricRead D deformationRead ∧
                Cont deformationRead N namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact ⟨routeMarked, routeComplex, routeMetric, routeDeformation, routeNamed, namedPkg⟩
  }
  exact ⟨cert, namedEq⟩

end BEDC.Derived.TeichmullerSpaceUp
