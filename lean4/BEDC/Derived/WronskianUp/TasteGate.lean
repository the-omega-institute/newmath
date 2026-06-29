import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WronskianUp : Type where
  | mk
      (family derivative jet determinant window readback realSeal transport replay
        provenance localName : BHist) :
      WronskianUp
  deriving DecidableEq

def wronskianEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: wronskianEncodeBHist h
  | BHist.e1 h => BMark.b1 :: wronskianEncodeBHist h

def wronskianDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (wronskianDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (wronskianDecodeBHist tail)

private theorem wronskianDecode_encode_bhist :
    ∀ h : BHist, wronskianDecodeBHist (wronskianEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def wronskianToEventFlow : WronskianUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WronskianUp.mk family derivative jet determinant window readback realSeal transport
      replay provenance localName =>
      [[BMark.b0],
        wronskianEncodeBHist family,
        [BMark.b1, BMark.b0],
        wronskianEncodeBHist derivative,
        [BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist jet,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist determinant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        wronskianEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        wronskianEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        wronskianEncodeBHist localName]

def wronskianFromEventFlow : EventFlow → Option WronskianUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: family :: _tag1 :: derivative :: _tag2 :: jet :: _tag3 ::
      determinant :: _tag4 :: window :: _tag5 :: readback :: _tag6 ::
        realSeal :: _tag7 :: transport :: _tag8 :: replay :: _tag9 ::
          provenance :: _tag10 :: localName :: [] =>
      some
        (WronskianUp.mk
          (wronskianDecodeBHist family)
          (wronskianDecodeBHist derivative)
          (wronskianDecodeBHist jet)
          (wronskianDecodeBHist determinant)
          (wronskianDecodeBHist window)
          (wronskianDecodeBHist readback)
          (wronskianDecodeBHist realSeal)
          (wronskianDecodeBHist transport)
          (wronskianDecodeBHist replay)
          (wronskianDecodeBHist provenance)
          (wronskianDecodeBHist localName))
  | _ => none

private theorem wronskian_round_trip :
    ∀ x : WronskianUp, wronskianFromEventFlow (wronskianToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family derivative jet determinant window readback realSeal transport replay
      provenance localName =>
      change
        some
          (WronskianUp.mk
            (wronskianDecodeBHist (wronskianEncodeBHist family))
            (wronskianDecodeBHist (wronskianEncodeBHist derivative))
            (wronskianDecodeBHist (wronskianEncodeBHist jet))
            (wronskianDecodeBHist (wronskianEncodeBHist determinant))
            (wronskianDecodeBHist (wronskianEncodeBHist window))
            (wronskianDecodeBHist (wronskianEncodeBHist readback))
            (wronskianDecodeBHist (wronskianEncodeBHist realSeal))
            (wronskianDecodeBHist (wronskianEncodeBHist transport))
            (wronskianDecodeBHist (wronskianEncodeBHist replay))
            (wronskianDecodeBHist (wronskianEncodeBHist provenance))
            (wronskianDecodeBHist (wronskianEncodeBHist localName))) =
          some
            (WronskianUp.mk family derivative jet determinant window readback realSeal
              transport replay provenance localName)
      rw [wronskianDecode_encode_bhist family, wronskianDecode_encode_bhist derivative,
        wronskianDecode_encode_bhist jet, wronskianDecode_encode_bhist determinant,
        wronskianDecode_encode_bhist window, wronskianDecode_encode_bhist readback,
        wronskianDecode_encode_bhist realSeal, wronskianDecode_encode_bhist transport,
        wronskianDecode_encode_bhist replay, wronskianDecode_encode_bhist provenance,
        wronskianDecode_encode_bhist localName]

private theorem wronskianToEventFlow_injective {x y : WronskianUp} :
    wronskianToEventFlow x = wronskianToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      wronskianFromEventFlow (wronskianToEventFlow x) =
        wronskianFromEventFlow (wronskianToEventFlow y) :=
    congrArg wronskianFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (wronskian_round_trip x).symm
      (Eq.trans hread (wronskian_round_trip y)))

instance wronskianBHistCarrier : BHistCarrier WronskianUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := wronskianToEventFlow
  fromEventFlow := wronskianFromEventFlow

instance wronskianChapterTasteGate : ChapterTasteGate WronskianUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change wronskianFromEventFlow (wronskianToEventFlow x) = some x
    exact wronskian_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (wronskianToEventFlow_injective heq)

def taste_gate : ChapterTasteGate WronskianUp :=
  -- BEDC touchpoint anchor: BHist BMark
  wronskianChapterTasteGate

def WronskianObligationRowSpec
    (F D J Omega S R E H C P N row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨ hsame row S ∨
    hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
      hsame row N

theorem WronskianNameCertObligations (F D J Omega S R E H C P N : BHist) :
    SemanticNameCert
      (WronskianObligationRowSpec F D J Omega S R E H C P N)
      (WronskianObligationRowSpec F D J Omega S R E H C P N)
      (WronskianObligationRowSpec F D J Omega S R E H C P N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro F (Or.inl (hsame_refl F))
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro _h _k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameKH : hsame k h := hsame_symm sameHK
        cases sourceH with
        | inl sameF =>
            exact Or.inl (hsame_trans sameKH sameF)
        | inr rest =>
            cases rest with
            | inl sameD =>
                exact Or.inr (Or.inl (hsame_trans sameKH sameD))
            | inr rest =>
                cases rest with
                | inl sameJ =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans sameKH sameJ)))
                | inr rest =>
                    cases rest with
                    | inl sameOmega =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl (hsame_trans sameKH sameOmega))))
                    | inr rest =>
                        cases rest with
                        | inl sameS =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl (hsame_trans sameKH sameS)))))
                        | inr rest =>
                            cases rest with
                            | inl sameR =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inl (hsame_trans sameKH sameR))))))
                            | inr rest =>
                                cases rest with
                                | inl sameE =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl (hsame_trans sameKH sameE)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameH =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans sameKH sameH))))))))
                                    | inr rest =>
                                        cases rest with
                                        | inl sameC =>
                                            exact
                                              Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans sameKH
                                                                  sameC)))))))))
                                        | inr rest =>
                                            cases rest with
                                            | inl sameP =>
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
                                                                    (Or.inl
                                                                      (hsame_trans sameKH
                                                                        sameP))))))))))
                                            | inr sameN =>
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
                                                                    (Or.inr
                                                                      (hsame_trans sameKH
                                                                        sameN))))))))))
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.WronskianUp
