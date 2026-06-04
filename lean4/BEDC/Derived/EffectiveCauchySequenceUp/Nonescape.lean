import BEDC.Derived.EffectiveCauchySequenceUp.TasteGate

namespace BEDC.Derived.EffectiveCauchySequenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem EffectiveCauchySequenceNonescape
    {S M W D Q E H C P N readM readW readD readQ readE : BHist} :
    Cont S M readM →
      Cont readM W readW →
        Cont readW D readD →
          Cont readD Q readQ →
            Cont readQ E readE →
              UnaryHistory S →
                UnaryHistory M →
                  UnaryHistory W →
                    UnaryHistory D →
                      UnaryHistory Q →
                        UnaryHistory E →
                          SemanticNameCert
                            (fun row : BHist =>
                              exists S M W D Q E H C P N : BHist,
                                EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                                    EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧
                                  hsame row N)
                            (fun row : BHist =>
                              exists S M W D Q E H C P N : BHist,
                                EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                                    EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧
                                  hsame row N)
                            (fun row : BHist =>
                              exists S M W D Q E H C P N : BHist,
                                EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                                    EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧
                                  hsame row N)
                            hsame ∧
                            UnaryHistory readM ∧ UnaryHistory readW ∧
                              UnaryHistory readD ∧ UnaryHistory readQ ∧
                                UnaryHistory readE ∧ Cont S M readM ∧
                                  Cont readM W readW ∧ Cont readW D readD ∧
                                    Cont readD Q readQ ∧ Cont readQ E readE := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro routeM routeW routeD routeQ routeE unaryS unaryM unaryW unaryD unaryQ unaryE
  have unaryReadM : UnaryHistory readM :=
    unary_cont_closed unaryS unaryM routeM
  have unaryReadW : UnaryHistory readW :=
    unary_cont_closed unaryReadM unaryW routeW
  have unaryReadD : UnaryHistory readD :=
    unary_cont_closed unaryReadW unaryD routeD
  have unaryReadQ : UnaryHistory readQ :=
    unary_cont_closed unaryReadD unaryQ routeQ
  have unaryReadE : UnaryHistory readE :=
    unary_cont_closed unaryReadQ unaryE routeE
  let Carrier : BHist → Prop :=
    fun row : BHist =>
      exists S M W D Q E H C P N : BHist,
        EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
            EffectiveCauchySequenceUp.mk S M W D Q E H C P N ∧
          hsame row N
  have core : NameCert Carrier hsame := {
    carrier_inhabited := by
      exact ⟨N, S, M, W, D, Q, E, H, C, P, N, rfl, hsame_refl N⟩
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
      intro _row other sameRows source
      obtain ⟨sourceS, sourceM, sourceW, sourceD, sourceQ, sourceE, sourceH, sourceC,
        sourceP, sourceN, sourceEq, sourceSame⟩ := source
      exact
        ⟨sourceS, sourceM, sourceW, sourceD, sourceQ, sourceE, sourceH, sourceC, sourceP,
          sourceN, sourceEq, hsame_trans (hsame_symm sameRows) sourceSame⟩
  }
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, unaryReadM, unaryReadW, unaryReadD, unaryReadQ, unaryReadE, routeM, routeW,
      routeD, routeQ, routeE⟩

end BEDC.Derived.EffectiveCauchySequenceUp
