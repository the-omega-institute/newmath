import BEDC.FKernel.Unary
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealCompletionWitnessExtractorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

def RealCompletionWitnessExtractorCarrier (D W M Q L S _H C P N : BHist) : Prop :=
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory S ∧
    Cont D W Q ∧ Cont Q M L ∧ Cont L S C ∧ hsame N (append P C)

theorem RealCompletionWitnessExtractorCarrier_selected_window_admission
    {D W M Q L S H C P N : BHist} :
    RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ->
      UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory C ∧ Cont D W Q ∧
          Cont Q M L ∧ Cont L S C ∧ hsame N (append P C) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro carrier
  obtain ⟨unaryD, unaryW, unaryM, unaryS, routeQ, routeL, routeC, nameSame⟩ := carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryD unaryW routeQ
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryQ unaryM routeL
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryL unaryS routeC
  exact
    ⟨unaryD, unaryW, unaryM, unaryQ, unaryL, unaryS, unaryC, routeQ, routeL,
      routeC, nameSame⟩

theorem RealCompletionWitnessExtractorCarrier_diagonal_handoff
    {D W M Q L S H C P N readback sealRow handoffRow : BHist} :
    RealCompletionWitnessExtractorCarrier D W M Q L S H C P N →
      Cont Q L sealRow →
        Cont sealRow S handoffRow →
          hsame readback Q →
            UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧
              UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory C ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧
                  UnaryHistory handoffRow ∧ Cont D W Q ∧ Cont Q M L ∧
                    Cont L S C ∧ Cont Q L sealRow ∧ Cont sealRow S handoffRow ∧
                      hsame readback Q ∧ hsame N (append P C) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont
  intro carrier sealRoute handoffRoute readbackSame
  obtain ⟨unaryD, unaryW, unaryM, unaryS, routeQ, routeL, routeC, nameSame⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryD unaryW routeQ
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryQ unaryM routeL
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryL unaryS routeC
  have readbackUnary : UnaryHistory readback :=
    unary_transport unaryQ (hsame_symm readbackSame)
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryL sealRoute
  have handoffUnary : UnaryHistory handoffRow :=
    unary_cont_closed sealUnary unaryS handoffRoute
  exact
    ⟨unaryD, unaryW, unaryM, unaryQ, unaryL, unaryS, unaryC, readbackUnary,
      sealUnary, handoffUnary, routeQ, routeL, routeC, sealRoute, handoffRoute,
      readbackSame, nameSame⟩

theorem RealCompletionWitnessExtractorCarrier_regular_readback_route
    {D W M Q L S H C P N : BHist} :
    RealCompletionWitnessExtractorCarrier D W M Q L S H C P N →
      SemanticNameCert
          (fun row : BHist =>
            RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ∧ hsame row Q)
          (fun row : BHist => hsame row Q ∧ UnaryHistory row)
          (fun _row : BHist => Cont D W Q ∧ Cont Q M L ∧ hsame N (append P C))
          hsame ∧
        UnaryHistory Q ∧ UnaryHistory L := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨unaryD, unaryW, unaryM, _unaryS, routeQ, routeL, _routeC, nameSame⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryD unaryW routeQ
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryQ unaryM routeL
  have sourceAtQ :
      RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ∧ hsame Q Q :=
    And.intro carrierWitness (hsame_refl Q)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ∧ hsame row Q)
          (fun row : BHist => hsame row Q ∧ UnaryHistory row)
          (fun _row : BHist => Cont D W Q ∧ Cont Q M L ∧ hsame N (append P C))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Q sourceAtQ
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, unary_transport unaryQ (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact ⟨routeQ, routeL, nameSame⟩
  }
  exact ⟨cert, unaryQ, unaryL⟩

theorem RealCompletionWitnessExtractorCarrier_seal_handoff_totality
    {D W M Q L S H C P N sealRow handoffRow : BHist} :
    RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ->
      Cont Q L sealRow ->
        Cont sealRow S handoffRow ->
          UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧
            UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory sealRow ∧
              UnaryHistory handoffRow ∧ Cont D W Q ∧ Cont Q M L ∧ Cont L S C ∧
                Cont Q L sealRow ∧ Cont sealRow S handoffRow ∧ hsame N (append P C) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro carrier sealRoute handoffRoute
  obtain ⟨unaryD, unaryW, unaryM, unaryS, routeQ, routeL, routeC, nameSame⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryD unaryW routeQ
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryQ unaryM routeL
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryL unaryS routeC
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryL sealRoute
  have unaryHandoff : UnaryHistory handoffRow :=
    unary_cont_closed unarySeal unaryS handoffRoute
  exact
    ⟨unaryD, unaryW, unaryM, unaryQ, unaryL, unaryS, unaryC, unarySeal,
      unaryHandoff, routeQ, routeL, routeC, sealRoute, handoffRoute, nameSame⟩

theorem RealCompletionWitnessExtractorCarrier_transport_totality
    {D W M Q L S H C P N D' W' M' Q' L' S' C' : BHist} :
    RealCompletionWitnessExtractorCarrier D W M Q L S H C P N ->
      hsame D D' ->
        hsame W W' ->
          hsame M M' ->
            hsame Q Q' ->
              hsame L L' ->
                hsame S S' ->
                  hsame C C' ->
                    UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory Q ∧
                      UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory C ∧
                        UnaryHistory D' ∧ UnaryHistory W' ∧ UnaryHistory M' ∧
                          UnaryHistory Q' ∧ UnaryHistory L' ∧ UnaryHistory S' ∧
                            UnaryHistory C' ∧ Cont D W Q ∧ Cont Q M L ∧ Cont L S C ∧
                              hsame N (append P C) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier sameD sameW sameM sameQ sameL sameS sameC
  obtain ⟨unaryD, unaryW, unaryM, unaryS, routeQ, routeL, routeC, nameSame⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryD unaryW routeQ
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryQ unaryM routeL
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryL unaryS routeC
  have unaryD' : UnaryHistory D' :=
    unary_transport unaryD sameD
  have unaryW' : UnaryHistory W' :=
    unary_transport unaryW sameW
  have unaryM' : UnaryHistory M' :=
    unary_transport unaryM sameM
  have unaryQ' : UnaryHistory Q' :=
    unary_transport unaryQ sameQ
  have unaryL' : UnaryHistory L' :=
    unary_transport unaryL sameL
  have unaryS' : UnaryHistory S' :=
    unary_transport unaryS sameS
  have unaryC' : UnaryHistory C' :=
    unary_transport unaryC sameC
  exact
    ⟨unaryD, unaryW, unaryM, unaryQ, unaryL, unaryS, unaryC, unaryD', unaryW',
      unaryM', unaryQ', unaryL', unaryS', unaryC', routeQ, routeL, routeC, nameSame⟩

end BEDC.Derived.RealCompletionWitnessExtractorUp
