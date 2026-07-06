import BEDC.Derived.MollifierUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MollifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def MollifierCarrier_dyadic_kernel_normalization_carrier [AskSetup] [PackageSetup]
    (smooth support normalization convolution replay transport localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: MollifierUp BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  FieldFaithful.fields
      (MollifierUp.mk smooth support normalization convolution replay transport localName) =
    [smooth, support, normalization, convolution, replay, transport, localName] ∧
    UnaryHistory normalization ∧ Cont smooth support normalization ∧
      Cont support normalization convolution ∧ PkgSig bundle localName pkg

theorem MollifierCarrier_support_normalization_obligation
    {S R N P C H L supportRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          Cont S R N →
            Cont N P supportRead →
              UnaryHistory N ∧ UnaryHistory supportRead ∧
                Cont S R N ∧ Cont N P supportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary rUnary pUnary supportRoute readRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed nUnary pUnary readRoute
  exact ⟨nUnary, supportReadUnary, supportRoute, readRoute⟩

theorem MollifierCarrier_convolution_window_obligation
    {S R N P C H L replayRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            Cont S R N →
              Cont N P C →
                Cont C H replayRead →
                  UnaryHistory N ∧ UnaryHistory C ∧ UnaryHistory replayRead ∧
                    Cont S R N ∧ Cont N P C ∧ Cont C H replayRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary rUnary pUnary hUnary supportRoute convolutionRoute replayRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed nUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed cUnary hUnary replayRoute
  exact ⟨nUnary, cUnary, replayUnary, supportRoute, convolutionRoute, replayRoute⟩

theorem MollifierCarrier_compact_support_window
    {S R N P C H compactReplay compactTransport supportRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory C →
            UnaryHistory H →
              Cont S R N →
                Cont N P supportRead →
                  Cont R C compactReplay →
                    Cont compactReplay H compactTransport →
                      UnaryHistory supportRead ∧ UnaryHistory compactReplay ∧
                        UnaryHistory compactTransport ∧ Cont S R N ∧
                          Cont N P supportRead ∧ Cont R C compactReplay ∧
                            Cont compactReplay H compactTransport := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary rUnary pUnary cUnary hUnary supportRoute readRoute replayRoute transportRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed nUnary pUnary readRoute
  have compactReplayUnary : UnaryHistory compactReplay :=
    unary_cont_closed rUnary cUnary replayRoute
  have compactTransportUnary : UnaryHistory compactTransport :=
    unary_cont_closed compactReplayUnary hUnary transportRoute
  exact
    ⟨supportReadUnary, compactReplayUnary, compactTransportUnary, supportRoute, readRoute,
      replayRoute, transportRoute⟩

theorem MollifierCarrier_real_window_regularity
    {S R N P C H realRead transportRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            Cont S R N →
              Cont N P C →
                Cont C H realRead →
                  Cont realRead H transportRead →
                    UnaryHistory N ∧ UnaryHistory C ∧ UnaryHistory realRead ∧
                      UnaryHistory transportRead ∧ Cont S R N ∧ Cont N P C ∧
                        Cont C H realRead ∧ Cont realRead H transportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sUnary rUnary pUnary hUnary supportRoute windowRoute realRoute transportRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed nUnary pUnary windowRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed cUnary hUnary realRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed realUnary hUnary transportRoute
  exact
    ⟨nUnary, cUnary, realUnary, transportUnary, supportRoute, windowRoute, realRoute,
      transportRoute⟩

theorem MollifierCarrier_dyadic_kernel_normalization [AskSetup] [PackageSetup]
    {smooth support normalization convolution replay transport localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MollifierCarrier_dyadic_kernel_normalization_carrier smooth support normalization
        convolution replay transport localName bundle pkg →
      UnaryHistory normalization ∧ Cont smooth support normalization ∧
        Cont support normalization convolution ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: MollifierUp BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  obtain ⟨fieldRows, normalizationUnary, smoothSupportNormalization,
    supportNormalizationConvolution, localNamePkg⟩ := carrier
  cases fieldRows
  exact
    ⟨normalizationUnary, smoothSupportNormalization, supportNormalizationConvolution,
      localNamePkg⟩

theorem MollifierCarrier_nonescape_ledger_obligation
    {S R N P C H L replayRead outputRead boundaryRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            UnaryHistory L →
              Cont S R N →
                Cont N P C →
                  Cont C H replayRead →
                    Cont replayRead L outputRead →
                      Cont outputRead H boundaryRead →
                        SemanticNameCert
                            (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨
                                hsame row C ∨ hsame row H ∨ hsame row L ∨
                                  hsame row replayRead ∨ hsame row outputRead ∨
                                    hsame row boundaryRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧
                                Cont C H replayRead ∧ Cont replayRead L outputRead ∧
                                  Cont outputRead H boundaryRead)
                            hsame ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  intro sUnary rUnary pUnary hUnary lUnary supportRoute convolutionRoute replayRoute
    outputRoute boundaryRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed nUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed cUnary hUnary replayRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed replayUnary lUnary outputRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputUnary hUnary boundaryRoute
  let sourceSpec : BHist → Prop :=
    fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row
  let patternSpec : BHist → Prop :=
    fun row : BHist =>
      hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨ hsame row C ∨
        hsame row H ∨ hsame row L ∨ hsame row replayRead ∨ hsame row outputRead ∨
          hsame row boundaryRead
  let ledgerPolicy : BHist → Prop :=
    fun row : BHist =>
      UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧ Cont C H replayRead ∧
        Cont replayRead L outputRead ∧ Cont outputRead H boundaryRead
  have core : NameCert sourceSpec hsame := by
    exact
      { carrier_inhabited := ⟨boundaryRead, hsame_refl boundaryRead, boundaryUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row next same
          exact hsame_symm same
        equiv_trans := by
          intro row next final sameRowNext sameNextFinal
          exact hsame_trans sameRowNext sameNextFinal
        carrier_respects_equiv := by
          intro row next sameRowNext sourceRow
          cases sameRowNext
          exact sourceRow }
  have pattern_sound : ∀ {row : BHist}, sourceSpec row → patternSpec row := by
    intro row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))))
  have ledger_sound : ∀ {row : BHist}, sourceSpec row → ledgerPolicy row := by
    intro row sourceRow
    cases sourceRow.left
    exact
      ⟨boundaryUnary, supportRoute, convolutionRoute, replayRoute, outputRoute,
        boundaryRoute⟩
  exact
    And.intro
      { core := core, pattern_sound := pattern_sound, ledger_sound := ledger_sound }
      boundaryUnary

theorem MollifierCarrier_obligation_closure_package
    {S R N P C H L replayRead outputRead boundaryRead : BHist} :
    UnaryHistory S →
      UnaryHistory R →
        UnaryHistory P →
          UnaryHistory H →
            UnaryHistory L →
              Cont S R N →
                Cont N P C →
                  Cont C H replayRead →
                    Cont replayRead L outputRead →
                      Cont outputRead H boundaryRead →
                        SemanticNameCert
                            (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨
                                hsame row C ∨ hsame row H ∨ hsame row L ∨
                                  hsame row replayRead ∨ hsame row outputRead ∨
                                    hsame row boundaryRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧
                                Cont C H replayRead ∧ Cont replayRead L outputRead ∧
                                  Cont outputRead H boundaryRead)
                            hsame ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  intro sUnary rUnary pUnary hUnary lUnary supportRoute convolutionRoute replayRoute
    outputRoute boundaryRoute
  have nUnary : UnaryHistory N :=
    unary_cont_closed sUnary rUnary supportRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed nUnary pUnary convolutionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed cUnary hUnary replayRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed replayUnary lUnary outputRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputUnary hUnary boundaryRoute
  let sourceSpec : BHist → Prop :=
    fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row
  let patternSpec : BHist → Prop :=
    fun row : BHist =>
      hsame row S ∨ hsame row R ∨ hsame row N ∨ hsame row P ∨ hsame row C ∨
        hsame row H ∨ hsame row L ∨ hsame row replayRead ∨ hsame row outputRead ∨
          hsame row boundaryRead
  let ledgerPolicy : BHist → Prop :=
    fun row : BHist =>
      UnaryHistory row ∧ Cont S R N ∧ Cont N P C ∧ Cont C H replayRead ∧
        Cont replayRead L outputRead ∧ Cont outputRead H boundaryRead
  have core : NameCert sourceSpec hsame := by
    exact
      { carrier_inhabited := ⟨boundaryRead, hsame_refl boundaryRead, boundaryUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row next same
          exact hsame_symm same
        equiv_trans := by
          intro row next final sameRowNext sameNextFinal
          exact hsame_trans sameRowNext sameNextFinal
        carrier_respects_equiv := by
          intro row next sameRowNext sourceRow
          cases sameRowNext
          exact sourceRow }
  have pattern_sound : ∀ {row : BHist}, sourceSpec row → patternSpec row := by
    intro row sourceRow
    exact Or.inr
      (Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))))
  have ledger_sound : ∀ {row : BHist}, sourceSpec row → ledgerPolicy row := by
    intro row sourceRow
    cases sourceRow.left
    exact
      ⟨boundaryUnary, supportRoute, convolutionRoute, replayRoute, outputRoute,
        boundaryRoute⟩
  exact
    And.intro
      { core := core, pattern_sound := pattern_sound, ledger_sound := ledger_sound }
      boundaryUnary

end BEDC.Derived.MollifierUp
