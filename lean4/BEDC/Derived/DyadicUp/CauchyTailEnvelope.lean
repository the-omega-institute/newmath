import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicCauchyTailEnvelopeNameCertObligations [AskSetup] [PackageSetup]
    {source tail envelope regseq realSeal transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory tail ->
        UnaryHistory regseq ->
          UnaryHistory provenance ->
            Cont source tail envelope ->
              Cont envelope regseq realSeal ->
                PkgSig bundle provenance pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row envelope ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row tail ∨ hsame row envelope ∨
                          hsame row regseq ∨ hsame row realSeal ∨ hsame row provenance)
                      (fun row : BHist => hsame row envelope ∧ PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory envelope ∧ UnaryHistory realSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sourceUnary tailUnary regseqUnary _provenanceUnary sourceTailRoute envelopeRoute
    provenancePkg
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed sourceUnary tailUnary sourceTailRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed envelopeUnary regseqUnary envelopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row envelope ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row tail ∨ hsame row envelope ∨
              hsame row regseq ∨ hsame row realSeal ∨ hsame row provenance)
          (fun row : BHist => hsame row envelope ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro envelope ⟨hsame_refl envelope, envelopeUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, envelopeUnary, realSealUnary, provenancePkg⟩

theorem DyadicCauchyTailEnvelopeRegSeqRatRealRoute [AskSetup] [PackageSetup]
    {source tail envelope regseq realSeal replay provenance routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory tail ->
        UnaryHistory regseq ->
          UnaryHistory replay ->
            Cont source tail envelope ->
              Cont envelope regseq realSeal ->
                Cont source replay routeRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle routeRead pkg ->
                      UnaryHistory envelope ∧ UnaryHistory realSeal ∧
                        UnaryHistory routeRead ∧ Cont source tail envelope ∧
                          Cont envelope regseq realSeal ∧ Cont source replay routeRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro sourceUnary tailUnary regseqUnary replayUnary sourceTailRoute envelopeRoute
    replayRoute provenancePkg routePkg
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed sourceUnary tailUnary sourceTailRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed envelopeUnary regseqUnary envelopeRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed sourceUnary replayUnary replayRoute
  exact
    ⟨envelopeUnary, realSealUnary, routeUnary, sourceTailRoute, envelopeRoute, replayRoute,
      provenancePkg, routePkg⟩

theorem DyadicCauchyTailEnvelopeCommonRefinement [AskSetup] [PackageSetup]
    {source tail tail' envelope envelope' commonTail commonBudget regseq realSeal
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory tail →
        UnaryHistory tail' →
          UnaryHistory regseq →
            Cont source tail envelope →
              Cont source tail' envelope' →
                Cont envelope envelope' commonTail →
                  Cont commonTail regseq commonBudget →
                    Cont commonBudget regseq realSeal →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle commonBudget pkg →
                          UnaryHistory envelope ∧ UnaryHistory envelope' ∧
                            UnaryHistory commonTail ∧ UnaryHistory commonBudget ∧
                              UnaryHistory realSeal ∧ Cont source tail envelope ∧
                                Cont source tail' envelope' ∧
                                  Cont envelope envelope' commonTail ∧
                                    Cont commonTail regseq commonBudget ∧
                                      Cont commonBudget regseq realSeal ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle commonBudget pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro sourceUnary tailUnary tailPrimeUnary regseqUnary sourceTailRoute
    sourceTailPrimeRoute commonTailRoute commonBudgetRoute realSealRoute provenancePkg
    commonBudgetPkg
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed sourceUnary tailUnary sourceTailRoute
  have envelopePrimeUnary : UnaryHistory envelope' :=
    unary_cont_closed sourceUnary tailPrimeUnary sourceTailPrimeRoute
  have commonTailUnary : UnaryHistory commonTail :=
    unary_cont_closed envelopeUnary envelopePrimeUnary commonTailRoute
  have commonBudgetUnary : UnaryHistory commonBudget :=
    unary_cont_closed commonTailUnary regseqUnary commonBudgetRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed commonBudgetUnary regseqUnary realSealRoute
  exact
    ⟨envelopeUnary, envelopePrimeUnary, commonTailUnary, commonBudgetUnary,
      realSealUnary, sourceTailRoute, sourceTailPrimeRoute, commonTailRoute,
      commonBudgetRoute, realSealRoute, provenancePkg, commonBudgetPkg⟩

theorem DyadicCauchyTailEnvelopeWindowHandoff [AskSetup] [PackageSetup]
    {reindex stream regseq dyadic tail realSeal windowRead routeRead provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory reindex →
      UnaryHistory stream →
        UnaryHistory regseq →
          UnaryHistory dyadic →
            Cont reindex stream windowRead →
              Cont windowRead regseq routeRead →
                Cont routeRead dyadic tail →
                  Cont tail regseq realSeal →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle realSeal pkg →
                        UnaryHistory windowRead ∧ UnaryHistory routeRead ∧
                          UnaryHistory tail ∧ UnaryHistory realSeal ∧
                            Cont reindex stream windowRead ∧
                              Cont windowRead regseq routeRead ∧
                                Cont routeRead dyadic tail ∧
                                  Cont tail regseq realSeal ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro reindexUnary streamUnary regseqUnary dyadicUnary windowRoute routeReadRoute
    tailRoute realSealRoute provenancePkg realSealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed reindexUnary streamUnary windowRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed windowUnary regseqUnary routeReadRoute
  have tailUnary : UnaryHistory tail :=
    unary_cont_closed routeUnary dyadicUnary tailRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed tailUnary regseqUnary realSealRoute
  exact
    ⟨windowUnary, routeUnary, tailUnary, realSealUnary, windowRoute, routeReadRoute,
      tailRoute, realSealRoute, provenancePkg, realSealPkg⟩

theorem DyadicCauchyTailEnvelopeBudgetExhaustion [AskSetup] [PackageSetup]
    {source tail envelope regseq realSeal replay provenance routeRead windowRead budgetRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ->
      UnaryHistory tail ->
        UnaryHistory regseq ->
          UnaryHistory replay ->
            Cont source tail envelope ->
              Cont envelope regseq realSeal ->
                Cont source replay routeRead ->
                  Cont routeRead envelope windowRead ->
                    Cont windowRead realSeal budgetRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle budgetRead pkg ->
                          UnaryHistory envelope ∧ UnaryHistory realSeal ∧
                            UnaryHistory routeRead ∧ UnaryHistory windowRead ∧
                              UnaryHistory budgetRead ∧ Cont source tail envelope ∧
                                Cont envelope regseq realSeal ∧ Cont source replay routeRead ∧
                                  Cont routeRead envelope windowRead ∧
                                    Cont windowRead realSeal budgetRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro sourceUnary tailUnary regseqUnary replayUnary sourceTailRoute envelopeRoute
    replayRoute windowRoute budgetRoute provenancePkg budgetPkg
  have envelopeUnary : UnaryHistory envelope :=
    unary_cont_closed sourceUnary tailUnary sourceTailRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed envelopeUnary regseqUnary envelopeRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed sourceUnary replayUnary replayRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed routeUnary envelopeUnary windowRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed windowUnary realSealUnary budgetRoute
  exact
    ⟨envelopeUnary, realSealUnary, routeUnary, windowUnary, budgetUnary, sourceTailRoute,
      envelopeRoute, replayRoute, windowRoute, budgetRoute, provenancePkg, budgetPkg⟩

end BEDC.Derived.DyadicUp
