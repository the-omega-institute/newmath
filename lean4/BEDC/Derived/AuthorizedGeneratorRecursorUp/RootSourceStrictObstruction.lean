import BEDC.Derived.AuthorizedGeneratorRecursorUp.RootSource

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootSourceStrictObstruction [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      sourceRead boundaryRead outputRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signature eliminator sourceRead ->
      Cont sourceRead routes outputRead ->
        Cont gap name boundaryRead ->
          Cont outputRead provenance ledgerRead ->
            UnaryHistory signature ->
              UnaryHistory eliminator ->
                UnaryHistory routes ->
                  UnaryHistory gap ->
                    UnaryHistory name ->
                      UnaryHistory provenance ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle ledgerRead pkg ->
                            UnaryHistory sourceRead ∧ UnaryHistory boundaryRead ∧
                              UnaryHistory outputRead ∧ UnaryHistory ledgerRead ∧
                                Cont signature eliminator sourceRead ∧
                                  Cont sourceRead routes outputRead ∧
                                    Cont gap name boundaryRead ∧
                                      Cont outputRead provenance ledgerRead ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro signatureEliminatorSource sourceRoutesOutput gapNameBoundary outputProvenanceLedger
    signatureUnary eliminatorUnary routesUnary gapUnary nameUnary provenanceUnary provenancePkg
    ledgerPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorSource
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed sourceUnary routesUnary sourceRoutesOutput
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundary
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed outputUnary provenanceUnary outputProvenanceLedger
  exact
    ⟨sourceUnary, boundaryUnary, outputUnary, ledgerUnary, signatureEliminatorSource,
      sourceRoutesOutput, gapNameBoundary, outputProvenanceLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
