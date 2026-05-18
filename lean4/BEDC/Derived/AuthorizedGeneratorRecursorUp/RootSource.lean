import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootSource [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      sourceRead boundaryRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signature eliminator sourceRead ->
      Cont sourceRead routes outputRead ->
        Cont gap name boundaryRead ->
          UnaryHistory signature ->
            UnaryHistory eliminator ->
              UnaryHistory routes ->
                UnaryHistory gap ->
                  UnaryHistory name ->
                    PkgSig bundle provenance pkg ->
                      authorizedGeneratorRecursorFromEventFlow
                          (authorizedGeneratorRecursorToEventFlow
                            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                              descent output audit transport routes provenance gap name)) =
                        some
                          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                            descent output audit transport routes provenance gap name) ∧
                        UnaryHistory sourceRead ∧ UnaryHistory boundaryRead ∧
                          UnaryHistory outputRead ∧ Cont signature eliminator sourceRead ∧
                            Cont sourceRead routes outputRead ∧ Cont gap name boundaryRead ∧
                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro signatureEliminatorSource sourceRoutesOutput gapNameBoundary signatureUnary
    eliminatorUnary routesUnary gapUnary nameUnary provenancePkg
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorSource
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed sourceUnary routesUnary sourceRoutesOutput
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundary
  exact
    ⟨roundTrip, sourceUnary, boundaryUnary, outputUnary, signatureEliminatorSource,
      sourceRoutesOutput, gapNameBoundary, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
