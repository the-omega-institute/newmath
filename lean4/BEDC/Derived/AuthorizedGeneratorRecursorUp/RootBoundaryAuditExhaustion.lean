import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBoundaryAuditExhaustion
    [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      outputRead publicRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont output audit outputRead ->
      Cont outputRead routes publicRead ->
        Cont gap name boundaryRead ->
          hsame transport BHist.Empty ->
            UnaryHistory output ->
              UnaryHistory audit ->
                UnaryHistory routes ->
                  UnaryHistory gap ->
                    UnaryHistory name ->
                      PkgSig bundle provenance pkg ->
                        authorizedGeneratorRecursorFromEventFlow
                            (authorizedGeneratorRecursorToEventFlow
                              (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                branches descent output audit transport routes provenance gap
                                name)) =
                          some
                            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                              branches descent output audit transport routes provenance gap name) ∧
                          UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                            Cont output audit outputRead ∧
                              Cont outputRead routes publicRead ∧
                                Cont gap name boundaryRead ∧ hsame transport BHist.Empty ∧
                                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro outputAuditOutputRead outputReadRoutesPublicRead gapNameBoundaryRead transportEmpty
    outputUnary auditUnary routesUnary gapUnary nameUnary provenancePkg
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
            audit transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary routesUnary outputReadRoutesPublicRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundaryRead
  exact
    ⟨roundTrip, publicReadUnary, boundaryReadUnary, outputAuditOutputRead,
      outputReadRoutesPublicRead, gapNameBoundaryRead, transportEmpty, provenancePkg⟩

theorem AuthorizedGeneratorRecursorBoundaryAuditStrictObstruction
    [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      outputRead publicRead boundaryRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont output audit outputRead ->
      Cont outputRead routes publicRead ->
        Cont gap name boundaryRead ->
          Cont boundaryRead name refusedRead ->
            hsame transport BHist.Empty ->
              UnaryHistory output ->
                UnaryHistory audit ->
                  UnaryHistory routes ->
                    UnaryHistory gap ->
                      UnaryHistory name ->
                        PkgSig bundle provenance pkg ->
                          authorizedGeneratorRecursorFromEventFlow
                              (authorizedGeneratorRecursorToEventFlow
                                (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                  branches descent output audit transport routes provenance gap
                                  name)) =
                            some
                              (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                branches descent output audit transport routes provenance gap name) ∧
                          UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                            UnaryHistory refusedRead ∧ Cont boundaryRead name refusedRead ∧
                              hsame transport BHist.Empty ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro outputAuditOutputRead outputReadRoutesPublicRead gapNameBoundaryRead
    boundaryReadNameRefusedRead transportEmpty outputUnary auditUnary routesUnary gapUnary
    nameUnary provenancePkg
  have roundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
            audit transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary routesUnary outputReadRoutesPublicRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundaryRead
  have refusedReadUnary : UnaryHistory refusedRead :=
    unary_cont_closed boundaryReadUnary nameUnary boundaryReadNameRefusedRead
  exact
    ⟨roundTrip, publicReadUnary, boundaryReadUnary, refusedReadUnary,
      boundaryReadNameRefusedRead, transportEmpty, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
