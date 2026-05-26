import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootOutputBoundaryStrictObstruction
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont D O outputRead ->
        Cont outputRead A auditRead ->
          Cont G N boundaryRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle boundaryRead pkg ->
                UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory boundaryRead ∧ Cont D O outputRead ∧
                    Cont outputRead A auditRead ∧ Cont G N boundaryRead ∧
                      hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier outputRoute auditRoute boundaryRoute provenancePkg boundaryPkg
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, _motiveUnary, _branchUnary, descentUnary,
      outputUnary, auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
      boundaryUnary, localCertUnary, _carrierSignature, _carrierDescent,
      _carrierOutput, transportSame, _carrierPkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary outputUnary outputRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary auditUnary auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary localCertUnary boundaryRoute
  exact
    ⟨outputReadUnary, auditReadUnary, boundaryReadUnary, outputRoute, auditRoute,
      boundaryRoute, transportSame, provenancePkg, boundaryPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
