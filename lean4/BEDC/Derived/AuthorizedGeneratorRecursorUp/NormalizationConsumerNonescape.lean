import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorNormalizationConsumerNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead boundaryRead normalizationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont G N boundaryRead ->
          Cont outputRead boundaryRead normalizationRead ->
            PkgSig bundle normalizationRead pkg ->
              UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                UnaryHistory normalizationRead ∧ hsame H (append A C) ∧
                  Cont O A outputRead ∧ Cont G N boundaryRead ∧
                    Cont outputRead boundaryRead normalizationRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle normalizationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame PkgSig
  intro carrier outputRoute boundaryRoute normalizationRoute normalizationPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH, unaryC,
      provenanceUnary, unaryG, unaryN, _contIEM, _contMBD, _contDOA, sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed outputUnary boundaryUnary normalizationRoute
  exact
    ⟨outputUnary, boundaryUnary, normalizationUnary, sameTransport, outputRoute,
      boundaryRoute, normalizationRoute, provenancePkg, normalizationPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
