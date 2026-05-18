import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBoundaryClosure [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead closedRead normalizationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont D O outputRead →
        Cont outputRead G closedRead →
          Cont O A normalizationRead →
            PkgSig bundle closedRead pkg →
              UnaryHistory outputRead ∧ UnaryHistory closedRead ∧
                UnaryHistory normalizationRead ∧ Cont D O outputRead ∧
                  Cont outputRead G closedRead ∧ Cont O A normalizationRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle closedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute closedRoute normalizationRoute closedPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, unaryD, unaryO, unaryA, unaryH, _unaryC,
      provenanceUnary, unaryG, _unaryN, _signatureMotive, _motiveDescent,
      _descentAudit, sameTransport, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryD unaryO outputRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed outputUnary unaryG closedRoute
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed unaryO unaryA normalizationRoute
  exact
    ⟨outputUnary, closedUnary, normalizationUnary, outputRoute, closedRoute,
      normalizationRoute, sameTransport, provenancePkg, closedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
