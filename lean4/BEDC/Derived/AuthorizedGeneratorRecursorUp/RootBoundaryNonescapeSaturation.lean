import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBoundaryNonescapeSaturation
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead boundaryRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E branchRead →
        Cont branchRead D descentRead →
          Cont descentRead O outputRead →
            Cont outputRead C publicRead →
              Cont G N boundaryRead →
                Cont O A auditRead →
                  PkgSig bundle publicRead pkg →
                    UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                      UnaryHistory auditRead ∧ Cont I E branchRead ∧
                        Cont branchRead D descentRead ∧ Cont descentRead O outputRead ∧
                          Cont outputRead C publicRead ∧ Cont G N boundaryRead ∧
                            Cont O A auditRead ∧ hsame H (append A C) ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont UnaryHistory hsame
  intro carrier branchRoute descentRoute outputRoute publicRoute boundaryRoute auditRoute publicPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      _unaryP, unaryG, unaryN, _carrierBranch, _carrierDescent, _carrierOutput,
      transportSame, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary unaryD descentRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary unaryO outputRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary unaryC publicRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed unaryO unaryA auditRoute
  exact
    ⟨publicReadUnary, boundaryReadUnary, auditReadUnary, branchRoute, descentRoute,
      outputRoute, publicRoute, boundaryRoute, auditRoute, transportSame, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
