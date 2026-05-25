import BEDC.Derived.AuthorizedGeneratorRecursorUp.AcceptanceBudgetCover
import BEDC.Derived.AuthorizedGeneratorRecursorUp.GroundRouteRefusalSurface

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAcceptanceObstructionLocality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N budgetRead auditRead terminalRead groundRead refusalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont B D budgetRead →
        Cont O A auditRead →
          Cont auditRead N terminalRead →
            Cont G N groundRead →
              Cont groundRead A refusalRead →
                PkgSig bundle terminalRead pkg →
                  PkgSig bundle refusalRead pkg →
                    UnaryHistory terminalRead ∧ UnaryHistory refusalRead ∧
                      Cont auditRead N terminalRead ∧ Cont groundRead A refusalRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
                          PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier budgetCont auditCont terminalCont groundCont refusalCont terminalPkg refusalPkg
  have budgetCover :=
    AuthorizedGeneratorRecursorAcceptanceBudgetCover
      (I := I) (E := E) (M := M) (B := B) (D := D) (O := O) (A := A) (H := H)
      (C := C) (P := P) (G := G) (N := N) (budgetRead := budgetRead)
      (auditRead := auditRead) (terminalRead := terminalRead) (bundle := bundle)
      (pkg := pkg) carrier budgetCont auditCont terminalCont terminalPkg
  have groundRefusal :=
    AuthorizedGeneratorRecursorGroundRouteRefusalSurface
      (I := I) (E := E) (M := M) (B := B) (D := D) (O := O) (A := A) (H := H)
      (C := C) (P := P) (G := G) (N := N) (groundRead := groundRead)
      (refusalRead := refusalRead) (bundle := bundle) (pkg := pkg) carrier groundCont
      refusalCont refusalPkg
  rcases budgetCover with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, _unaryA, _unaryG,
      _unaryN, _budgetUnary, _auditUnary, terminalUnary, _budgetCont, _auditCont,
      terminalCont', provenancePkg, terminalPkg'⟩
  rcases groundRefusal with
    ⟨_groundUnaryG, _groundUnaryN, _refusalUnaryA, _groundUnary, refusalUnary,
      _sameTransport, _groundCont, refusalCont', _provenancePkg, refusalPkg'⟩
  exact
    ⟨terminalUnary, refusalUnary, terminalCont', refusalCont', provenancePkg,
      terminalPkg', refusalPkg'⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
