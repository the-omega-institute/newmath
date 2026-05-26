import BEDC.Derived.AuthorizedGeneratorRecursorUp.AcceptanceBudgetCover
import BEDC.Derived.AuthorizedGeneratorRecursorUp.GroundRouteRefusalSurface

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAcceptanceBudgetStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N budgetRead auditRead terminalRead groundRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D budgetRead ->
        Cont O A auditRead ->
          Cont auditRead N terminalRead ->
            Cont G N groundRead ->
              Cont groundRead A refusalRead ->
                PkgSig bundle terminalRead pkg ->
                  PkgSig bundle refusalRead pkg ->
                    UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory groundRead ∧
                      UnaryHistory refusalRead ∧ Cont G N groundRead ∧
                        Cont groundRead A refusalRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle terminalRead pkg ∧
                            PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier budgetCont auditCont terminalCont groundCont refusalCont terminalPkg refusalPkg
  have cover :=
    AuthorizedGeneratorRecursorAcceptanceBudgetCover
      (I := I) (E := E) (M := M) (B := B) (D := D) (O := O) (A := A) (H := H)
      (C := C) (P := P) (G := G) (N := N) (budgetRead := budgetRead)
      (auditRead := auditRead) (terminalRead := terminalRead) (bundle := bundle)
      (pkg := pkg) carrier budgetCont auditCont terminalCont terminalPkg
  have refusal :=
    AuthorizedGeneratorRecursorGroundRouteRefusalSurface
      (I := I) (E := E) (M := M) (B := B) (D := D) (O := O) (A := A) (H := H)
      (C := C) (P := P) (G := G) (N := N) (groundRead := groundRead)
      (refusalRead := refusalRead) (bundle := bundle) (pkg := pkg) carrier groundCont
      refusalCont refusalPkg
  rcases cover with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, _unaryA, unaryG,
      unaryN, _budgetUnary, _auditUnary, _terminalUnary, _budgetRow, _auditRow,
      _terminalRow, provenancePkg, terminalPkg'⟩
  rcases refusal with
    ⟨_groundUnaryG, _groundUnaryN, _unaryAFromRefusal, groundUnary, refusalUnary,
      _transportSame, groundCont', refusalCont', provenancePkg', refusalPkg'⟩
  exact
    ⟨unaryG, unaryN, groundUnary, refusalUnary, groundCont', refusalCont',
      provenancePkg', terminalPkg', refusalPkg'⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
