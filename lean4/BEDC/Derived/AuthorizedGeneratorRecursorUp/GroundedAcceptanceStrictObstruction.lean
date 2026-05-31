import BEDC.Derived.AuthorizedGeneratorRecursorUp.GroundRouteRefusalSurface

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorGroundedAcceptanceStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead groundRead
      refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont M D descentRead ->
          Cont branchRead descentRead outputRead ->
            Cont outputRead C publicRead ->
              Cont G N groundRead ->
                Cont groundRead A refusalRead ->
                  PkgSig bundle refusalRead pkg ->
                    UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                      UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                        UnaryHistory groundRead ∧ UnaryHistory refusalRead ∧
                          hsame H (append A C) ∧ Cont G N groundRead ∧
                            Cont groundRead A refusalRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier branchRoute descentRoute outputRoute publicRoute groundRoute refusalRoute
    refusalPkg
  have grounded :=
    AuthorizedGeneratorRecursorGroundRouteRefusalSurface
      (I := I) (E := E) (M := M) (B := B) (D := D) (O := O) (A := A) (H := H)
      (C := C) (P := P) (G := G) (N := N) (groundRead := groundRead)
      (refusalRead := refusalRead) (bundle := bundle) (pkg := pkg) carrier groundRoute
      refusalRoute refusalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, _unaryO, _unaryA, _unaryH,
      unaryC, _unaryP, _unaryG, _unaryN, _iem, _mbd, _doa, _sameTransport,
      _provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed unaryM unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed branchUnary descentUnary outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary unaryC publicRoute
  rcases grounded with
    ⟨_groundUnaryG, _groundUnaryN, _groundUnaryA, groundUnary, refusalUnary,
      sameTransport, groundRoute', refusalRoute', provenancePkg, refusalPkg'⟩
  exact
    ⟨branchUnary, descentUnary, outputUnary, publicUnary, groundUnary, refusalUnary,
      sameTransport, groundRoute', refusalRoute', provenancePkg, refusalPkg'⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
