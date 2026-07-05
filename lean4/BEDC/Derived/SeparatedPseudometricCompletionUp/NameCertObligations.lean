import BEDC.Derived.SeparatedPseudometricCompletionUp
import BEDC.Derived.SeparatedPseudometricCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedPseudometricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedPseudometricCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {P Z Q M S R D E H C K N sepRead completionRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P Z sepRead ->
      Cont sepRead Q completionRead ->
        Cont S R realRead ->
          PkgSig bundle K pkg ->
            PkgSig bundle N pkg ->
              UnaryHistory P ->
                UnaryHistory Z ->
                  UnaryHistory Q ->
                    UnaryHistory S ->
                      UnaryHistory R ->
                        SemanticNameCert
                            (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row completionRead ∧ Cont P Z sepRead)
                            (fun row : BHist =>
                              hsame row completionRead ∧
                                Cont sepRead Q completionRead ∧ PkgSig bundle K pkg)
                            hsame ∧
                          UnaryHistory sepRead ∧ UnaryHistory completionRead ∧
                            UnaryHistory realRead ∧ Cont P Z sepRead ∧
                              Cont sepRead Q completionRead ∧ Cont S R realRead ∧
                                PkgSig bundle K pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro sepRoute completionRoute realRoute pkgK pkgN unaryP unaryZ unaryQ unaryS unaryR
  have unarySep : UnaryHistory sepRead :=
    unary_cont_closed unaryP unaryZ sepRoute
  have unaryCompletion : UnaryHistory completionRead :=
    unary_cont_closed unarySep unaryQ completionRoute
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryS unaryR realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row completionRead ∧ Cont P Z sepRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont sepRead Q completionRead ∧
              PkgSig bundle K pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, unaryCompletion⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, sepRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, completionRoute, pkgK⟩
  }
  exact
    ⟨cert, unarySep, unaryCompletion, unaryReal, sepRoute, completionRoute, realRoute, pkgK,
      pkgN⟩

theorem SeparatedPseudometricCompletionCarrier_obligation_closure_package
    [AskSetup] [PackageSetup]
    {P Z Q M S R D E H C K N pz zq qm ms sr rd de eh : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedPseudometricCompletionCarrier P Z Q M S R D E H C K N bundle pkg →
      Cont P Z pz →
        Cont pz Q zq →
          Cont zq M qm →
            Cont qm S ms →
              Cont ms R sr →
                Cont sr D rd →
                  Cont rd E de →
                    Cont de H eh →
                      PkgSig bundle eh pkg →
                        SemanticNameCert
                              (fun row : BHist => hsame row eh ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row P ∨ hsame row Z ∨ hsame row Q ∨ hsame row M ∨
                                  hsame row S ∨ hsame row R ∨ hsame row D ∨
                                    hsame row E ∨ hsame row eh)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont P Z pz ∧ Cont pz Q zq ∧
                                  Cont zq M qm ∧ Cont qm S ms ∧ Cont ms R sr ∧
                                    Cont sr D rd ∧ Cont rd E de ∧ Cont de H eh ∧
                                      PkgSig bundle eh pkg)
                              hsame ∧
                          UnaryHistory pz ∧ UnaryHistory zq ∧ UnaryHistory qm ∧
                            UnaryHistory ms ∧ UnaryHistory sr ∧ UnaryHistory rd ∧
                              UnaryHistory de ∧ UnaryHistory eh ∧ PkgSig bundle K pkg ∧
                                PkgSig bundle eh pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier pzRoute zqRoute qmRoute msRoute srRoute rdRoute deRoute ehRoute ehPkg
  rcases carrier with
    ⟨unaryP, unaryZ, unaryQ, unaryM, unaryS, unaryR, unaryD, unaryE, unaryH, unaryC,
      unaryK, unaryN, pkgK, pkgN⟩
  have pzUnary : UnaryHistory pz :=
    unary_cont_closed unaryP unaryZ pzRoute
  have zqUnary : UnaryHistory zq :=
    unary_cont_closed pzUnary unaryQ zqRoute
  have qmUnary : UnaryHistory qm :=
    unary_cont_closed zqUnary unaryM qmRoute
  have msUnary : UnaryHistory ms :=
    unary_cont_closed qmUnary unaryS msRoute
  have srUnary : UnaryHistory sr :=
    unary_cont_closed msUnary unaryR srRoute
  have rdUnary : UnaryHistory rd :=
    unary_cont_closed srUnary unaryD rdRoute
  have deUnary : UnaryHistory de :=
    unary_cont_closed rdUnary unaryE deRoute
  have ehUnary : UnaryHistory eh :=
    unary_cont_closed deUnary unaryH ehRoute
  have obligationSurface :=
    SeparatedPseudometricCompletionCarrier_namecert_obligations (P := P) (Z := Z)
      (Q := Q) (M := M) (S := ms) (R := R) (D := D) (E := E) (H := H) (C := C)
      (K := K) (N := N) (sepRead := pz) (completionRead := zq) (realRead := sr)
      (bundle := bundle) (pkg := pkg) pzRoute zqRoute srRoute pkgK pkgN unaryP unaryZ
      unaryQ msUnary unaryR
  rcases obligationSurface with
    ⟨_completionCert, _pzUnaryByObligation, _zqUnaryByObligation, _srUnaryByObligation,
      _pzRouteByObligation, _zqRouteByObligation, _srRouteByObligation, _pkgKByObligation,
      _pkgNByObligation⟩
  have routePackage :=
    SeparatedPseudometricCompletionCarrier_completion_route (P := P) (Z := Z) (Q := Q)
      (M := M) (S := S) (R := R) (D := D) (E := E) (H := H) (C := de) (K := K)
      (N := N) (routeSep := pz) (routeCompletion := zq) (routeWindow := qm)
      (routeReg := ms) (routeDyadic := sr) (routeReal := rd) (bundle := bundle)
      (pkg := pkg)
      ⟨unaryP, unaryZ, unaryQ, unaryM, unaryS, unaryR, unaryD, unaryE, unaryH,
        deUnary, unaryK, unaryN, pzRoute, zqRoute, qmRoute, msRoute, srRoute,
        rdRoute, deRoute, pkgK, pkgN⟩
  rcases routePackage with
    ⟨_pzUnary, _zqUnary, _qmUnary, _msUnary, _srUnary, _rdUnary, _pzRoute, _zqRoute,
      _qmRoute, _msRoute, _srRoute, _rdRoute, _deRoute, _pkgK, _ehPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row eh ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row Z ∨ hsame row Q ∨ hsame row M ∨ hsame row S ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row eh)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P Z pz ∧ Cont pz Q zq ∧ Cont zq M qm ∧
              Cont qm S ms ∧ Cont ms R sr ∧ Cont sr D rd ∧ Cont rd E de ∧
                Cont de H eh ∧ PkgSig bundle eh pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro eh ⟨hsame_refl eh, ehUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, pzRoute, zqRoute, qmRoute, msRoute, srRoute, rdRoute, deRoute,
          ehRoute, ehPkg⟩
  }
  exact
    ⟨cert, pzUnary, zqUnary, qmUnary, msUnary, srUnary, rdUnary, deUnary, ehUnary, pkgK,
      ehPkg⟩

end BEDC.Derived.SeparatedPseudometricCompletionUp
