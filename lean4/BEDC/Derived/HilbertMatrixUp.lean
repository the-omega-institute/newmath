import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HilbertMatrixUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HilbertMatrixCarrier [AskSetup] [PackageSetup]
    (I R P D S H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory D ∧ UnaryHistory S ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory Q ∧ UnaryHistory N ∧
      Cont H C (append H C) ∧ PkgSig bundle Q pkg

theorem HilbertMatrixCarrier_positive_definite_route [AskSetup] [PackageSetup]
    {I R P D S H C Q N rowRead determinantRead positiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HilbertMatrixCarrier I R P D S H C Q N bundle pkg ->
      Cont R P rowRead ->
        Cont D S determinantRead ->
          Cont determinantRead N positiveRead ->
            PkgSig bundle Q pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row positiveRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row R ∨ hsame row P ∨ hsame row D ∨
                      hsame row S ∨ hsame row positiveRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D S determinantRead ∧
                      Cont determinantRead N positiveRead ∧ PkgSig bundle Q pkg)
                  hsame ∧ UnaryHistory rowRead ∧ UnaryHistory determinantRead ∧
                    UnaryHistory positiveRead := by
  -- BEDC touchpoint anchor: HilbertMatrixCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier rowRoute determinantRoute positiveRoute qPkg
  obtain ⟨_unaryI, unaryR, unaryP, unaryD, unaryS, _unaryH, _unaryC, _unaryQ,
    unaryN, _transportRoute, _carrierPkg⟩ := carrier
  have rowUnary : UnaryHistory rowRead :=
    unary_cont_closed unaryR unaryP rowRoute
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed unaryD unaryS determinantRoute
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed determinantUnary unaryN positiveRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row positiveRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row R ∨ hsame row P ∨ hsame row D ∨
              hsame row S ∨ hsame row positiveRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S determinantRead ∧
              Cont determinantRead N positiveRead ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro positiveRead ⟨hsame_refl positiveRead, positiveUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, determinantRoute, positiveRoute, qPkg⟩
  }
  exact ⟨cert, rowUnary, determinantUnary, positiveUnary⟩

theorem HilbertMatrixCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I R P D S H C Q N matrixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HilbertMatrixCarrier I R P D S H C Q N bundle pkg ->
      Cont H C matrixRead ->
        PkgSig bundle Q pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row matrixRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row R ∨ hsame row P ∨ hsame row D ∨
                  hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨
                    hsame row N ∨ hsame row matrixRead)
              (fun row : BHist => UnaryHistory row ∧ Cont H C matrixRead ∧
                PkgSig bundle Q pkg)
              hsame ∧ UnaryHistory matrixRead := by
  -- BEDC touchpoint anchor: HilbertMatrixCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier matrixRoute qPkg
  obtain ⟨_unaryI, _unaryR, _unaryP, _unaryD, _unaryS, unaryH, unaryC, _unaryQ,
    _unaryN, _transportRoute, _carrierPkg⟩ := carrier
  have matrixUnary : UnaryHistory matrixRead :=
    unary_cont_closed unaryH unaryC matrixRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matrixRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row R ∨ hsame row P ∨ hsame row D ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨
                hsame row N ∨ hsame row matrixRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H C matrixRead ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matrixRead ⟨hsame_refl matrixRead, matrixUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, matrixRoute, qPkg⟩
  }
  exact ⟨cert, matrixUnary⟩

end BEDC.Derived.HilbertMatrixUp
