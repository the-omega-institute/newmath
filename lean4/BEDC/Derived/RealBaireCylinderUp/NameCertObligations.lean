import BEDC.Derived.RealBaireCylinderUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealBaireCylinderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealBaireCylinderCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B S Q E H C P N streamRead rationalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B -> UnaryHistory S -> UnaryHistory Q -> UnaryHistory E ->
      UnaryHistory H -> UnaryHistory C -> UnaryHistory P -> UnaryHistory N ->
        Cont B S streamRead -> Cont streamRead Q rationalRead ->
          Cont rationalRead E sealRead -> PkgSig bundle P pkg ->
            PkgSig bundle N pkg -> PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row S ∨ hsame row Q ∨ hsame row E ∨
                      hsame row streamRead ∨ hsame row rationalRead ∨
                        hsame row sealRead)
                  (fun row : BHist =>
                    hsame row sealRead ∧ Cont B S streamRead ∧
                      Cont streamRead Q rationalRead ∧ Cont rationalRead E sealRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle sealRead pkg)
                  hsame ∧ UnaryHistory streamRead ∧ UnaryHistory rationalRead ∧
                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryB unaryS unaryQ unaryE _unaryH _unaryC _unaryP _unaryN streamRoute
    rationalRoute sealRoute provenancePkg namePkg sealPkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryB unaryS streamRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed streamUnary unaryQ rationalRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row Q ∨ hsame row E ∨
              hsame row streamRead ∨ hsame row rationalRead ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont B S streamRead ∧
              Cont streamRead Q rationalRead ∧ Cont rationalRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, streamRoute, rationalRoute, sealRoute, provenancePkg,
          namePkg, sealPkg⟩
  }
  exact ⟨cert, streamUnary, rationalUnary, sealUnary⟩

end BEDC.Derived.RealBaireCylinderUp
