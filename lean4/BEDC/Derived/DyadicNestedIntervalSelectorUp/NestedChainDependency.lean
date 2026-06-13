import BEDC.Derived.DyadicNestedIntervalSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicNestedIntervalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicNestedIntervalSelectorNestedChainDependency [AskSetup] [PackageSetup]
    {I D S R E H C P N chainRead selectorRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory D ->
        UnaryHistory S ->
          UnaryHistory E ->
            Cont I D chainRead ->
              Cont chainRead S selectorRead ->
                Cont selectorRead E sealRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row I ∨ hsame row D ∨ hsame row S ∨ hsame row E ∨
                              Cont I D chainRead ∨ Cont chainRead S selectorRead ∨
                                Cont selectorRead E sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                          hsame ∧ UnaryHistory chainRead ∧ UnaryHistory selectorRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryI unaryD unaryS unaryE chainRoute selectorRoute sealRoute provenancePkg namePkg
  have chainUnary : UnaryHistory chainRead :=
    unary_cont_closed unaryI unaryD chainRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed chainUnary unaryS selectorRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row D ∨ hsame row S ∨ hsame row E ∨
              Cont I D chainRead ∨ Cont chainRead S selectorRead ∨
                Cont selectorRead E sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sealRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, chainUnary, selectorUnary, sealUnary⟩

end BEDC.Derived.DyadicNestedIntervalSelectorUp
