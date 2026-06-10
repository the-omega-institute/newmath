import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservableDiameterDecayUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObservableDiameterDecayCompactUniformRoute [AskSetup] [PackageSetup]
    {compactNet pointwise radius triangle modulus transport replay provenance localName
      compactPoint radiusTriangle triangleModulus uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactNet ->
      UnaryHistory pointwise ->
        UnaryHistory radius ->
          UnaryHistory triangle ->
            UnaryHistory modulus ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont compactNet pointwise compactPoint ->
                    Cont radius triangle radiusTriangle ->
                      Cont radiusTriangle modulus triangleModulus ->
                        Cont compactPoint triangleModulus uniformRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row compactNet ∨ hsame row pointwise ∨
                                      hsame row radius ∨ hsame row triangle ∨
                                        hsame row modulus ∨ hsame row uniformRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont compactNet pointwise compactPoint ∧
                                        Cont radius triangle radiusTriangle ∧
                                          Cont radiusTriangle modulus triangleModulus ∧
                                            Cont compactPoint triangleModulus uniformRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory compactPoint ∧ UnaryHistory radiusTriangle ∧
                                  UnaryHistory triangleModulus ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro compactUnary pointwiseUnary radiusUnary triangleUnary modulusUnary _transportUnary
    _replayUnary compactPointRoute radiusTriangleRoute triangleModulusRoute uniformRoute
    provenancePkg localNamePkg
  have compactPointUnary : UnaryHistory compactPoint :=
    unary_cont_closed compactUnary pointwiseUnary compactPointRoute
  have radiusTriangleUnary : UnaryHistory radiusTriangle :=
    unary_cont_closed radiusUnary triangleUnary radiusTriangleRoute
  have triangleModulusUnary : UnaryHistory triangleModulus :=
    unary_cont_closed radiusTriangleUnary modulusUnary triangleModulusRoute
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactPointUnary triangleModulusUnary uniformRoute
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactNet ∨ hsame row pointwise ∨ hsame row radius ∨
              hsame row triangle ∨ hsame row modulus ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactNet pointwise compactPoint ∧
              Cont radius triangle radiusTriangle ∧ Cont radiusTriangle modulus triangleModulus ∧
                Cont compactPoint triangleModulus uniformRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
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
      exact
        ⟨source.right, compactPointRoute, radiusTriangleRoute, triangleModulusRoute,
          uniformRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, compactPointUnary, radiusTriangleUnary, triangleModulusUnary, uniformReadUnary⟩

end BEDC.Derived.ObservableDiameterDecayUp
