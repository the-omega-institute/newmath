import BEDC.Derived.CauchyNetCompletionUp.NameCertObligations

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionRootSealNonescape [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead requestRead mooreRead uniformRead
      separatedRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead Q requestRead ->
          Cont requestRead M mooreRead ->
            Cont mooreRead U uniformRead ->
              Cont uniformRead S separatedRead ->
                Cont separatedRead R readbackRead ->
                  Cont readbackRead A sealRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row D ∨ hsame row W ∨ hsame row Q ∨
                                hsame row M ∨ hsame row U ∨ hsame row S ∨
                                  hsame row R ∨ hsame row A ∨
                                    hsame row boundaryRead ∨ hsame row requestRead ∨
                                      hsame row mooreRead ∨ hsame row uniformRead ∨
                                        hsame row separatedRead ∨ hsame row readbackRead ∨
                                          hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont D W boundaryRead ∧
                                Cont boundaryRead Q requestRead ∧
                                  Cont requestRead M mooreRead ∧
                                    Cont mooreRead U uniformRead ∧
                                      Cont uniformRead S separatedRead ∧
                                        Cont separatedRead R readbackRead ∧
                                          Cont readbackRead A sealRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute requestRoute mooreRoute uniformRoute separatedRoute readbackRoute
    sealRoute provenancePkg localNamePkg
  obtain ⟨unaryD, unaryW, unaryQ, unaryM, unaryU, unaryS, unaryR, unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, _carrierProvenancePkg,
        _carrierLocalNamePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed boundaryUnary unaryQ requestRoute
  have mooreUnary : UnaryHistory mooreRead :=
    unary_cont_closed requestUnary unaryM mooreRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed mooreUnary unaryU uniformRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed uniformUnary unaryS separatedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed separatedUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryA sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row boundaryRead ∨
                hsame row requestRead ∨ hsame row mooreRead ∨ hsame row uniformRead ∨
                  hsame row separatedRead ∨ hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧ Cont boundaryRead Q requestRead ∧
              Cont requestRead M mooreRead ∧ Cont mooreRead U uniformRead ∧
                Cont uniformRead S separatedRead ∧ Cont separatedRead R readbackRead ∧
                  Cont readbackRead A sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, requestRoute, mooreRoute, uniformRoute,
          separatedRoute, readbackRoute, sealRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
