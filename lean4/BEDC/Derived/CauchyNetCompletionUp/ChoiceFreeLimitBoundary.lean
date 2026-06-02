import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionChoiceFreeLimitBoundary [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead handoffRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead M handoffRead ->
          Cont handoffRead A limitRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
                        hsame row U ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row boundaryRead ∨ hsame row handoffRead ∨
                              hsame row limitRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont D W boundaryRead ∧
                        Cont boundaryRead M handoffRead ∧ Cont handoffRead A limitRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory handoffRead ∧
                    UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute handoffRoute limitRoute provenancePkg localNamePkg
  obtain ⟨unaryD, unaryW, _unaryQ, unaryM, _unaryU, _unaryS, _unaryR, unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, _carrierProvenancePkg,
        _carrierLocalNamePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed boundaryUnary unaryM handoffRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed handoffUnary unaryA limitRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row boundaryRead ∨
                  hsame row handoffRead ∨ hsame row limitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧
              Cont boundaryRead M handoffRead ∧ Cont handoffRead A limitRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro limitRead ⟨hsame_refl limitRead, limitUnary⟩
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
        ⟨source.right, boundaryRoute, handoffRoute, limitRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, handoffUnary, limitUnary⟩

theorem CauchyNetCompletionCarrier_choice_free_limit_boundary [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead comparisonRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead S comparisonRead ->
          Cont comparisonRead R readbackRead ->
            Cont readbackRead A sealRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨
                          hsame row U ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                            hsame row boundaryRead ∨ hsame row comparisonRead ∨
                              hsame row readbackRead ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D W boundaryRead ∧
                          Cont boundaryRead S comparisonRead ∧
                            Cont comparisonRead R readbackRead ∧
                              Cont readbackRead A sealRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory comparisonRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute comparisonRoute readbackRoute sealRoute provenancePkg localNamePkg
  obtain ⟨unaryD, unaryW, _unaryQ, _unaryM, _unaryU, unaryS, unaryR, unaryA,
    _unaryH, _unaryC, _carrierProvenanceUnary, _carrierNameUnary, _carrierBoundaryRoute,
      _carrierMooreRoute, _carrierComparisonRoute, _carrierSealRoute, _carrierPkgP,
        _carrierPkgN⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed boundaryUnary unaryS comparisonRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed comparisonUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryA sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row M ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row A ∨ hsame row boundaryRead ∨
                hsame row comparisonRead ∨ hsame row readbackRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧
              Cont boundaryRead S comparisonRead ∧ Cont comparisonRead R readbackRead ∧
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
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, boundaryRoute, comparisonRoute, readbackRoute, sealRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, comparisonUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
