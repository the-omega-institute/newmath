import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureCarrier_located_cauchy_filter_handoff [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N endpointRead radiusRead filterRead windowRead readbackRead
      locatedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont R M endpointRead →
        Cont endpointRead D radiusRead →
          Cont radiusRead U filterRead →
            Cont filterRead S windowRead →
              Cont windowRead Q readbackRead →
                Cont readbackRead F locatedTail →
                  PkgSig bundle locatedTail pkg →
                    UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory U ∧
                      UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                        UnaryHistory endpointRead ∧ UnaryHistory radiusRead ∧
                          UnaryHistory filterRead ∧ UnaryHistory windowRead ∧
                            UnaryHistory readbackRead ∧ UnaryHistory locatedTail ∧
                              Cont R M endpointRead ∧ Cont endpointRead D radiusRead ∧
                                Cont radiusRead U filterRead ∧ Cont filterRead S windowRead ∧
                                  Cont windowRead Q readbackRead ∧
                                    Cont readbackRead F locatedTail ∧
                                      PkgSig bundle P pkg ∧
                                        PkgSig bundle locatedTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointCont radiusCont filterCont windowCont readbackCont locatedCont
    locatedPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rUnary mUnary endpointCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed endpointUnary dUnary radiusCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed radiusUnary uUnary filterCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have locatedUnary : UnaryHistory locatedTail :=
    unary_cont_closed readbackUnary fUnary locatedCont
  exact
    ⟨rUnary, mUnary, dUnary, uUnary, fUnary, sUnary, qUnary, endpointUnary, radiusUnary,
      filterUnary, windowUnary, readbackUnary, locatedUnary, endpointCont, radiusCont,
      filterCont, windowCont, readbackCont, locatedCont, pPkg, locatedPkg⟩

theorem RealUniformStructureCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N radiusRead entourageRead filterRead windowRead readbackRead
      locatedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont R M radiusRead →
        Cont radiusRead D entourageRead →
          Cont entourageRead U filterRead →
            Cont filterRead S windowRead →
              Cont windowRead Q readbackRead →
                Cont readbackRead F locatedTail →
                  PkgSig bundle locatedTail pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row locatedTail ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row M ∨ hsame row U ∨ hsame row F ∨
                            hsame row D ∨ hsame row S ∨ hsame row Q ∨ hsame row locatedTail)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont R M radiusRead ∧
                            Cont radiusRead D entourageRead ∧
                              Cont entourageRead U filterRead ∧
                                Cont filterRead S windowRead ∧
                                  Cont windowRead Q readbackRead ∧
                                    Cont readbackRead F locatedTail ∧
                                      PkgSig bundle locatedTail pkg)
                        hsame ∧
                      UnaryHistory radiusRead ∧ UnaryHistory entourageRead ∧
                        UnaryHistory filterRead ∧ UnaryHistory windowRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory locatedTail := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier radiusCont entourageCont filterCont windowCont readbackCont locatedCont
    locatedPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary mUnary radiusCont
  have entourageUnary : UnaryHistory entourageRead :=
    unary_cont_closed radiusUnary dUnary entourageCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed entourageUnary uUnary filterCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have locatedUnary : UnaryHistory locatedTail :=
    unary_cont_closed readbackUnary fUnary locatedCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedTail ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row M ∨ hsame row U ∨ hsame row F ∨ hsame row D ∨
              hsame row S ∨ hsame row Q ∨ hsame row locatedTail)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R M radiusRead ∧ Cont radiusRead D entourageRead ∧
              Cont entourageRead U filterRead ∧ Cont filterRead S windowRead ∧
                Cont windowRead Q readbackRead ∧ Cont readbackRead F locatedTail ∧
                  PkgSig bundle locatedTail pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedTail ⟨hsame_refl locatedTail, locatedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, radiusCont, entourageCont, filterCont, windowCont, readbackCont,
          locatedCont, locatedPkg⟩
  }
  exact
    ⟨cert, radiusUnary, entourageUnary, filterUnary, windowUnary, readbackUnary,
      locatedUnary⟩

end BEDC.Derived.RealUniformStructureUp
