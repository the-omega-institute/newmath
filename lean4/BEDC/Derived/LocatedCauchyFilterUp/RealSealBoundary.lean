import BEDC.Derived.LocatedCauchyFilterUp.ChoiceFreeBasis

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterRealSealBoundary [AskSetup] [PackageSetup]
    {F B R S Q D T E H C P N basisRead dyadicRead regularRead streamRead readbackRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterCarrier F B R S Q D T E H C P N bundle pkg →
      Cont F B basisRead →
        Cont basisRead D dyadicRead →
          Cont dyadicRead R regularRead →
            Cont regularRead S streamRead →
              Cont streamRead Q readbackRead →
                Cont readbackRead E realRead →
                  PkgSig bundle realRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row F ∨ hsame row B ∨ hsame row R ∨ hsame row S ∨
                            hsame row Q ∨ hsame row D ∨ hsame row T ∨ hsame row E ∨
                              hsame row realRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont F B basisRead ∧
                            Cont basisRead D dyadicRead ∧
                              Cont dyadicRead R regularRead ∧
                                Cont regularRead S streamRead ∧
                                  Cont streamRead Q readbackRead ∧
                                    Cont readbackRead E realRead ∧
                                      PkgSig bundle realRead pkg)
                        hsame ∧
                      UnaryHistory basisRead ∧ UnaryHistory dyadicRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory streamRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory realRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier basisCont dyadicCont regularCont streamCont readbackCont realCont realPkg
  obtain ⟨unaryF, unaryB, unaryR, unaryS, unaryQ, unaryD, unaryT, unaryE,
    _unaryH, _unaryC, unaryP, _unaryN, provenancePkg, localNamePkg⟩ := carrier
  have route :=
    LocatedCauchyFilterBasisRefinementRoute
      (F := F) (B := B) (R := R) (S := S) (Q := Q) (D := D) (T := T) (E := E)
      (H := H) (C := C) (P := P) (N := N) (basisRead := basisRead) (dyadicRead := dyadicRead)
      (regularRead := regularRead) (streamRead := streamRead)
      (readbackRead := readbackRead) (realRead := realRead) (bundle := bundle)
      (pkg := pkg) unaryF unaryB unaryR unaryS unaryQ unaryD unaryT unaryE unaryP
      basisCont dyadicCont regularCont streamCont readbackCont realCont provenancePkg realPkg
  obtain ⟨basisUnary, dyadicUnary, regularUnary, streamUnary, readbackUnary,
    realUnary, _basisCont, _dyadicCont, _regularCont, _streamCont, _readbackCont,
      _realCont, _routeProvenancePkg, _routeRealPkg⟩ := route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row B ∨ hsame row R ∨ hsame row S ∨
              hsame row Q ∨ hsame row D ∨ hsame row T ∨ hsame row E ∨
                hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F B basisRead ∧ Cont basisRead D dyadicRead ∧
              Cont dyadicRead R regularRead ∧ Cont regularRead S streamRead ∧
                Cont streamRead Q readbackRead ∧ Cont readbackRead E realRead ∧
                  PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        ⟨source.right, basisCont, dyadicCont, regularCont, streamCont, readbackCont,
          realCont, realPkg⟩
  }
  exact
    ⟨cert, basisUnary, dyadicUnary, regularUnary, streamUnary, readbackUnary, realUnary,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.LocatedCauchyFilterUp
