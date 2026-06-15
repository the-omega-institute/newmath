import BEDC.Derived.LocatedCauchyFilterUp.ChoiceFreeBasis

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterBishopCompletionHandoff [AskSetup] [PackageSetup]
    {F B R S Q D T E H C P N basisRead tailRead sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterCarrier F B R S Q D T E H C P N bundle pkg ->
      Cont F B basisRead ->
        Cont basisRead T tailRead ->
          Cont tailRead E sealRead ->
            Cont sealRead C completionRead ->
              PkgSig bundle completionRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row B ∨ hsame row R ∨ hsame row S ∨
                        hsame row Q ∨ hsame row D ∨ hsame row T ∨ hsame row E ∨
                          hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F B basisRead ∧
                        Cont basisRead T tailRead ∧ Cont tailRead E sealRead ∧
                          Cont sealRead C completionRead ∧
                            PkgSig bundle completionRead pkg)
                    hsame ∧
                  UnaryHistory basisRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: LocatedCauchyFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier basisRoute tailRoute sealRoute completionRoute completionPkg
  obtain ⟨unaryF, unaryB, _unaryR, _unaryS, _unaryQ, _unaryD, unaryT, unaryE,
    _unaryH, unaryC, _unaryP, _unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed unaryF unaryB basisRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed basisUnary unaryT tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryE sealRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary unaryC completionRoute
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row B ∨ hsame row R ∨ hsame row S ∨ hsame row Q ∨
              hsame row D ∨ hsame row T ∨ hsame row E ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F B basisRead ∧ Cont basisRead T tailRead ∧
              Cont tailRead E sealRead ∧ Cont sealRead C completionRead ∧
                PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
        ⟨source.right, basisRoute, tailRoute, sealRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, basisUnary, tailUnary, sealUnary, completionUnary⟩

end BEDC.Derived.LocatedCauchyFilterUp
