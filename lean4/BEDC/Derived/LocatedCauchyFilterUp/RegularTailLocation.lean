import BEDC.Derived.LocatedCauchyFilterUp.ChoiceFreeBasis

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterRegularTailLocation [AskSetup] [PackageSetup]
    {F B R S Q D T E H C P N basisRead tailRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterCarrier F B R S Q D T E H C P N bundle pkg ->
      Cont F B basisRead ->
        Cont basisRead D tailRead ->
          Cont tailRead R regularRead ->
            PkgSig bundle regularRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row F ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨
                      hsame row R ∨ hsame row regularRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont F B basisRead ∧ Cont basisRead D tailRead ∧
                      Cont tailRead R regularRead ∧ PkgSig bundle regularRead pkg)
                  hsame ∧
                UnaryHistory basisRead ∧ UnaryHistory tailRead ∧
                  UnaryHistory regularRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier basisRoute tailRoute regularRoute regularPkg
  obtain ⟨unaryF, unaryB, unaryR, _unaryS, _unaryQ, unaryD, _unaryT, _unaryE,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierProvenancePkg,
      _carrierLocalNamePkg⟩ := carrier
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed unaryF unaryB basisRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed basisUnary unaryD tailRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed tailUnary unaryR regularRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨ hsame row R ∨
              hsame row regularRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F B basisRead ∧ Cont basisRead D tailRead ∧
              Cont tailRead R regularRead ∧ PkgSig bundle regularRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regularRead ⟨hsame_refl regularRead, regularUnary⟩
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
      exact ⟨source.right, basisRoute, tailRoute, regularRoute, regularPkg⟩
  }
  exact ⟨cert, basisUnary, tailUnary, regularUnary⟩

end BEDC.Derived.LocatedCauchyFilterUp
