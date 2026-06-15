import BEDC.Derived.LocatedCauchyFilterUp.ChoiceFreeBasis

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterRealExtraction [AskSetup] [PackageSetup]
    {F B R S Q D T E H C P N baseRead tailRead seqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyFilterCarrier F B R S Q D T E H C P N bundle pkg ->
      Cont B D baseRead ->
        Cont baseRead T tailRead ->
          Cont S Q seqRead ->
            Cont tailRead seqRead realRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row F ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨
                          hsame row S ∨ hsame row Q ∨ hsame row E ∨
                            Cont B D baseRead ∨ Cont baseRead T tailRead ∨
                              Cont S Q seqRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont B D baseRead ∧
                          Cont baseRead T tailRead ∧ Cont S Q seqRead ∧
                            Cont tailRead seqRead realRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory baseRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory seqRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: LocatedCauchyFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier baseRoute tailRoute seqRoute realRoute provenancePkg localNamePkg
  obtain ⟨_unaryF, unaryB, _unaryR, unaryS, unaryQ, unaryD, unaryT, _unaryE,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierProvenancePkg,
      _carrierLocalNamePkg⟩ := carrier
  have baseUnary : UnaryHistory baseRead :=
    unary_cont_closed unaryB unaryD baseRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed baseUnary unaryT tailRoute
  have seqUnary : UnaryHistory seqRead :=
    unary_cont_closed unaryS unaryQ seqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary seqUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row B ∨ hsame row D ∨ hsame row T ∨
              hsame row S ∨ hsame row Q ∨ hsame row E ∨ Cont B D baseRead ∨
                Cont baseRead T tailRead ∨ Cont S Q seqRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B D baseRead ∧ Cont baseRead T tailRead ∧
              Cont S Q seqRead ∧ Cont tailRead seqRead realRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr seqRoute))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baseRoute, tailRoute, seqRoute, realRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, baseUnary, tailUnary, seqUnary, realUnary⟩

end BEDC.Derived.LocatedCauchyFilterUp
